//! This module provides parsers for the DIMACS CNF and WCNF file formats. Given that DIMACS files
//! can be very large, the implementation is designed to read the file in chunks. The parser also
//! will not allocate for every encountered clause, but rather re-use its buffers.
//!
//! To invoke the parser, there are two options:
//!  - For a CNF file, the [`parse_cnf`] function can be called,
//!  - For a WCNF file, the [`parse_wcnf`] function can be called.
//!
//! Both these functions operate on a type that implements the [`DimacsSink`] trait, which is
//! serves as an interface between the consumer of the parsed contents of the file.
//!
//! It should be noted that the parsers should not be used as DIMACS validators. Even though they
//! should only accept valid DIMACS files, the errors are not extremely detailed. Perhaps this
//! could change over time, however.
use std::io::BufRead;
use std::io::BufReader;
use std::io::Read;
use std::num::NonZeroI32;
use std::num::NonZeroU32;
use std::str::FromStr;

use pumpkin_solver::options::SolverOptions;
use pumpkin_solver::variables::Literal;
use pumpkin_solver::Function;
use pumpkin_solver::Solver;
use thiserror::Error;

/// A dimacs sink stores a set of clauses and allows for new variables to be created.
pub(crate) trait DimacsSink {
    /// The arguments to the dimacs sink.
    type ConstructorArgs;

    /// Create an empty formula.
    fn empty(args: Self::ConstructorArgs, num_variables: usize) -> Self;

    /// Add a new hard clause to the formula. Consistency does not have to be checked at every
    /// insertion. As such, after the formula is constructed from the file format, consistency
    /// needs to be evaluated if appropriate.
    fn add_hard_clause(&mut self, clause: &[NonZeroI32]);

    /// Add a new soft clause to the formula. This supports non-unit soft clauses, and returns the
    /// literal which can be used in the objective function.
    fn add_soft_clause(&mut self, weight: NonZeroU32, clause: &[NonZeroI32]);
}

#[derive(Debug, Error)]
pub(crate) enum DimacsParseError {
    #[error("failed to read file")]
    Io(#[from] std::io::Error),

    #[error("missing dimacs header")]
    MissingHeader,

    #[error("'{0}' is an invalid header")]
    InvalidHeader(String),

    #[error("multiple dimacs headers found")]
    DuplicateHeader,

    #[error("unexpected character '{0}'")]
    UnexpectedCharacter(char),

    #[error("'{0}' is an invalid DIMACS literal")]
    InvalidLiteral(String),

    #[error("the last clause in the source is not terminated with a '0'")]
    UnterminatedClause,

    #[error("expected to parse {expected} clauses, but parsed {parsed}")]
    IncorrectClauseCount { expected: usize, parsed: usize },
}

pub(crate) fn parse_cnf<Sink: DimacsSink>(
    source: impl Read,
    sink_constructor_args: Sink::ConstructorArgs,
) -> Result<Sink, DimacsParseError> {
    let mut reader = BufReader::new(source);
    let mut parser =
        DimacsParser::<Sink, _, CNFHeader>::new(sink_constructor_args, |sink, clause, _| {
            sink.add_hard_clause(clause);
        });

    loop {
        let num_bytes = {
            let data = reader.fill_buf()?;

            if data.is_empty() {
                return parser.complete();
            }

            parser.parse_chunk(data)?;
            data.len()
        };

        reader.consume(num_bytes);
    }
}

pub(crate) fn parse_wcnf<Sink: DimacsSink>(
    source: impl Read,
    sink_constructor_args: Sink::ConstructorArgs,
) -> Result<Sink, DimacsParseError> {
    let mut reader = BufReader::new(source);
    let mut parser =
        DimacsParser::<Sink, _, WCNFHeader>::new(sink_constructor_args, |sink, clause, header| {
            let weight: NonZeroU32 = clause[0].try_into().unwrap();

            if u64::from(weight.get()) == header.top_weight {
                sink.add_hard_clause(&clause[1..]);
            } else {
                sink.add_soft_clause(weight, &clause[1..]);
            }
        });

    loop {
        let num_bytes = {
            let data = reader.fill_buf()?;

            if data.is_empty() {
                let formula = parser.complete()?;
                return Ok(formula);
            }

            parser.parse_chunk(data)?;
            data.len()
        };

        reader.consume(num_bytes);
    }
}

/// The core DIMACS parser. New clauses are not directly added to the sink, but rather a callback
/// `OnClause` is used. This allows the WCNF and CNF parser to reuse the same logic.
struct DimacsParser<Sink: DimacsSink, OnClause, Header> {
    sink_constructor_args: Option<Sink::ConstructorArgs>,
    sink: Option<Sink>,
    header: Option<Header>,
    buffer: String,
    clause: Vec<NonZeroI32>,
    state: ParseState,
    on_clause: OnClause,
    parsed_clauses: usize,
}

enum ParseState {
    StartLine,
    Header,
    Comment,
    Literal,
    NegativeLiteral,
    Clause,
}

impl<Sink, OnClause, Header> DimacsParser<Sink, OnClause, Header>
where
    OnClause: FnMut(&mut Sink, &[NonZeroI32], &Header),
    Sink: DimacsSink,
    Header: DimacsHeader,
{
    /// Construct a new DIMACS parser based on the sink constructor arguments and the callback to
    /// be executed when a clause is completely parsed.
    fn new(sink_constructor_args: Sink::ConstructorArgs, on_clause: OnClause) -> Self {
        DimacsParser {
            sink_constructor_args: Some(sink_constructor_args),
            sink: None,
            header: None,
            buffer: String::new(),
            clause: vec![],
            state: ParseState::StartLine,
            on_clause,
            parsed_clauses: 0,
        }
    }

    /// Parse the next chunk of bytes. This may start in the middle of parsing a clause or file
    /// header, and may end in such a state as well.
    fn parse_chunk(&mut self, chunk: &[u8]) -> Result<(), DimacsParseError> {
        for byte in chunk {
            match self.state {
                ParseState::StartLine => match byte {
                    b if b.is_ascii_whitespace() => {} // Continue consuming whitespace.

                    b'p' => {
                        self.state = ParseState::Header;
                        self.buffer.clear();
                        self.buffer.push('p');
                    }

                    b'c' => {
                        self.state = ParseState::Comment;
                    }

                    b @ b'1'..=b'9' => {
                        self.start_literal(b, true);
                    }

                    // covers the exotic case of having an empty clause in the dimacs file
                    b'0' => self.finish_clause()?,

                    b'-' => self.start_literal(&b'-', false),

                    b => return Err(DimacsParseError::UnexpectedCharacter(*b as char)),
                },

                ParseState::Header => match byte {
                    b'\n' => {
                        self.init_formula()?;
                        self.state = ParseState::StartLine;
                    }

                    b => self.buffer.push(*b as char),
                },

                ParseState::Comment => {
                    // Ignore all other bytes until we find a new-line, at which point the comment
                    // ends.
                    if *byte == b'\n' {
                        self.state = ParseState::StartLine;
                    }
                }

                ParseState::Literal => match byte {
                    b if b.is_ascii_whitespace() => {
                        self.finish_literal()?;
                    }

                    b @ b'0'..=b'9' => self.buffer.push(*b as char),

                    b => return Err(DimacsParseError::UnexpectedCharacter(*b as char)),
                },

                ParseState::NegativeLiteral => match byte {
                    b @ b'1'..=b'9' => {
                        self.buffer.push(*b as char);
                        self.state = ParseState::Literal;
                    }

                    b => return Err(DimacsParseError::UnexpectedCharacter(*b as char)),
                },

                ParseState::Clause => match byte {
                    b'0' => self.finish_clause()?,

                    // When a new-line is encountered, it does not mean the clause is terminated.
                    // We switch to the StartLine state to handle comments and leading whitespace.
                    // However, the clause buffer is not cleared so the clause that is being parsed
                    // is kept in-memory and will continue to be parsed as soon as a literal is
                    // encountered.
                    b'\n' => self.state = ParseState::StartLine,
                    b if b.is_ascii_whitespace() => {} // Ignore whitespace.

                    b @ b'1'..=b'9' => self.start_literal(b, true),
                    b'-' => self.start_literal(&b'-', false),

                    b => return Err(DimacsParseError::UnexpectedCharacter(*b as char)),
                },
            }
        }

        Ok(())
    }

    fn start_literal(&mut self, b: &u8, is_positive: bool) {
        self.state = if is_positive {
            ParseState::Literal
        } else {
            ParseState::NegativeLiteral
        };

        self.buffer.clear();
        self.buffer.push(*b as char);
    }

    fn complete(self) -> Result<Sink, DimacsParseError> {
        let sink = self.sink.ok_or(DimacsParseError::MissingHeader)?;
        let header = self
            .header
            .expect("if sink is present then header is present");

        if !self.clause.is_empty() {
            Err(DimacsParseError::UnterminatedClause)
        } else if header.num_clauses() != self.parsed_clauses {
            Err(DimacsParseError::IncorrectClauseCount {
                expected: header.num_clauses(),
                parsed: self.parsed_clauses,
            })
        } else {
            Ok(sink)
        }
    }

    fn init_formula(&mut self) -> Result<(), DimacsParseError> {
        let header = self.buffer.trim().parse::<Header>()?;

        self.sink = Some(Sink::empty(
            self.sink_constructor_args
                .take()
                .ok_or(DimacsParseError::DuplicateHeader)?,
            header.num_variables(),
        ));

        self.header = Some(header);

        Ok(())
    }

    fn finish_literal(&mut self) -> Result<(), DimacsParseError> {
        let dimacs_code = self
            .buffer
            .parse::<i32>()
            .map_err(|_| DimacsParseError::InvalidLiteral(self.buffer.clone()))?;

        let literal = NonZeroI32::new(dimacs_code).expect("cannot be 0 here");
        self.clause.push(literal);
        self.state = ParseState::Clause;

        Ok(())
    }

    fn finish_clause(&mut self) -> Result<(), DimacsParseError> {
        let sink = self.sink.as_mut().ok_or(DimacsParseError::MissingHeader)?;
        let header = self
            .header
            .as_ref()
            .expect("header is set when the sink is created");

        self.parsed_clauses += 1;
        (self.on_clause)(sink, &self.clause, header);
        self.clause.clear();

        Ok(())
    }
}

trait DimacsHeader: FromStr<Err = DimacsParseError> {
    fn num_variables(&self) -> usize;
    fn num_clauses(&self) -> usize;
}

struct WCNFHeader {
    num_variables: usize,
    num_clauses: usize,
    top_weight: u64,
}

struct CNFHeader {
    num_variables: usize,
    num_clauses: usize,
}

impl FromStr for WCNFHeader {
    type Err = DimacsParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if !s.starts_with("p wcnf ") {
            return Err(DimacsParseError::InvalidHeader(s.to_owned()));
        }

        let mut components = s.trim().split(' ').skip(2);

        let num_variables = next_header_component::<usize>(&mut components, s)?;
        let num_clauses = next_header_component::<usize>(&mut components, s)?;
        let top_weight = next_header_component::<u64>(&mut components, s)?;

        if components.next().is_some() {
            return Err(DimacsParseError::InvalidHeader(s.to_owned()));
        }

        Ok(Self {
            num_variables,
            num_clauses,
            top_weight,
        })
    }
}

impl FromStr for CNFHeader {
    type Err = DimacsParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if !s.starts_with("p cnf ") {
            return Err(DimacsParseError::InvalidHeader(s.to_owned()));
        }

        let mut components = s.trim().split(' ').skip(2);

        let num_variables = next_header_component::<usize>(&mut components, s)?;
        let num_clauses = next_header_component::<usize>(&mut components, s)?;

        if components.next().is_some() {
            return Err(DimacsParseError::InvalidHeader(s.to_owned()));
        }

        Ok(Self {
            num_variables,
            num_clauses,
        })
    }
}

impl DimacsHeader for CNFHeader {
    fn num_variables(&self) -> usize {
        self.num_variables
    }

    fn num_clauses(&self) -> usize {
        self.num_clauses
    }
}

impl DimacsHeader for WCNFHeader {
    fn num_variables(&self) -> usize {
        self.num_variables
    }

    fn num_clauses(&self) -> usize {
        self.num_clauses
    }
}

fn next_header_component<'a, Num: FromStr>(
    components: &mut impl Iterator<Item = &'a str>,
    header: &str,
) -> Result<Num, DimacsParseError> {
    components
        .next()
        .ok_or_else(|| DimacsParseError::InvalidHeader(header.to_owned()))?
        .parse::<Num>()
        .map_err(|_| DimacsParseError::InvalidHeader(header.to_owned()))
}

/// A dimacs sink that creates a fresh [`Solver`] when reading DIMACS files.
pub(crate) struct SolverDimacsSink {
    pub(crate) solver: Solver,
    pub(crate) objective: Function,
    pub(crate) variables: Vec<Literal>,
}

/// The arguments to construct a [`Solver`]. Forwarded to
/// [`Solver::with_options()`].
pub(crate) struct SolverArgs {
    // todo: add back the learning options
    solver_options: SolverOptions,
}

impl SolverArgs {
    pub(crate) fn new(solver_options: SolverOptions) -> SolverArgs {
        SolverArgs { solver_options }
    }
}

impl SolverDimacsSink {
    fn mapped_clause(&self, clause: &[NonZeroI32]) -> Vec<Literal> {
        clause
            .iter()
            .map(|dimacs_code| {
                if dimacs_code.is_positive() {
                    self.variables[dimacs_code.unsigned_abs().get() as usize - 1]
                } else {
                    !self.variables[dimacs_code.unsigned_abs().get() as usize - 1]
                }
            })
            .collect()
    }
}

impl DimacsSink for SolverDimacsSink {
    type ConstructorArgs = SolverArgs;

    fn empty(args: Self::ConstructorArgs, num_variables: usize) -> Self {
        let SolverArgs { solver_options } = args;

        let mut solver = Solver::with_options(solver_options);
        let variables = (0..num_variables)
            .map(|code| solver.new_named_literal(format!("{}", code + 1)))
            .collect::<Vec<_>>();

        SolverDimacsSink {
            solver,
            objective: Function::default(),
            variables,
        }
    }

    fn add_hard_clause(&mut self, clause: &[NonZeroI32]) {
        let mapped = self
            .mapped_clause(clause)
            .into_iter()
            .map(|literal| literal.get_true_predicate());
        let _ = self.solver.add_clause(mapped);
    }

    fn add_soft_clause(&mut self, weight: NonZeroU32, clause: &[NonZeroI32]) {
        let mut clause = self.mapped_clause(clause);

        let is_clause_satisfied = clause
            .iter()
            .any(|literal| self.solver.get_literal_value(*literal).unwrap_or(false));

        if clause.is_empty() {
            // The soft clause is violated at the root level.
            self.objective.add_constant_term(weight.get().into());
        } else if is_clause_satisfied {
            // The soft clause is satisfied at the root level and may be ignored.
        } else if clause.len() == 1 {
            self.objective
                .add_weighted_literal(clause[0], weight.get().into());
        } else {
            // General case, a soft clause with more than one literal.
            let soft_literal = self.solver.new_literal();
            clause.push(soft_literal);
            let _ = self.solver.add_clause(
                clause
                    .into_iter()
                    .map(|literal| literal.get_true_predicate()),
            );

            self.objective
                .add_weighted_literal(!soft_literal, weight.get().into());
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_instance_is_read() {
        let source = "p cnf 2 2\n1 -2 0\n-1 2 0";
        let formula = parse_cnf_source(source);

        assert_eq!(vec![vec![1, -2], vec![-1, 2]], formula);
    }

    #[test]
    fn instance_with_two_character_codes_is_accepted() {
        let source = "p cnf 11 2\n1 -2 10 0\n-1 2 -11 0";
        let formula = parse_cnf_source(source);

        assert_eq!(vec![vec![1, -2, 10], vec![-1, 2, -11]], formula);
    }

    #[test]
    fn trailing_whitespace_is_ignored() {
        let source = "p cnf 2 2\n1 -2 0\n-1 2 0\n";
        let formula = parse_cnf_source(source);

        assert_eq!(vec![vec![1, -2], vec![-1, 2]], formula);
    }

    #[test]
    fn comments_are_ignored() {
        let source = "c this is\nc a comment\np cnf 2 2\n1 -2 0\nc within the file\n-1 2 0\n";
        let formula = parse_cnf_source(source);

        assert_eq!(vec![vec![1, -2], vec![-1, 2]], formula);
    }

    #[test]
    fn whitespace_is_ignored() {
        let source = r#"
            p cnf 2 2
             1 -2 0
            -1  2 0
        "#;

        let formula = parse_cnf_source(source);

        assert_eq!(vec![vec![1, -2], vec![-1, 2]], formula);
    }

    #[test]
    fn empty_lines_are_ignored() {
        let source = r#"

            p cnf 2 2


             1 -2 0

            -1  2 0
        "#;

        let formula = parse_cnf_source(source);

        assert_eq!(vec![vec![1, -2], vec![-1, 2]], formula);
    }

    #[test]
    fn clauses_on_same_line_are_separated() {
        let source = "p cnf 2 2\n1 -2 0 -1 2 0";
        let formula = parse_cnf_source(source);

        assert_eq!(vec![vec![1, -2], vec![-1, 2]], formula);
    }

    #[test]
    fn new_lines_do_not_terminate_clause() {
        let source = "p cnf 2 2\n1\n-2 0 -1 2\n 0";
        let formula = parse_cnf_source(source);

        assert_eq!(vec![vec![1, -2], vec![-1, 2]], formula);
    }

    #[test]
    fn weighted_maxsat_is_parsed_correctly() {
        let source = r#"
            p wcnf 2 4 3
            3  1 -2 0
            3 -1  2 0
            2 1 0
            1 2 0
        "#;

        let (objective, formula) = parse_wcnf_source(source);

        assert_eq!(vec![vec![1, -2], vec![-1, 2]], formula);
        assert_eq!(vec![(2, 1), (1, 2)], objective);
    }

    #[test]
    fn negative_zero_is_an_unexpected_sequence() {
        let source = "p cnf 2 1\n1 -2 -0";
        let err = get_cnf_parse_error(source);

        assert!(matches!(err, DimacsParseError::UnexpectedCharacter('0')));
    }

    #[test]
    fn incomplete_clause_causes_error() {
        let source = "p cnf 2 1\n1 -2";
        let err = get_cnf_parse_error(source);

        assert!(matches!(err, DimacsParseError::UnterminatedClause));
    }

    #[test]
    fn incorrect_reported_clause_count() {
        let source = "p cnf 2 2\n1 -2 0";
        let err = get_cnf_parse_error(source);

        assert!(matches!(
            err,
            DimacsParseError::IncorrectClauseCount {
                expected: 2,
                parsed: 1
            }
        ));
    }

    fn parse_cnf_source(source: &str) -> Vec<Vec<i32>> {
        parse_cnf::<Vec<Vec<i32>>>(source.as_bytes(), ()).expect("valid dimacs")
    }

    fn get_cnf_parse_error(source: &str) -> DimacsParseError {
        parse_cnf::<Vec<Vec<i32>>>(source.as_bytes(), ()).expect_err("invalid dimacs")
    }

    fn parse_wcnf_source(source: &str) -> (Vec<(u32, i32)>, Vec<Vec<i32>>) {
        parse_wcnf::<(Vec<(u32, i32)>, Vec<Vec<i32>>)>(source.as_bytes(), ()).expect("valid dimacs")
    }

    impl DimacsSink for Vec<Vec<i32>> {
        type ConstructorArgs = ();

        fn empty(_: Self::ConstructorArgs, _: usize) -> Self {
            vec![]
        }

        fn add_hard_clause(&mut self, clause: &[NonZeroI32]) {
            self.push(clause.iter().map(|lit| lit.get()).collect());
        }

        fn add_soft_clause(&mut self, _: NonZeroU32, _: &[NonZeroI32]) {
            panic!("Use (Vec<i32>, Vec<Vec<i32>>) to parse wcnf in tests");
        }
    }

    impl DimacsSink for (Vec<(u32, i32)>, Vec<Vec<i32>>) {
        type ConstructorArgs = ();

        fn empty(_: Self::ConstructorArgs, _: usize) -> Self {
            (vec![], vec![])
        }

        fn add_hard_clause(&mut self, clause: &[NonZeroI32]) {
            self.1.push(clause.iter().map(|lit| lit.get()).collect());
        }

        fn add_soft_clause(&mut self, weight: NonZeroU32, clause: &[NonZeroI32]) {
            assert_eq!(1, clause.len(), "in test instances use unit soft clauses");

            self.0.push((weight.get(), clause[0].get()));
        }
    }
}
