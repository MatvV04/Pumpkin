use std::rc::Rc;

use enumset::enum_set;

use crate::basic_types::Inconsistency;
use crate::predicates::Predicate;
use crate::propagators::disjunctive::Timeline;
use crate::{conjunction, predicate, predicates};

use crate::{basic_types::PropagationStatusCP, engine::{opaque_domain_event::OpaqueDomainEvent, propagation::{contexts::PropagationContextWithTrailedValues, EnqueueDecision, LocalId, PropagationContext, PropagationContextMut, Propagator, PropagatorInitialisationContext}, DomainEvents, IntDomainEvent}, predicates::PropositionalConjunction, propagators::disjunctive::{ArgTask, Task}, variables::IntegerVariable};



#[derive(Clone, Debug)]
pub (crate) struct DetectablePrecedencesPropagator<Var> {
    tasks: Rc<[Task<Var>]>,
}

impl<Var> DetectablePrecedencesPropagator<Var>
where 
    Var: IntegerVariable + 'static,
{
    pub (crate) fn new(tasks: Rc<[ArgTask<Var>]>) -> Self {
        DetectablePrecedencesPropagator {
           tasks: tasks.iter().enumerate().map(|(i, task)| {
                Task {
                    starting_time: task.starting_time.clone(),
                    duration: task.duration,
                    deadline: task.deadline,
                    local_id: LocalId::from(i as u32),
                }
            }).collect(), 
        }
    }
}

impl <Var> Propagator for DetectablePrecedencesPropagator<Var>
where 
    Var: IntegerVariable + 'static,
{
    fn priority(&self) -> u32 {
        3
    }    
    fn name(&self) -> &str {
        "DisDetectablePrecedences" 
    }

    fn notify(
        &mut self, 
        context: PropagationContextWithTrailedValues,
        local_id: LocalId,
        _event: OpaqueDomainEvent
    ) -> EnqueueDecision {
        EnqueueDecision::Enqueue
    }

    fn notify_backtrack(
        &mut self, 
        _context: PropagationContext,
        local_id: LocalId,
        event: OpaqueDomainEvent
    ) {

    }

    fn initialise_at_root(
        &mut self, 
        context: &mut PropagatorInitialisationContext,
    ) -> Result<(), PropositionalConjunction> {
        self.tasks.iter().for_each(|task| {
            let _ = context.register(task.starting_time.clone(), DomainEvents::ASSIGN, task.local_id);
            let _ = context.register_for_backtrack_events(
                task.starting_time.clone(),
                DomainEvents::create_with_int_events(enum_set!(
                    IntDomainEvent::Assign | IntDomainEvent::Removal
                )),
                task.local_id,
            );

        });
        Ok(())
    }
    
    fn debug_propagate_from_scratch(&self, context: PropagationContextMut) -> PropagationStatusCP {
        let assignments = context.assignments;
        for task in self.tasks.iter() {
            let ect = Task::get_ect(task, &assignments);
            let lst = Task::get_lst(task,&assignments); 
            if ect > task.deadline {
                let reason: PropositionalConjunction = predicate![task.starting_time >= lst - 1].into();
                return Err(Inconsistency::Conflict(reason));
            }
        }
        let mut tasks_lst: Vec<_> = self.tasks.iter().cloned().collect();
        tasks_lst.sort_by(|a, b| {
            let a_lst = Task::get_lst(a, &assignments);
            let b_lst = Task::get_lst(b, &assignments);
            a_lst.cmp(&b_lst)
        });

        let mut tasks_ect: Vec<_> = self.tasks.iter().cloned().collect();
        tasks_ect.sort_by(|a, b| {
            let a_ect = Task::get_ect(a, assignments);
            let b_ect = Task::get_ect(b, assignments);
            a_ect.cmp(&b_ect)
        });
        let mut k = 0; 
        let mut current_task = tasks_lst[k].clone();
        for i in tasks_ect.iter() {
            
        }
        Ok(())
    }

    fn propagate(&mut self, context: PropagationContextMut) -> PropagationStatusCP {
        //self.debug_propagate_from_scratch(context)
        let reason = self.tasks.iter().flat_map(|task| {
            vec!(
                predicate![task.starting_time >= Task::get_est(task, context.assignments)],
                predicate![task.starting_time <= Task::get_lst(task, context.assignments)]
            )
        }).collect::<PropositionalConjunction>();
        let mut timeline = Timeline::new(self.tasks.clone(), context.assignments);
        let assignments = context.assignments;
        let mut i_lst = self.tasks.iter().cloned().collect::<Vec<Task<Var>>>();
        i_lst.sort_by(|a, b| {
            let a_lst = Task::get_lst(a, &assignments);
            let b_lst = Task::get_lst(b, &assignments);
            a_lst.cmp(&b_lst)
        });
        let mut i_ect = self.tasks.iter().cloned().collect::<Vec<Task<Var>>>();
        i_ect.sort_by(|a, b| {
            let a_ect = Task::get_ect(a, &assignments);
            let b_ect = Task::get_ect(b, &assignments);
            a_ect.cmp(&b_ect)
        });
        let mut j = 0;
        let mut k = i_lst[0].clone();
        let mut ect_k = Task::get_ect(&k, &assignments);
        let mut lst_k = Task::get_lst(&k, &assignments);
        let mut blocking_task: Option<Task<Var>> = None;
        for i in i_ect.iter() {
            let ect_i  = Task::get_ect(i, &assignments);
            while j < i_lst.len() && lst_k < ect_i {
                if lst_k >= ect_k {
                    timeline.schedule_task(&Rc::new(k.clone()));
                } else {
                    if matches!(blocking_task, Some(_)) {
                        return Err(Inconsistency::Conflict(reason));
                    }
                    
                }
            }
        }
        Ok(())
    }
    
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use crate::{basic_types::Inconsistency, engine::{propagation::{PropagationContextMut, Propagator}, test_solver::TestSolver}, propagators::disjunctive::{ArgTask, DetectablePrecedencesPropagator}};

    
    #[test]
    fn test_debug_propagate() {
        let mut solver = TestSolver::default();
        let x = solver.new_variable(5, 8);

        let propagator = solver.new_propagator(DetectablePrecedencesPropagator::new(
            Rc::new([ArgTask {
                starting_time: x.clone(),
                duration: 2,
                deadline: 10,
            }])
        )).expect("fail");
        let result = solver.propagate(propagator);
        assert!(result.is_ok());

    }
    #[test]
    fn test_debug_propagate_fail() {
        let mut solver = TestSolver::default();
        let x = solver.new_variable(3, 8);

        let propagator = solver.new_propagator(DetectablePrecedencesPropagator::new(
            Rc::new([ArgTask {
                starting_time: x.clone(),
                duration: 2,
                deadline: 6
            }])
        )).expect("fail");
        let _ = solver.remove(x, 3);
        let _ = solver.remove(x, 4);
        let result = solver.propagate(propagator);
        assert!(matches!(result, Err(_)));
    }
}