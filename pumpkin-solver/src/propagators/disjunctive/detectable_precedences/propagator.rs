use std::collections::{HashMap, HashSet};
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
        
        Ok(())
    }

    fn propagate(&mut self, mut context: PropagationContextMut) -> PropagationStatusCP {
        //self.debug_propagate_from_scratch(context)
        let assignments = context.assignments.clone();
        let reason = self.tasks.iter().flat_map(|task| {
            vec!(
                predicate![task.starting_time >= Task::get_est(task, &assignments)],
                predicate![task.starting_time <= Task::get_lst(task, &assignments)]
            )
        }).collect::<PropositionalConjunction>();
        let mut timeline = Timeline::new(self.tasks.clone(), &assignments);
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
        let mut postponed_tasks: Vec<Task<Var>> = vec![];
        let mut propagations: HashMap<LocalId, (i32, PropositionalConjunction)> = HashMap::new();
        for i in i_ect.iter() {
            let ect_i  = Task::get_ect(i, &assignments);
            while j < i_lst.len() && lst_k < ect_i {
                if lst_k >= ect_k {
                    timeline.schedule_task(&Rc::new(k.clone()));
                } else {
                    if matches!(blocking_task, Some(_)) {
                        return Err(Inconsistency::Conflict(reason));
                    }
                    blocking_task = Some(k.clone());
                }
                j += 1;
                k = i_lst[j].clone();
                ect_k = Task::get_ect(&k, &assignments);
                lst_k = Task::get_lst(&k, &assignments);
            }
            if matches!(blocking_task, None) {
                let ect_timeline = timeline.earliest_completion_time(); 
                if !propagations.contains_key(&k.local_id) || ect_timeline > propagations.get(&k.local_id).unwrap().0 {
                    let _ = propagations.insert(k.local_id, (ect_timeline, reason.clone()));
                }
            } else {
                let Some(ref x) = blocking_task else {
                    panic!("This should not happen");
                };
                if i.local_id == x.local_id {
                    let mut ect_timeline = timeline.earliest_completion_time();
                    if !propagations.contains_key(&i.local_id) || ect_timeline > propagations.get(&i.local_id).unwrap().0 {
                        let _ = propagations.insert(i.local_id, (ect_timeline, reason.clone()));
                    } 
                    timeline.schedule_task(&Rc::new(i.clone()));
                    blocking_task = None;
                    ect_timeline = timeline.earliest_completion_time();
                    for z in postponed_tasks.iter() {
                        if !propagations.contains_key(&z.local_id) || ect_timeline > propagations.get(&z.local_id).unwrap().0 {
                            let _ = propagations.insert(z.local_id, (ect_timeline, reason.clone()));
                        } 
                    }
                    postponed_tasks.clear();
                } else {
                    postponed_tasks.push(i.clone());
                }
            }
        }
        for (local_id, (ect, reason)) in propagations.iter() {
            let _ = context.set_lower_bound(&self.tasks[local_id.unpack() as usize].starting_time.clone(), *ect, reason.clone());
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
        //assert!(matches!(result, Err(_)));
    }

    #[test]
    fn test_prop() {
        let mut solver = TestSolver::default();
        let w = solver.new_variable(0, 15);
        let x = solver.new_variable(2, 13);
        let y = solver.new_variable(9, 23);
        let z = solver.new_variable(12, 14);
        let tasks = [
            ArgTask {
                starting_time:w, 
                duration: 4,
                deadline: 19,
            },
            ArgTask {
                starting_time: x,
                duration: 9,
                deadline: 22,
            },
            ArgTask {
                starting_time: y,
                duration: 7,
                deadline: 30,
            },
            ArgTask {
                starting_time: z,
                duration: 6,
                deadline: 20
            }
        ]; 
        assert!(solver.lower_bound(y) == 9);
        assert!(solver.lower_bound(z) == 12);
        let propagator = solver.new_propagator(DetectablePrecedencesPropagator::new(
            Rc::new(tasks)
        )).expect("fail");
        assert!(solver.lower_bound(x) == 2);
        assert!(solver.lower_bound(y) == 19);
        assert!(solver.lower_bound(z) == 13);
    }
}