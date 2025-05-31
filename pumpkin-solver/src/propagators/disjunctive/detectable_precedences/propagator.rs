use core::task;
use std::collections::HashMap;
use std::rc::Rc;

use enumset::enum_set;

use crate::basic_types::Inconsistency;
use crate::basic_types::PropagationStatusCP;
use crate::conjunction;
use crate::engine::opaque_domain_event::OpaqueDomainEvent;
use crate::engine::propagation::contexts::PropagationContextWithTrailedValues;
use crate::engine::propagation::EnqueueDecision;
use crate::engine::propagation::LocalId;
use crate::engine::propagation::PropagationContext;
use crate::engine::propagation::PropagationContextMut;
use crate::engine::propagation::Propagator;
use crate::engine::propagation::PropagatorInitialisationContext;
use crate::engine::Assignments;
use crate::engine::DomainEvents;
use crate::engine::IntDomainEvent;
use crate::predicate;
use crate::predicates::PropositionalConjunction;
use crate::propagators::disjunctive::ArgTaskDisj;
use crate::propagators::disjunctive::TaskDisj;
use crate::propagators::disjunctive::Timeline;
use crate::propagators::RevTimeline;
use crate::variables::IntegerVariable;

#[derive(Clone, Debug)]
pub(crate) struct DetectablePrecedencesPropagator<Var> {
    tasks: Rc<[TaskDisj<Var>]>,
}

impl<Var> DetectablePrecedencesPropagator<Var>
where
    Var: IntegerVariable + 'static,
{
    pub(crate) fn new(tasks: Rc<Vec<ArgTaskDisj<Var>>>) -> Self {
        DetectablePrecedencesPropagator {
            tasks: tasks
                .iter()
                .enumerate()
                .map(|(i, task)| TaskDisj {
                    starting_time: task.starting_time.clone(),
                    duration: task.duration,
                    local_id: LocalId::from(i as u32),
                })
                .collect(),
        }
    }
    fn propagate_upper_bound(&mut self, mut context: PropagationContextMut) -> Result<(), Inconsistency> {
        let assignments = context.assignments.clone();
        let mut timeline = RevTimeline::new(self.tasks.clone(), &assignments);
        let naive_reason = self.tasks.iter().flat_map(|task| {
            let est = TaskDisj::get_est(task, &assignments);
            let lst = TaskDisj::get_lst(task, &assignments);
            vec![
                predicate![task.starting_time >= est],
                predicate![task.starting_time <= lst],
            ]
        }).collect::<PropositionalConjunction>();
        let mut i_lst = self.tasks.iter().cloned().collect::<Vec<TaskDisj<Var>>>();
        i_lst.sort_by(|a, b| {
            let a_lst = TaskDisj::get_lst(a, &assignments);
            let b_lst = TaskDisj::get_lst(b, &assignments);
            b_lst.cmp(&a_lst)
        });
        let mut i_ect = self.tasks.iter().cloned().collect::<Vec<TaskDisj<Var>>>();
        i_ect.sort_by(|a, b| {
            let a_ect = TaskDisj::get_ect(a, &assignments);
            let b_ect = TaskDisj::get_ect(b, &assignments);
            b_ect.cmp(&a_ect)
        });
        let mut j = 0;
        let mut k = i_ect[0].clone();
        let mut ect_k = TaskDisj::get_ect(&k, &assignments);
        let mut lst_k = TaskDisj::get_lst(&k, &assignments);
        let mut blocking_task: Option<TaskDisj<Var>> = None;
        let mut postponed_tasks: Vec<TaskDisj<Var>> = vec![];
        let mut propagations: HashMap<LocalId, (i32, PropositionalConjunction)> = HashMap::new();
        for i in i_lst.iter() {
            let lst_i = TaskDisj::get_lst(i, &assignments);
            while j < i_lst.len() - 1 && ect_k > lst_i {
                if lst_k >= ect_k {
                    timeline.schedule_task(&Rc::new(k.clone()));
                } else {
                    if matches!(blocking_task, Some(_)) {
                        let block_task = blocking_task.clone().unwrap();
                        let r = conjunction!(
                            [block_task.starting_time >= TaskDisj::get_est(&block_task, &assignments)] & [block_task.starting_time <= TaskDisj::get_lst(&block_task, &assignments)] &
                            [k.starting_time >= TaskDisj::get_est(&k, &assignments)] &
                            [k.starting_time <= TaskDisj::get_lst(&k, &assignments)]
                        );
                        return Err(Inconsistency::Conflict(r));
                    }
                    blocking_task = Some(k.clone());
                }
                j += 1;
                k = i_ect[j].clone();
                ect_k = TaskDisj::get_ect(&k, &assignments);
                lst_k = TaskDisj::get_lst(&k, &assignments);
            }
            if matches!(blocking_task, None) {
                let lst_timeline = timeline.latest_starting_time();
                if !propagations.contains_key(&i.local_id)
                    || lst_timeline - i.duration < propagations.get(&i.local_id).unwrap().0
                    
                {
                    let reason = self.get_explanation_right(i, &timeline, &assignments);
                    let _ = propagations.insert(i.local_id, (lst_timeline - i.duration, naive_reason.clone()));
                }
            } else {
                let Some(ref x) = blocking_task else {
                    panic!("This should not happen");
                };
                if i.local_id == x.local_id {
                    let mut lst_timeline = timeline.latest_starting_time();
                    if !propagations.contains_key(&i.local_id)
                        || lst_timeline - i.duration < propagations.get(&i.local_id).unwrap().0
                    {
                        let reason = self.get_explanation_right(i, &timeline, &assignments);
                        let _ = propagations.insert(i.local_id, (lst_timeline - i.duration, naive_reason.clone()));
                    }
                    timeline.schedule_task(&Rc::new(i.clone()));
                    blocking_task = None;
                    lst_timeline = timeline.latest_starting_time();
                    for z in postponed_tasks.iter() {
                        if !propagations.contains_key(&z.local_id)
                            || lst_timeline - z.duration < propagations.get(&z.local_id).unwrap().0
                        {
                            let reason = self.get_explanation_right(z, &timeline, &assignments);
                            let _ = propagations.insert(z.local_id, (lst_timeline - z.duration, naive_reason.clone()));
                        }
                    }
                    postponed_tasks.clear();
                } else {
                    postponed_tasks.push(i.clone());
                }
            }
        }
        for (local_id, (lst, reason)) in propagations.iter() {
            let task = &self.tasks[local_id.unpack() as usize];
            if *lst >= TaskDisj::get_lst(task, &assignments) {
                continue;
            }
            let x = context.set_upper_bound(
                &task.starting_time.clone(),
                *lst,
                reason.clone(),
            );
            if matches!(x, Err(_)) {
                let mut conflict_reason = reason.clone();
                conflict_reason.push(predicate![task.starting_time >= TaskDisj::get_est(task, &assignments)]);
                return Err(Inconsistency::Conflict(reason.clone()));
            }
        }
        Ok(())    
    }

    fn get_explanation_left(&self, task: &TaskDisj<Var>, timeline: &Timeline, assignments: &Assignments) -> PropositionalConjunction {
        let omega = timeline.get_omega();
        let p_omega = omega.iter().map(|id| {
            let omega_task = &self.tasks[id.unpack() as usize];
            omega_task.duration
        }).sum::<i32>();
        let max_lst = omega.iter().map(|id| {
            TaskDisj::get_lst(&self.tasks[id.unpack() as usize], assignments)
        }).max().unwrap_or(0);
        let est_i = TaskDisj::get_est(task, assignments);
        let p_i = task.duration;
        let delta = est_i + p_i - max_lst - 1;
        let ceiled_delta = (delta + 1) / 2;
        //let mut reason = conjunction!([task.starting_time >= est_i - ceiled_delta]);
        let mut reason = conjunction!([task.starting_time >= est_i]);
        reason.extend(omega.iter().flat_map(|id| {
            let omega_task = &self.tasks[id.unpack() as usize];
          /* vec![
                predicate![omega_task.starting_time >= est_i - ceiled_delta - p_omega],
                predicate![omega_task.starting_time <= est_i + p_i - ceiled_delta - 1]
            ]*/
            vec![
                predicate![omega_task.starting_time >= TaskDisj::get_est(omega_task, assignments)],
                predicate![omega_task.starting_time <= TaskDisj::get_lst(omega_task, assignments)],
            ]
        }));
        reason
    }

    fn get_explanation_right(&self, task: &TaskDisj<Var>, timeline: &RevTimeline, assignments: &Assignments) -> PropositionalConjunction {
        let omega = timeline.get_omega();
        let p_omega = omega.iter().map(|id| {
            let omega_task = &self.tasks[id.unpack() as usize];
            omega_task.duration
        }).sum::<i32>();
        let min_est = omega.iter().map(|id| {
            TaskDisj::get_est(&self.tasks[id.unpack() as usize], assignments)
        }).min().unwrap_or(0);
        let est_i = TaskDisj::get_est(task, assignments);
        let lst_i = TaskDisj::get_lst(task, assignments);
        let p_i = task.duration;
        let delta = min_est - est_i - p_i + 1;
        let ceiled_delta = (delta + 1) / 2;
        //let mut reason = conjunction!([task.starting_time <= min_est + ceiled_delta]);
        let mut reason = conjunction!([task.starting_time <= lst_i]);
        reason.extend(omega.iter().flat_map(|id| {
            let omega_task = &self.tasks[id.unpack() as usize];
          /* vec![
                predicate![omega_task.starting_time >= min_est + ceiled_delta - p_omega],
                predicate![omega_task.starting_time <= min_est + p_i + ceiled_delta - 1]
            ]*/
            vec![
                predicate![omega_task.starting_time >= TaskDisj::get_est(omega_task, assignments)],
                predicate![omega_task.starting_time <= TaskDisj::get_lst(omega_task, assignments)],
            ]
        }));
        reason
    }

}

impl<Var> Propagator for DetectablePrecedencesPropagator<Var>
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
        _event: OpaqueDomainEvent,
    ) -> EnqueueDecision {
        EnqueueDecision::Enqueue
    }

    fn notify_backtrack(
        &mut self,
        _context: PropagationContext,
        local_id: LocalId,
        event: OpaqueDomainEvent,
    ) {
    }

    fn initialise_at_root(
        &mut self,
        context: &mut PropagatorInitialisationContext,
    ) -> Result<(), PropositionalConjunction> {
        self.tasks.iter().for_each(|task| {
            let _ = context.register(
                task.starting_time.clone(),
                DomainEvents::create_with_int_events(enum_set!(
                    IntDomainEvent::LowerBound | IntDomainEvent::UpperBound
                )),
                
                task.local_id,
            );
            /*let _ = context.register_for_backtrack_events(
                task.starting_time.clone(),
                DomainEvents::create_with_int_events(enum_set!(
                    IntDomainEvent::Assign | IntDomainEvent::Removal
                )),
                task.local_id,
            );*/
        });
        Ok(())
    }

    fn debug_propagate_from_scratch(&self, context: PropagationContextMut) -> PropagationStatusCP {
        let assignments = context.assignments;
        for task in self.tasks.iter() {
            let ect = TaskDisj::get_ect(task, &assignments);
            let lst = TaskDisj::get_lst(task, &assignments);
            if ect > TaskDisj::get_lct(task, &assignments) {
                let reason: PropositionalConjunction =
                    predicate![task.starting_time >= lst - 1].into();
                return Err(Inconsistency::Conflict(reason));
            }
        }

        Ok(())
    }

    fn propagate(&mut self, mut context: PropagationContextMut) -> PropagationStatusCP {
        // self.debug_propagate_from_scratch(context)
        let assignments = context.assignments.clone();
        let mut timeline = Timeline::new(self.tasks.clone(), &assignments);
        let mut i_lst = self.tasks.iter().cloned().collect::<Vec<TaskDisj<Var>>>();
        i_lst.sort_by(|a, b| {
            let a_lst = TaskDisj::get_lst(a, &assignments);
            let b_lst = TaskDisj::get_lst(b, &assignments);
            a_lst.cmp(&b_lst)
        });
        let mut i_ect = self.tasks.iter().cloned().collect::<Vec<TaskDisj<Var>>>();
        i_ect.sort_by(|a, b| {
            let a_ect = TaskDisj::get_ect(a, &assignments);
            let b_ect = TaskDisj::get_ect(b, &assignments);
            a_ect.cmp(&b_ect)
        });
        let mut j = 0;
        let mut k = i_lst[0].clone();
        let mut ect_k = TaskDisj::get_ect(&k, &assignments);
        let mut lst_k = TaskDisj::get_lst(&k, &assignments);
        let mut blocking_task: Option<TaskDisj<Var>> = None;
        let mut postponed_tasks: Vec<TaskDisj<Var>> = vec![];
        let mut propagations: HashMap<LocalId, (i32, PropositionalConjunction)> = HashMap::new();
        for i in i_ect.iter() {
            let ect_i = TaskDisj::get_ect(i, &assignments);
            while j < i_lst.len() - 1 && lst_k < ect_i {
                if lst_k >= ect_k {
                    timeline.schedule_task(&Rc::new(k.clone()));
                } else {
                    if matches!(blocking_task, Some(_)) {
                        let block_task = blocking_task.clone().unwrap();
                        let r = conjunction!(
                            [block_task.starting_time >= TaskDisj::get_est(&block_task, &assignments)] & [block_task.starting_time <= TaskDisj::get_lst(&block_task, &assignments)] &
                            [k.starting_time >= TaskDisj::get_est(&k, &assignments)] &
                            [k.starting_time <= TaskDisj::get_lst(&k, &assignments)]
                        );
                        return Err(Inconsistency::Conflict(r));
                    }
                    blocking_task = Some(k.clone());
                }
                j += 1;
                k = i_lst[j].clone();
                ect_k = TaskDisj::get_ect(&k, &assignments);
                lst_k = TaskDisj::get_lst(&k, &assignments);
            }
            if matches!(blocking_task, None) {
                let ect_timeline = timeline.earliest_completion_time();
                if !propagations.contains_key(&i.local_id)
                    || ect_timeline > propagations.get(&i.local_id).unwrap().0
                {
                    let reason = self.get_explanation_left(i, &timeline, &assignments);
                    let _ = propagations.insert(i.local_id, (ect_timeline, reason));
                }
            } else {
                let Some(ref x) = blocking_task else {
                    panic!("This should not happen");
                };
                if i.local_id == x.local_id {
                    let mut ect_timeline = timeline.earliest_completion_time();
                    if !propagations.contains_key(&i.local_id)
                        || ect_timeline > propagations.get(&i.local_id).unwrap().0
                    {
                        let reason = self.get_explanation_left(i, &timeline, &assignments);
                        let _ = propagations.insert(i.local_id, (ect_timeline, reason));
                    }
                    timeline.schedule_task(&Rc::new(i.clone()));
                    blocking_task = None;
                    ect_timeline = timeline.earliest_completion_time();
                    for z in postponed_tasks.iter() {
                        if !propagations.contains_key(&z.local_id)
                            || ect_timeline > propagations.get(&z.local_id).unwrap().0
                        {
                            let reason = self.get_explanation_left(z, &timeline, &assignments);
                            let _ = propagations.insert(z.local_id, (ect_timeline, reason));
                        }
                    }
                    postponed_tasks.clear();
                } else {
                    postponed_tasks.push(i.clone());
                }
            }
        }
        for (local_id, (ect, reason)) in propagations.iter() {
            let task = &self.tasks[local_id.unpack() as usize];
            if *ect <= TaskDisj::get_est(task, &assignments) {
                continue;
            }
            let x = context.set_lower_bound(
                &task.starting_time.clone(),
                *ect,
                reason.clone(),
            );
            if matches!(x, Err(_)) {
                let mut conflict_reason = reason.clone();
                conflict_reason.push(predicate![task.starting_time <= TaskDisj::get_lst(task, &assignments)]);
                return Err(Inconsistency::Conflict(conflict_reason));
            }
        }
        self.propagate_upper_bound(context) 
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use crate::basic_types::Inconsistency;
    use crate::engine::propagation::LocalId;
    use crate::engine::propagation::PropagationContextMut;
    use crate::engine::propagation::Propagator;
    use crate::engine::test_solver::TestSolver;
    use crate::propagators::disjunctive::ArgTaskDisj;
    use crate::propagators::disjunctive::DetectablePrecedencesPropagator;
    use crate::propagators::TaskDisj;
    use crate::propagators::Timeline;


    #[test]
    fn test_exp() {
        let mut solver = TestSolver::default();
        let x = solver.new_variable(0, 2);
        let y = solver.new_variable(0, 10);

        let argtasks = vec![
            ArgTaskDisj {
                starting_time: x.clone(),
                duration: 2,
            },
            ArgTaskDisj {
                starting_time: y.clone(),
                duration: 4,
            },
        ];
        let tasks = [
            TaskDisj {
                starting_time: x.clone(),
                duration: 2,
                local_id: LocalId::from(0),
            },
            TaskDisj {
                starting_time: y.clone(),
                duration: 4,
                local_id: LocalId::from(1),
            },
        ];
        let propagator = DetectablePrecedencesPropagator::new(Rc::new(argtasks));
        let assignments = solver.assignments.clone();
        let mut timeline = Timeline::new(Rc::new(tasks.clone()), &assignments);
        timeline.schedule_task(&Rc::new(tasks[0].clone()));
        let reason = propagator.get_explanation_left(&tasks[1], &timeline, &assignments);
        println!("{:?}", reason);
    }
    #[test]
    fn test_debug_propagate() {
        let mut solver = TestSolver::default();
        let x = solver.new_variable(5, 8);

        let propagator = solver
            .new_propagator(DetectablePrecedencesPropagator::new(Rc::new(vec![ArgTaskDisj {
                starting_time: x.clone(),
                duration: 2,
            }])))
            .expect("fail");
        let result = solver.propagate(propagator);
        assert!(result.is_ok());
    }
    #[test]
    fn test_debug_propagate_fail() {
        let mut solver = TestSolver::default();
        let x = solver.new_variable(3, 8);

        let propagator = solver
            .new_propagator(DetectablePrecedencesPropagator::new(Rc::new(vec![ArgTaskDisj {
                starting_time: x.clone(),
                duration: 2,
            }])))
            .expect("fail");
        let _ = solver.remove(x, 3);
        let _ = solver.remove(x, 4);
        let result = solver.propagate(propagator);
        // assert!(matches!(result, Err(_)));
    }

    #[test]
    fn test_prop() {
        let mut solver = TestSolver::default();
        let w = solver.new_variable(0, 15);
        let x = solver.new_variable(2, 13);
        let y = solver.new_variable(9, 23);
        let z = solver.new_variable(12, 14);
        let tasks = vec![
            ArgTaskDisj {
                starting_time: w,
                duration: 4,
            },
            ArgTaskDisj {
                starting_time: x,
                duration: 9,
            },
            ArgTaskDisj {
                starting_time: y,
                duration: 7,
            },
            ArgTaskDisj {
                starting_time: z,
                duration: 6,
            },
        ];
        assert!(solver.lower_bound(y) == 9);
        assert!(solver.lower_bound(z) == 12);
        let propagator = solver
            .new_propagator(DetectablePrecedencesPropagator::new(Rc::new(tasks)))
            .expect("fail");
        assert!(solver.lower_bound(x) == 2);
        assert!(solver.lower_bound(y) == 19);
        assert!(solver.lower_bound(z) == 13);
    }

    #[test]
    fn test_prop_example(){
        let mut solver = TestSolver::default();
        let w = solver.new_variable(0, 4);
        let x = solver.new_variable(3,5);
        let y = solver.new_variable(7, 10);
        let z = solver.new_variable(4, 18);
        let tasks = vec![
            ArgTaskDisj {
                starting_time: w,
                duration: 2,
            },
            ArgTaskDisj {
                starting_time: x,
                duration: 5,
            },
            ArgTaskDisj {
                starting_time: y,
                duration: 5,
            },
            ArgTaskDisj {
                starting_time: z,
                duration: 2,
            },
        ];
        let propagator = solver
            .new_propagator(DetectablePrecedencesPropagator::new(Rc::new(tasks)))
            .expect("fail");
        assert!(solver.lower_bound(w) == 0);
        assert!(solver.lower_bound(x) == 3);
        assert!(solver.lower_bound(y) == 8);
        assert!(solver.lower_bound(z) == 8);

    
    }

    
}

