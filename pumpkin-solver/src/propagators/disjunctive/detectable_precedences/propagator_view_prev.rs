use std::{cmp::Ordering, rc::Rc};

use enumset::enum_set;

use crate::{basic_types::{HashMap, Inconsistency, PropagationStatusCP}, conjunction, engine::{opaque_domain_event::OpaqueDomainEvent, predicates::predicate, propagation::{contexts::PropagationContextWithTrailedValues, EnqueueDecision, LocalId, PropagationContext, PropagationContextMut, Propagator, PropagatorInitialisationContext}, reason, Assignments, DomainEvents, IntDomainEvent}, predicate, predicates::PropositionalConjunction, propagators::{ArgTaskDisj, TaskDisj, Timeline, TimelineNaive, TimelinePrev}, pumpkin_assert_extreme, pumpkin_assert_moderate, variables::{IntegerVariable, TransformableVariable}};





#[derive(Clone, Debug)]
pub(crate) struct DetectablePrecedencesViewPropagatorPrev<Var: IntegerVariable> {
    tasks: Box<[TaskDisj<Var>]>,
    reversed_tasks: Box<[TaskDisj<<<Var as IntegerVariable>::AffineView as IntegerVariable>::AffineView>]>,
    root_level_bounds: Vec<(i32, i32)>,
    root_level_bounds_rev: Vec<(i32, i32)>, 
    i_ect: Vec<TaskDisj<Var>>,
    i_lst: Vec<TaskDisj<Var>>,
    i_ect_rev: Vec<TaskDisj<<<Var as IntegerVariable>::AffineView as IntegerVariable>::AffineView>>,
    i_lst_rev: Vec<TaskDisj<<<Var as IntegerVariable>::AffineView as IntegerVariable>::AffineView>>,
    
}


impl <Var: IntegerVariable + 'static> DetectablePrecedencesViewPropagatorPrev<Var> {
    pub(crate) fn new(arg_tasks: Vec<ArgTaskDisj<Var>>) -> Self {
        let tasks = arg_tasks
            .iter()
            .enumerate()
            .map(|(id, task)| TaskDisj {
                starting_time: task.starting_time.clone(),
                duration: task.duration,
                local_id: LocalId::from(id as u32),
            })
            .collect::<Vec<_>>();
        
        let reversed_tasks = tasks.
            iter()
            .map(|task| TaskDisj {
                starting_time: task.starting_time.clone().offset(task.duration).scaled(-1),
                duration: task.duration,
                local_id: task.local_id,
            }).collect::<Vec<_>>();
        DetectablePrecedencesViewPropagatorPrev{
            tasks: tasks.clone().into_boxed_slice(), 
            reversed_tasks: reversed_tasks.clone().into_boxed_slice(),
            root_level_bounds: vec![],
            root_level_bounds_rev: vec![],
            i_ect: tasks.clone(),
            i_lst: tasks.clone(),
            i_ect_rev: reversed_tasks.clone(),
            i_lst_rev: reversed_tasks.clone()
        }
    }
    
    
}

    fn detectable_precedences<Var:IntegerVariable + 'static>(tasks: &[TaskDisj<Var>], context: &mut PropagationContextMut, root_bounds: &Vec<(i32, i32)>, i_ect: &Vec<TaskDisj<Var>>, i_lst: &Vec<TaskDisj<Var>>) -> PropagationStatusCP {
        let assignments = context.assignments.clone();
        let mut timeline = TimelinePrev::new(tasks.clone().into(), &assignments);
        
        let reason = tasks.iter().flat_map(|task| {
            let est = TaskDisj::get_est(task, &assignments);
            let lst = TaskDisj::get_lst(task, &assignments);
            vec![
                predicate![task.starting_time >= est],
                predicate![task.starting_time <= lst],
            ]
        }).collect::<PropositionalConjunction>();

        let mut j = 0;
        let mut k = i_lst[0].clone();
        let mut ect_k = TaskDisj::get_ect(&k, &assignments);
        let mut lst_k = TaskDisj::get_lst(&k, &assignments);
        let mut blocking_task: Option<TaskDisj<Var>> = None;
        let mut postponed_tasks: Vec<TaskDisj<Var>> = vec![];
        let mut propagations: HashMap<LocalId, (i32, PropositionalConjunction)> = HashMap::default();
        for i in i_ect.iter() {
            let ect_i = TaskDisj::get_ect(i, &assignments);
            while j < i_lst.len() - 1 && lst_k < ect_i {
                if lst_k >= ect_k {
                    timeline.schedule_task(&Rc::new(k.clone()));
                } else {
                    if matches!(blocking_task, Some(_)) {
                        let block_task = blocking_task.clone().unwrap();
                       /*  let r = conjunction!(
                            [block_task.starting_time >= TaskDisj::get_est(&block_task, &assignments)] & [block_task.starting_time <= TaskDisj::get_lst(&block_task, &assignments)] &
                            [k.starting_time >= TaskDisj::get_est(&k, &assignments)] &
                            [k.starting_time <= TaskDisj::get_lst(&k, &assignments)]
                        );*/
                        let r = get_conflict_explanation(&block_task, &k, &assignments, root_bounds);
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
                    let reason = get_explanation_left(i,tasks,  &timeline, &assignments);
                    let _ = propagations.insert(i.local_id, (ect_timeline, reason.clone()));
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
                        let reason = get_explanation_left(i,tasks,  &timeline, &assignments);
                        let _ = propagations.insert(i.local_id, (ect_timeline, reason));
                    }
                    timeline.schedule_task(&Rc::new(i.clone()));
                    blocking_task = None;
                    ect_timeline = timeline.earliest_completion_time();
                    for z in postponed_tasks.iter() {
                        if !propagations.contains_key(&z.local_id)
                            || ect_timeline > propagations.get(&z.local_id).unwrap().0
                        {
                            let reason = get_explanation_left(z,tasks, &timeline, &assignments);
                            let _ = propagations.insert(z.local_id, (ect_timeline, reason));
                        }
                    }
                    postponed_tasks.clear();
                } else {
                    postponed_tasks.push(i.clone());
                }
            }
        }
        for i in i_ect.iter().rev() {
            if !propagations.contains_key(&i.local_id) {
                continue;
            }
            //let task = &tasks[id.unpack() as usize];
            let (ect, reason) = propagations.get(&i.local_id).unwrap();
            if *ect <= TaskDisj::get_est(i, &assignments) {
                continue;
            }
            let _x = context.set_lower_bound(
                &i.starting_time.clone(),
                *ect,
                reason.clone(),
            )?;
            /* 
            if matches!(x, Err(_)) {
                let mut conflict_reason = reason.clone();
                conflict_reason.push(predicate![i.starting_time <= TaskDisj::get_lst(i, &assignments)]);
                return Err(Inconsistency::Conflict(conflict_reason));
            }*/
        }
        /* 
        for (local_id, (ect, reason)) in propagations.iter() {
            let task = &tasks[local_id.unpack() as usize];
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
        }*/
        Ok(())
    }

    fn get_explanation_left<Var: IntegerVariable + 'static>(task: &TaskDisj<Var>, tasks: &[TaskDisj<Var>], timeline: &TimelinePrev, assignments: &Assignments) -> PropositionalConjunction {
        let mut reason = timeline.get_scheduled_tasks().iter().flat_map(|scheduled_task| {
            let task = &tasks[scheduled_task.unpack() as usize];
            vec![
                predicate![task.starting_time >= TaskDisj::get_est(task, assignments)],
                predicate![task.starting_time <= TaskDisj::get_lst(task, assignments)]
            ]
        }).collect::<PropositionalConjunction>();
        reason.push(predicate![task.starting_time >= TaskDisj::get_est(task, assignments)]);
        reason
    }


    fn get_conflict_explanation<Var: IntegerVariable + 'static>(a: &TaskDisj<Var>, b: &TaskDisj<Var>, assignments: &Assignments, root_bounds: &Vec<(i32, i32)>) -> PropositionalConjunction {

        return conjunction!(
            [a.starting_time >= TaskDisj::get_est(a, assignments)] &
            [a.starting_time <= TaskDisj::get_lst(a, assignments)] &
            [b.starting_time >= TaskDisj::get_est(b, assignments)] &
            [b.starting_time <= TaskDisj::get_lst(b, assignments)]
        );
        /*  
        let mut reason = PropositionalConjunction::new(vec![]);
        let p_omega = a.duration + b.duration;
        let est_omega = TaskDisj::get_est(a, assignments).min(TaskDisj::get_est(b, assignments));
        let lct_omega = TaskDisj::get_lct(a, assignments).max(TaskDisj::get_lct(b, assignments));
        //let mut offset = 0;
        
        let delta = (p_omega - (lct_omega - est_omega) - 1).max(0);

        let est_a = TaskDisj::get_est(a, assignments).min(est_omega - f64::floor(delta as f64 / 2.0) as i32);
        let est_b = TaskDisj::get_est(b, assignments).min(est_omega - f64::floor(delta as f64 / 2.0) as i32);

        let lst_a = TaskDisj::get_lst(a, assignments).max(lct_omega - a.duration + f64::ceil(delta as f64 / 2.0) as i32);
        let lst_b = TaskDisj::get_lst(b, assignments).max(lct_omega - b.duration + f64::ceil(delta as f64 / 2.0) as i32);

        if root_bounds[a.local_id.unpack() as usize].0 <= est_a {
            reason.push(predicate![a.starting_time >= est_a]);
        }
        if root_bounds[b.local_id.unpack() as usize].0 <= est_b {
            reason.push(predicate![b.starting_time >= est_b]);
        }
        if root_bounds[a.local_id.unpack() as usize].1 >= lst_a {
            reason.push(predicate![a.starting_time <= lst_a]);
        }
        if root_bounds[b.local_id.unpack() as usize].1 >= lst_b {
            reason.push(predicate![b.starting_time <= lst_b]);
        }
        
        reason*/
    }



impl <Var> Propagator for DetectablePrecedencesViewPropagatorPrev<Var>
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
        for i in 0..self.tasks.len() {
            let est_i = TaskDisj::get_est(&self.tasks[i], &context.assignments);
            let rev_est_i = TaskDisj::get_est(&self.reversed_tasks[i], &context.assignments);
            let lst_i = TaskDisj::get_lst(&self.tasks[i], &context.assignments);
            let rev_lst_i = TaskDisj::get_lst(&self.reversed_tasks[i], &context.assignments);
            self.root_level_bounds.push((est_i, lst_i));
            self.root_level_bounds_rev.push((rev_est_i, rev_lst_i));
        }
        self.i_ect.sort_by(|a,b| TaskDisj::get_ect(&a, &context.assignments).cmp(&TaskDisj::get_ect(&b, &context.assignments)));
        self.i_lst.sort_by(|a,b| TaskDisj::get_lst(&a, &context.assignments).cmp(&TaskDisj::get_lst(&b, &context.assignments)));
        self.i_ect_rev.sort_by(|a, b| TaskDisj::get_ect(&a, &context.assignments).cmp(&TaskDisj::get_ect(&b, &context.assignments)));
        self.i_lst_rev.sort_by(|a, b| TaskDisj::get_lst(&a, &context.assignments).cmp(&TaskDisj::get_lst(&b, &context.assignments)));
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
        self.i_ect.sort_by(|a,b| TaskDisj::get_ect(&a, &context.assignments).cmp(&TaskDisj::get_ect(&b, &context.assignments)));
        self.i_lst.sort_by(|a,b| TaskDisj::get_lst(&a, &context.assignments).cmp(&TaskDisj::get_lst(&b, &context.assignments)));
        detectable_precedences(&self.tasks, &mut context, &self.root_level_bounds, &self.i_ect, &self.i_lst)?;

        self.i_ect_rev.sort_by(|a, b| TaskDisj::get_ect(&a, &context.assignments).cmp(&TaskDisj::get_ect(&b, &context.assignments)));
        self.i_lst_rev.sort_by(|a, b| TaskDisj::get_lst(&a, &context.assignments).cmp(&TaskDisj::get_lst(&b, &context.assignments)));
        detectable_precedences(&self.reversed_tasks, &mut context, &self.root_level_bounds_rev, &self.i_ect_rev, &self.i_lst_rev)
    }
}