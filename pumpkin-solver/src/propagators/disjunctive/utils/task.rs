use std::rc::Rc;
use std::fmt::Debug; 
use crate::{engine::{propagation::LocalId, Assignments}, variables::IntegerVariable};



#[derive(Clone)]
pub (crate) struct Task<Var> {
    pub (crate) starting_time: Var,
    pub (crate) duration: i32,
    pub (crate) deadline: i32, 
    pub (crate) local_id: LocalId,
}

impl<Var: IntegerVariable + 'static> Task<Var> {
    pub (crate) fn get_id(task: &Rc<Task<Var>>) -> usize {
        task.local_id.unpack() as usize
    }

    pub (crate) fn get_ect(task: &Task<Var>, assignments: &Assignments) -> i32 {
        task.starting_time.lower_bound(assignments) + task.duration
    }

    pub (crate) fn get_lst(task: &Task<Var>, assignments: &Assignments) -> i32 {
        task.starting_time.upper_bound(assignments)
    }

    pub (crate) fn get_est(task: &Task<Var>, assignments: &Assignments) -> i32 {
        task.starting_time.lower_bound(assignments)
    }

    pub (crate) fn get_lct(task: &Task<Var>, assignments: &Assignments) -> i32 {
        task.starting_time.upper_bound(assignments) + task.duration
    }
}

impl<Var> Debug for Task<Var> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Task")
            .field("duration", &self.duration)
            .field("deadline", &self.deadline)
            .field("local_id", &self.local_id)
            .finish()
    }
}

pub (crate) struct ArgTask<Var> {
    pub (crate) starting_time: Var,
    pub (crate) duration: i32,
    pub (crate) deadline: i32, 
}

