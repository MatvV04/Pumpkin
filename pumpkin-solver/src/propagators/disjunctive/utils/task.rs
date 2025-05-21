use std::fmt::Debug;
use std::rc::Rc;

use crate::engine::propagation::LocalId;
use crate::engine::Assignments;
use crate::variables::IntegerVariable;

#[derive(Clone)]
pub(crate) struct TaskDisj<Var> {
    pub(crate) starting_time: Var,
    pub(crate) duration: i32,
    pub(crate) deadline: i32,
    pub(crate) local_id: LocalId,
}

impl<Var: IntegerVariable + 'static> TaskDisj<Var> {
    pub(crate) fn get_id(task: &Rc<TaskDisj<Var>>) -> usize {
        task.local_id.unpack() as usize
    }

    pub(crate) fn get_ect(task: &TaskDisj<Var>, assignments: &Assignments) -> i32 {
        task.starting_time.lower_bound(assignments) + task.duration
    }

    pub(crate) fn get_lst(task: &TaskDisj<Var>, assignments: &Assignments) -> i32 {
        task.starting_time.upper_bound(assignments)
    }

    pub(crate) fn get_est(task: &TaskDisj<Var>, assignments: &Assignments) -> i32 {
        task.starting_time.lower_bound(assignments)
    }

    pub(crate) fn get_lct(task: &TaskDisj<Var>, assignments: &Assignments) -> i32 {
        task.starting_time.upper_bound(assignments) + task.duration
    }
}

impl<Var> Debug for TaskDisj<Var> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Task")
            .field("duration", &self.duration)
            .field("deadline", &self.deadline)
            .field("local_id", &self.local_id)
            .finish()
    }
}

pub(crate) struct ArgTaskDisj<Var> {
    pub(crate) starting_time: Var,
    pub(crate) duration: i32,
    pub(crate) deadline: i32,
}
