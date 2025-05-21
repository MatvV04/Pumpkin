use std::cmp::max;
use std::cmp::min;
use std::collections::HashMap;
use std::fmt::Debug;
use std::rc::Rc;

use super::TaskDisj;
use super::UnionFind;
use crate::{engine::Assignments, variables::IntegerVariable};

pub(crate) struct Timeline {
    pub(crate) t: Vec<i32>,
    pub(crate) c: Vec<i32>,
    pub(crate) m: Vec<i32>,
    pub(crate) e: i32,
    pub(crate) s: UnionFind,
}

impl Timeline {
    pub(crate) fn new<Var: IntegerVariable + 'static>(
        tasks: Rc<[TaskDisj<Var>]>,
        assignments: &Assignments,
    ) -> Self {
        let mut tasks_est = tasks.iter().cloned().collect::<Vec<TaskDisj<Var>>>();
        tasks_est.sort_by(|a, b| TaskDisj::get_est(a, assignments).cmp(&TaskDisj::get_est(b, assignments)));

        let mut t = vec![];
        let mut c = vec![];
        let mut m: Vec<i32> = vec![0; tasks_est.len()];

        for task in tasks_est.iter() {
            let est = TaskDisj::get_est(task, assignments);
            if t.len() == 0 || t[t.len() - 1] != est {
                t.push(est);
            }
            m[TaskDisj::get_id(&Rc::new(task.clone()))] = (t.len() - 1) as i32;
        }
        let highest_lct = tasks
            .iter()
            .map(|task| TaskDisj::get_lct(task, assignments))
            .max()
            .unwrap();
        t.push(highest_lct + tasks.iter().map(|task| task.duration).sum::<i32>());
        for k in 0..t.len() - 1 {
            c.push(t[k + 1] - t[k]);
        }
        let n = t.len();
        Timeline {
            t: t,
            c: c,
            m: m,
            e: -1,
            s: UnionFind::new(n as i32),
        }
    }

    pub(crate) fn schedule_task<Var: IntegerVariable + 'static>(
        &mut self,
        task: &Rc<TaskDisj<Var>>,
    ) -> () {
        let mut rho = task.duration;
        let mut k = self.s.find(self.m[TaskDisj::get_id(task)]) as usize;

        while rho > 0 {
            let delta = min(self.c[k], rho);
            rho -= delta;
            self.c[k] -= delta;
            if self.c[k] == 0 {
                let _ = self.s.union(k as i32, (k + 1) as i32);
                k = self.s.find(k as i32) as usize;
            }
        }
        self.e = max(self.e, k as i32);
    }

    pub(crate) fn earliest_completion_time(&self) -> i32 {
        if self.e == -1 {
            return 0;
        }
        self.t[(self.e + 1) as usize] - self.c[self.e as usize]
    }

    fn print_uf(&mut self) {
        let mut uf_map: HashMap<i32, Vec<i32>> = HashMap::new();
        for i in 0..self.s.size() {
            let root = self.s.find(i);
            uf_map.entry(root).or_insert_with(Vec::new).push(i);
        }
        let mut vals = uf_map.values().cloned().collect::<Vec<Vec<i32>>>();
        vals.iter_mut().for_each(|i| {
            i.sort();
        });
        vals.sort();
        println!("{:?}", vals);
    }
}

impl Debug for Timeline {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Timeline")
            .field("t", &self.t)
            .field("c", &self.c)
            .field("m", &self.m)
            .field("e", &self.e)
            .finish()
    }
}

pub(crate) struct RevTimeline {
    pub(crate) t: Vec<i32>,
    pub(crate) c: Vec<i32>,
    pub(crate) m: Vec<i32>,
    pub(crate) e: i32,
    pub(crate) s: UnionFind,
}

impl RevTimeline {
    pub(crate) fn new<Var: IntegerVariable + 'static>(
        tasks: Rc<[TaskDisj<Var>]>,
        assignments: &Assignments,
    ) -> Self {
        //let mut tasks_est = tasks.iter().cloned().collect::<Vec<TaskDisj<Var>>>();
        //tasks_est.sort_by(|a, b| TaskDisj::get_est(a, assignments).cmp(&TaskDisj::get_est(b, assignments)));
        let mut tasks_lct = tasks.iter().cloned().collect::<Vec<TaskDisj<Var>>>();
        tasks_lct.sort_by(|a, b| TaskDisj::get_lct(b, assignments).cmp(&TaskDisj::get_lct(a, assignments)));
        let mut t = vec![];
        let mut c = vec![];
        let mut m: Vec<i32> = vec![0; tasks_lct.len()];

        for task in tasks_lct.iter() {
            //let est = TaskDisj::get_est(task, assignments);
            let lct = TaskDisj::get_lct(task, assignments);
            if t.len() == 0 || t[t.len() - 1] != lct {
                t.push(lct);
            }
            m[TaskDisj::get_id(&Rc::new(task.clone()))] = (t.len() - 1) as i32;
        }
        /*let highest_lct = tasks
            .iter()
            .map(|task| TaskDisj::get_lct(task, assignments))
            .max()
            .unwrap();*/
        let lowest_est = tasks.iter().map(|task| TaskDisj::get_est(task, assignments)).min().unwrap();
        t.push(lowest_est - tasks.iter().map(|task| task.duration).sum::<i32>());
        for k in 0..t.len() - 1 {
            c.push(t[k] - t[k+1]);
        }
        let n = t.len();
        RevTimeline {
            t: t,
            c: c,
            m: m,
            e: -1,
            s: UnionFind::new(n as i32),
        }
    }

    pub(crate) fn schedule_task<Var: IntegerVariable + 'static>(
        &mut self,
        task: &Rc<TaskDisj<Var>>,
    ) -> () {
        let mut rho = task.duration;
        let mut k = self.s.find(self.m[TaskDisj::get_id(task)]) as usize;

        while rho > 0 {
            let delta = min(self.c[k], rho);
            rho -= delta;
            self.c[k] -= delta;
            if self.c[k] == 0 {
                let _ = self.s.union(k as i32, (k + 1) as i32);
                k = self.s.find(k as i32) as usize;
            }
        }
        self.e = max(self.e, k as i32);
    }

    pub(crate) fn latest_starting_time(&self) -> i32 {
        if self.e == -1 {
            return self.t[0];
        }
        self.t[(self.e + 1) as usize] + self.c[self.e as usize]
    }

    fn print_uf(&mut self) {
        let mut uf_map: HashMap<i32, Vec<i32>> = HashMap::new();
        for i in 0..self.s.size() {
            let root = self.s.find(i);
            uf_map.entry(root).or_insert_with(Vec::new).push(i);
        }
        let mut vals = uf_map.values().cloned().collect::<Vec<Vec<i32>>>();
        vals.iter_mut().for_each(|i| {
            i.sort();
        });
        vals.sort();
        println!("{:?}", vals);
    }
}

impl Debug for RevTimeline {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Timeline")
            .field("t", &self.t)
            .field("c", &self.c)
            .field("m", &self.m)
            .field("e", &self.e)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use core::time;
    use std::rc::Rc;

    use super::Timeline;
    use crate::engine::propagation::LocalId;
    use crate::engine::test_solver::TestSolver;
    use crate::propagators::disjunctive::TaskDisj;

    #[test]
    fn test_constructor() {
        let mut solver = TestSolver::default();
        let x = solver.new_variable(4, 10);
        let y = solver.new_variable(1, 4);
        let z = solver.new_variable(5, 6);
        let tasks = [
            TaskDisj {
                starting_time: x,
                duration: 5,
                deadline: 15,
                local_id: LocalId::from(0),
            },
            TaskDisj {
                starting_time: y,
                duration: 6,
                deadline: 10,
                local_id: LocalId::from(1),
            },
            TaskDisj {
                starting_time: z,
                deadline: 8,
                duration: 2,
                local_id: LocalId::from(2),
            },
        ];
        let mut timeline = Timeline::new(Rc::new(tasks.clone()), &solver.assignments);
        println!("{:?}", timeline);
        timeline.print_uf();
        timeline.schedule_task(&Rc::new(tasks[0].clone()));
        println!("{:?}", timeline);
        timeline.print_uf();
        assert!(timeline.earliest_completion_time() == 9);
        timeline.schedule_task(&Rc::new(tasks[1].clone()));
        assert!(timeline.earliest_completion_time() == 12);
        timeline.schedule_task(&Rc::new(tasks[2].clone()));
        assert!(timeline.earliest_completion_time() == 14);
    }

    #[test]
    fn test_rev() {
        let mut solver = TestSolver::default();
        let w = solver.new_variable(0, 15);
        let x = solver.new_variable(2, 13);
        let y = solver.new_variable(9, 23);
        let z = solver.new_variable(12, 14);
        let tasks = [
            TaskDisj {
                starting_time: w,
                duration: 4,
                deadline: 19,
                local_id: LocalId::from(0),
            },
            TaskDisj {
                starting_time: x,
                duration: 9,
                deadline: 22,
                local_id: LocalId::from(1),
            },
            TaskDisj {
                starting_time: y,
                duration: 7,
                deadline: 30,
                local_id: LocalId::from(2),
            },
            TaskDisj {
                starting_time: z,
                deadline: 20,
                duration: 6,
                local_id: LocalId::from(3),
            },
        ];
        let mut timeline = super::RevTimeline::new(Rc::new(tasks.clone()), &solver.assignments);
        println!("{:?}", timeline);
        timeline.print_uf();

        timeline.schedule_task(&Rc::new(tasks[2].clone()));
        println!("{:?}", timeline);
        timeline.print_uf();
        assert!(timeline.latest_starting_time() == 23);
        timeline.schedule_task(&Rc::new(tasks[1].clone()));
        println!("{:?}", timeline);
        timeline.print_uf();
        assert!(timeline.latest_starting_time() == 13);
       // timeline.schedule_task(&Rc::new(tasks[0].clone()));
        //println!("{:?}", timeline);
        //timeline.print_uf();
        //assert!(timeline.earliest_completion_time() == -1);
    }
}
