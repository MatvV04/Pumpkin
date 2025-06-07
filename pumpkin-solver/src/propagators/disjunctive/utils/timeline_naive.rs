use std::cmp::max;
use std::cmp::min;
use std::collections::HashMap;
use std::fmt::Debug;
use std::rc::Rc;

use super::TaskDisj;
use super::UnionFind;
use crate::engine::propagation::LocalId;
use crate::{engine::Assignments, variables::IntegerVariable};

pub(crate) struct TimelineNaive {
    pub(crate) t: Vec<i32>,
    pub(crate) c: Vec<i32>,
    pub(crate) m: Vec<i32>,
    pub(crate) e: i32,
    pub(crate) s: UnionFind,
    pub(crate) lower: i32
}

impl TimelineNaive {
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
        let lower = tasks.iter().map(|task| task.starting_time.lower_bound(assignments)).min().unwrap();
        TimelineNaive {
            t: t,
            c: c,
            m: m,
            e: -1,
            s: UnionFind::new(n as i32),
            lower: lower,
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
            return self.lower;
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