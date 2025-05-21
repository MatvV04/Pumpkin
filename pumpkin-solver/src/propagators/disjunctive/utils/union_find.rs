use std::fmt::Debug;

pub(crate) struct UnionFind {
    parent: Vec<i32>,
    n: i32,
}

impl UnionFind {
    pub(crate) fn new(n: i32) -> Self {
        let mut parent = vec![0; n as usize];
        for i in 0..n {
            parent[i as usize] = i;
        }
        UnionFind { parent, n }
    }

    pub(crate) fn find(&mut self, x: i32) -> i32 {
        if self.parent[x as usize] != x {
            self.parent[x as usize] = self.find(self.parent[x as usize]);
        }
        self.parent[x as usize]
    }

    pub(crate) fn union(&mut self, x: i32, y: i32) -> bool {
        let root_x = self.find(x);
        let root_y = self.find(y);
        if root_x == root_y {
            return false;
        }
        self.parent[root_x as usize] = root_y;
        true
    }

    pub(crate) fn size(&self) -> i32 {
        self.n
    }
}
impl Debug for UnionFind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("UnionFind")
            .field("parent", &self.parent)
            .field("n", &self.n)
            .finish()
    }
}
