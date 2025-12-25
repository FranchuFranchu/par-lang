use std::collections::HashMap;

use crate::runtime::new::{
    arena::TripleArena,
    runtime::{Global, Instance, Linear, Node, Shared},
};

pub struct Freezer<'a> {
    variable_map: HashMap<(usize, usize), usize>,
    pub arena: &'a mut TripleArena,
}

impl<'a> Freezer<'a> {
    pub fn new(arena: &'a mut TripleArena) -> Self {
        Self {
            arena,
            variable_map: HashMap::new(),
        }
    }
    fn freeze_shared(&mut self, node: &Shared) -> Global {
        todo!()
    }
    fn freeze_linear(&mut self, node: &Linear) -> Global {
        todo!()
    }
    pub fn freeze_global(&mut self, instance: &Instance, node: &Global) -> Global {
        todo!()
    }
    pub fn freeze_node(&mut self, node: &Node) -> Global {
        todo!()
    }
}
