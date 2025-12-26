use std::collections::HashMap;

use crate::runtime::new::{
    arena::{Arena, Index, TripleArena},
    runtime::{Global, GlobalCont, Instance, Linear, Node, Shared, Value},
};

pub struct Freezer<'a> {
    variable_map: HashMap<(usize, usize), usize>,
    pub write: &'a mut Arena,
    pub num_vars: usize,
}

impl<'a> Freezer<'a> {
    pub fn new(write: &'a mut Arena) -> Self {
        Self {
            write,
            variable_map: HashMap::new(),
            num_vars: 0,
        }
    }
    fn freeze_value<P>(
        &mut self,
        read: &TripleArena,
        value: &Value<P>,
        mut leaves: impl FnMut(&mut Self, &TripleArena, &P) -> Index<Global>,
    ) -> Global {
        let value = value
            .map_ref_leaves(|p| Some(leaves(self, read, p)))
            .unwrap();
        Global::Value(value)
    }
    fn freeze_shared(&mut self, read: &TripleArena, node: &Shared) -> Global {
        todo!()
    }
    fn freeze_linear(&mut self, read: &TripleArena, node: &Linear) -> Global {
        todo!()
    }
    pub fn freeze_global(
        &mut self,
        read: &TripleArena,
        instance: &Instance,
        node: &Global,
    ) -> Index<Global> {
        let global = match node {
            Global::Variable(id) => {
                let node = instance.at(id, |slot| slot.take());
                if let Some(node) = node {
                    return self.freeze_node(read, &node);
                } else {
                    let addr = instance.identifier();
                    let id = *self.variable_map.entry((addr, *id)).or_insert_with(|| {
                        let res = self.num_vars;
                        self.num_vars += 1;
                        res
                    });
                    Global::Variable(id)
                }
            }
            Global::Package(index, index1, fan_behavior) => todo!(),
            Global::Destruct(global_cont) => match global_cont {
                GlobalCont::Continue => Global::Destruct(GlobalCont::Continue),
                GlobalCont::Par(index, index1) => todo!(),
                GlobalCont::Choice(index, index1) => todo!(),
            },
            Global::Value(value) => self.freeze_value(read, value, |this, read, p| {
                let global = read.get(*p);
                let p = this.freeze_global(read, instance, global);
                return p;
            }),
            Global::Fanout(index) => todo!(),
        };
        let r = self.write.alloc(global);
        r
    }
    pub fn freeze_node(&mut self, read: &TripleArena, node: &Node) -> Index<Global> {
        let node = (match node {
            Node::Linear(linear) => self.freeze_linear(read, linear),
            Node::Shared(shared) => self.freeze_shared(read, shared),
            Node::Global(instance, index) => {
                let global = read.get(*index);
                return self.freeze_global(read, instance, global);
            }
        });
        self.write.alloc(node)
    }
}
