use indexmap::IndexMap;

use crate::runtime::new::{
    arena::{Arena, ArenaTrim, Index, TripleArena},
    runtime::{Global, GlobalCont, Instance, Linear, Node, PackageBody, Shared, Value},
};

pub struct Freezer<'a> {
    variable_map: IndexMap<(usize, usize), usize>,
    pub write: &'a mut Arena,
    pub num_vars: usize,
    pub offset: ArenaTrim,
}

impl<'a> Freezer<'a> {
    pub fn new(read: &TripleArena, write: &'a mut Arena) -> Self {
        Self {
            write,
            variable_map: IndexMap::new(),
            num_vars: 0,
            offset: read.permanent.slots_end_indices(),
        }
    }
    fn intern(&mut self, read: &TripleArena, s: &str) -> Index<str> {
        if let Some(s) = read.interned(s) {
            s
        } else {
            self.write.intern(s)
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
                GlobalCont::Par(a, b) => {
                    let a = self.freeze_global(read, instance, read.get(*a));
                    let b = self.freeze_global(read, instance, read.get(*b));
                    Global::Destruct(GlobalCont::Par(a, b))
                }
                GlobalCont::Choice(captures, branches) => {
                    let captures = self.freeze_global(read, instance, read.get(*captures));
                    let len = self.variable_map.len();

                    let branches: Vec<_> = read
                        .get(*branches)
                        .into_iter()
                        .map(|(name, package_body)| {
                            self.variable_map.truncate(len);
                            let name = self.intern(read, read.get(*name));
                            let root =
                                self.freeze_global(read, instance, read.get(package_body.root));
                            let captures =
                                self.freeze_global(read, instance, read.get(package_body.captures));
                            let redexes: Vec<_> = read
                                .get(package_body.redexes)
                                .iter()
                                .map(|(a, b)| {
                                    let a = self.freeze_global(read, instance, read.get(*a));
                                    let b = self.freeze_global(read, instance, read.get(*b));
                                    (a, b)
                                })
                                .collect();
                            let redexes = self.write.alloc_clone(redexes.as_ref());
                            (
                                name,
                                PackageBody {
                                    root,
                                    captures,
                                    redexes,
                                    debug_name: package_body.debug_name.clone(),
                                },
                            )
                        })
                        .collect();
                    let branches = self.write.alloc_clone(branches.as_ref());
                    self.variable_map.truncate(len);
                    Global::Destruct(GlobalCont::Choice(captures, branches))
                }
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
        let node = match node {
            Node::Linear(linear) => self.freeze_linear(read, linear),
            Node::Shared(shared) => self.freeze_shared(read, shared),
            Node::Global(instance, index) => {
                let global = read.get(*index);
                return self.freeze_global(read, instance, global);
            }
        };
        self.write.alloc(node)
    }
}
