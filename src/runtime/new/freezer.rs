use std::sync::OnceLock;

use indexmap::IndexMap;

use crate::runtime::{
    new::{
        arena::{Arena, ArenaTrim, Index, TripleArena, HIGHER_HALF},
        runtime::{
            Global, GlobalCont, Instance, Linear, Node, Package, PackageBody, PackagePtr, Shared,
            SharedHole, SyncShared, Value,
        },
    },
    old::net::FanBehavior,
};

pub struct Freezer<'a> {
    variable_map: IndexMap<(usize, usize), (usize, bool)>,
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
        mut leaves: impl FnMut(&mut Self, &TripleArena, &P) -> Global,
    ) -> Global {
        let value = value
            .map_ref_leaves(|p| {
                Some({
                    let p = leaves(self, read, p);
                    self.write.alloc(p)
                })
            })
            .unwrap();
        Global::Value(value)
    }
    fn freeze_shared(&mut self, read: &TripleArena, node: &Shared) -> Global {
        match node {
            Shared::Async(mutex) => todo!(),
            Shared::Sync(sync_shared) => match &**sync_shared {
                SyncShared::Package(index, captures) => {
                    let package = self.maybe_freeze_package(read, index);
                    let global = self.freeze_shared(read, captures);
                    let global = self.write.alloc(global);
                    Global::Package(package, global, FanBehavior::Propagate)
                }
                SyncShared::Value(value) => Global::Value(
                    value
                        .map_ref_leaves(|shared| {
                            let global = self.freeze_shared(read, shared);
                            let global = self.write.alloc(global);
                            Some(global)
                        })
                        .unwrap(),
                ),
            },
        }
    }
    fn freeze_linear(&mut self, read: &TripleArena, node: &Linear) -> Global {
        match node {
            Linear::Value(value) => Global::Value(
                value
                    .map_ref_leaves(|node| {
                        Some({
                            let n = self.freeze_node(read, node);
                            self.write.alloc(n)
                        })
                    })
                    .unwrap(),
            ),
            Linear::Request(_) => panic!("attempted to freeze `Linear::Request`"),
            Linear::ShareHole(mutex) => {
                todo!(); // we still have to add them from the Shared side.
                let mut lock = mutex.lock().unwrap();
                let SharedHole::Unfilled(codes) = &mut *lock else {
                    unreachable!()
                };
                let codes: Vec<_> = codes.iter().map(|x| self.freeze_node(read, x)).collect();
                let codes = self.write.alloc_clone(codes.as_ref());
                Global::Fanout(codes)
            }
        }
    }
    pub fn freeze_global(
        &mut self,
        read: &TripleArena,
        instance: &Instance,
        node: &Global,
    ) -> Global {
        let global: Global = match node {
            Global::Variable(id) => {
                let node = instance.at(id, |slot| slot.take());
                if let Some(node) = node {
                    return self.freeze_node(read, &node);
                } else {
                    let addr = instance.identifier();
                    let id = self
                        .variable_map
                        .entry((addr, *id))
                        .and_modify(|(id, visited)| *visited = true)
                        .or_insert_with(|| {
                            let res = self.num_vars;
                            self.num_vars += 1;
                            (res, false)
                        })
                        .0;
                    Global::Variable(id)
                }
            }
            Global::Package(package, captures, fan_behavior) => {
                let captures = self.freeze_global(read, instance, read.get(*captures));
                let captures = self.write.alloc(captures);
                let package = self.maybe_freeze_package(read, package);
                Global::Package(package, captures, fan_behavior.clone())
            }
            Global::Destruct(global_cont) => match global_cont {
                GlobalCont::Continue => Global::Destruct(GlobalCont::Continue),
                GlobalCont::Par(a, b) => {
                    let a = self.freeze_global(read, instance, read.get(*a));
                    let b = self.freeze_global(read, instance, read.get(*b));
                    let a = self.write.alloc(a);
                    let b = self.write.alloc(b);
                    Global::Destruct(GlobalCont::Par(a, b))
                }
                GlobalCont::Choice(captures, branches) => {
                    let captures = self.freeze_global(read, instance, read.get(*captures));
                    let captures = self.write.alloc(captures);
                    let len = self.variable_map.len();

                    let branches: Vec<_> = read
                        .get(*branches)
                        .into_iter()
                        .map(|(name, package_body)| {
                            self.variable_map.truncate(len);
                            let name = self.intern(read, read.get(*name));
                            let root =
                                self.freeze_global(read, instance, read.get(package_body.root));
                            let root = self.write.alloc(root);
                            let captures =
                                self.freeze_global(read, instance, read.get(package_body.captures));
                            let captures = self.write.alloc(captures);
                            let redexes: Vec<_> = read
                                .get(package_body.redexes)
                                .iter()
                                .map(|(a, b)| {
                                    let a = self.freeze_global(read, instance, read.get(*a));
                                    let b = self.freeze_global(read, instance, read.get(*b));
                                    let a = self.write.alloc(a);
                                    let b = self.write.alloc(b);
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
                this.freeze_global(read, instance, global)
            }),
            Global::Fanout(index) => {
                let globs: Vec<_> = read
                    .get(*index)
                    .iter()
                    .map(|node| self.freeze_global(read, instance, node))
                    .collect();
                let globs = self.write.alloc_clone(globs.as_ref());
                Global::Fanout(globs)
            }
        };
        global
    }
    pub fn freeze_node(&mut self, read: &TripleArena, node: &Node) -> Global {
        match node {
            Node::Linear(linear) => self.freeze_linear(read, linear),
            Node::Shared(shared) => self.freeze_shared(read, shared),
            Node::Global(instance, index) => {
                let global = read.get(*index);
                self.freeze_global(read, instance, global)
            }
        }
    }
    pub fn maybe_freeze_global(
        &mut self,
        read: &TripleArena,
        instance: &Instance,
        node: &Index<Global>,
    ) -> Index<Global> {
        if node.0 < HIGHER_HALF {
            node.clone()
        } else {
            let node = self.freeze_global(read, instance, read.get(*node));
            self.write.alloc(node)
        }
    }
    pub fn maybe_freeze_redexes(
        &mut self,
        read: &TripleArena,
        instance: &Instance,
        redexes: &Index<[(Index<Global>, Index<Global>)]>,
    ) -> Index<[(Index<Global>, Index<Global>)]> {
        if redexes.0 .0 < HIGHER_HALF {
            redexes.clone()
        } else {
            let redexes: Vec<_> = redexes
                .into_iter()
                .map(|i| {
                    let (a, b) = read.get(i);
                    (
                        self.maybe_freeze_global(read, instance, a),
                        self.maybe_freeze_global(read, instance, b),
                    )
                })
                .collect();
            self.write.alloc_clone(redexes.as_ref())
        }
    }
    pub fn maybe_freeze_package(&mut self, read: &TripleArena, package: &PackagePtr) -> PackagePtr {
        if package.0 >= HIGHER_HALF {
            let mut child = Freezer::new(read, self.write);
            let package = read.get(package.clone()).as_ref().unwrap();
            let instance = Instance::from_num_vars(package.num_vars);

            let root = child.freeze_global(&read, &instance, read.get(package.body.root));
            let captures = child.freeze_global(&read, &instance, read.get(package.body.captures));
            let root = child.write.alloc(root);
            let captures = child.write.alloc(captures);
            let redexes: Vec<_> = read
                .get(package.body.redexes)
                .into_iter()
                .map(|(a, b)| {
                    let a = child.freeze_global(&read, &instance, read.get(*a));
                    let b = child.freeze_global(&read, &instance, read.get(*b));
                    let a = child.write.alloc(a);
                    let b = child.write.alloc(b);
                    (a, b)
                })
                .collect();
            let redexes = child.write.alloc_clone(redexes.as_ref());
            child.write.alloc(Some(Package {
                body: PackageBody {
                    root,
                    captures,
                    debug_name: package.body.debug_name.clone(),
                    redexes,
                },
                num_vars: child.num_vars,
            }))
        } else {
            package.clone()
        }
    }
    pub fn verify(&mut self) {
        if !self.variable_map.iter().all(|x| x.1 .1 == true) {
            for i in self.variable_map.iter().filter(|x| x.1 .1 == false) {
                eprintln!(
                    "Variable {} of {:x} is mapped to {}, but was only linked to once",
                    i.0 .1, i.0 .0, i.1 .0
                )
            }
            panic!("Net validatio failed: there are single-linked vars");
        }
    }
}
