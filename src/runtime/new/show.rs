use std::cell::RefCell;
use std::fmt::Display;

use crate::runtime::new::arena::ArenaLike;
use crate::runtime::new::runtime::{
    Global, GlobalPtr, Instance, Linear, Node, PackageBody, Shared, SyncShared, Value,
};

pub struct Shower<'a, A: ArenaLike> {
    pub arena: &'a A,
    pub deref_globals: bool,
    pub depth: RefCell<usize>,
}

impl<'a, A: ArenaLike> Shower<'a, A> {
    pub fn from_arena(arena: &'a A) -> Self {
        Self {
            arena,
            deref_globals: true,
            depth: RefCell::new(0),
        }
    }
}

pub struct Showable<'a, 'b, P, A: ArenaLike>(pub P, pub &'b Shower<'a, A>);
//pub struct ShowableGlobal<'a, 'b>(&'a Instance, &'a Global, &'b mut Shower<'a>);

impl<'a, 'b, A: ArenaLike> std::fmt::Display for Showable<'a, 'b, &'a Node, A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0 {
            Node::Linear(linear) => write!(f, "-{}", Showable(linear, self.1)),
            Node::Shared(shared) => write!(f, "&{}", Showable(shared, self.1)),
            Node::Global(i, global) => write!(
                f,
                "{:x}'{}",
                (i.identifier() >> 3) & 0xFF,
                Showable(global, self.1)
            ),
        }
    }
}

impl<'a, 'b, A: ArenaLike> std::fmt::Display for Showable<'a, 'b, &'a Box<Node>, A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Showable(self.0.as_ref(), self.1).fmt(f)
    }
}

impl<'a, 'b, A: ArenaLike> std::fmt::Display for Showable<'a, 'b, &'a Linear, A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0 {
            Linear::Value(value) => {
                write!(f, "{}", Showable(value, self.1))?;
            }
            Linear::Request(_sender) => {
                write!(f, "<external request>")?;
            }
            Linear::ShareHole(mutex) => {
                if let Ok(lock) = mutex.try_lock() {
                    match &*lock {
                        crate::runtime::new::runtime::SharedHole::Filled(_sync_shared) => {
                            write!(f, "<unexpected filled share hole>")?;
                        }
                        crate::runtime::new::runtime::SharedHole::Unfilled(_nodes) => {
                            write!(f, "<unfilled hole>")?;
                        }
                    }
                } else {
                    write!(f, "<locked>")?;
                }
            }
        }
        Ok(())
    }
}

impl<'a, 'b, A: ArenaLike> std::fmt::Display for Showable<'a, 'b, &'a Shared, A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0 {
            Shared::Async(mutex) => {
                if let Ok(lock) = mutex.try_lock() {
                    match &*lock {
                        crate::runtime::new::runtime::SharedHole::Filled(sync_shared) => {
                            write!(f, "{}", Showable(sync_shared, self.1))?;
                        }
                        crate::runtime::new::runtime::SharedHole::Unfilled(_) => {
                            write!(f, "<waiting>")?;
                        }
                    }
                } else {
                    write!(f, "<locked>")?;
                }
            }
            Shared::Sync(sync_shared) => {
                write!(f, "{}", Showable(sync_shared.as_ref(), self.1))?;
            }
        };
        Ok(())
    }
}
impl<'a, 'b, A: ArenaLike> std::fmt::Display for Showable<'a, 'b, &'a SyncShared, A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0 {
            SyncShared::Package(index, shared) => {
                write!(f, "@{}${}", index.0, Showable(shared, self.1))?;
            }
            SyncShared::Value(value) => {
                write!(f, "{}", Showable(value, self.1))?;
            }
        };
        Ok(())
    }
}

impl<'a, 'b, A: ArenaLike> std::fmt::Display for Showable<'a, 'b, &'a Global, A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0 {
            Global::Variable(id) => {
                write!(f, "{}", id)?;
            }
            Global::Package(index, captures, _) => {
                write!(f, "@{}${}", index.0, Showable(captures, self.1))?;
            }
            Global::Fanout(index) => {
                write!(f, "{{")?;
                for i in self.1.arena.get(index.clone()) {
                    write!(f, "{} ", Showable(i, self.1))?;
                }
                write!(f, "}}")?;
            }
            Global::Destruct(global_cont) => {
                use crate::runtime::new::runtime::GlobalCont::*;
                match global_cont {
                    Continue => write!(f, "?")?,
                    Par(a, b) => {
                        write!(f, "[{}] {}", Showable(b, self.1), Showable(a, self.1))?;
                    }
                    Choice(captures, branches) => {
                        write!(f, ".{{\n")?;
                        const TAB: &'static str = "    ";
                        let prefix = TAB.repeat(*self.1.depth.borrow());
                        for (k, v) in self.1.arena.get(branches.clone()).iter() {
                            write!(
                                f,
                                "{prefix}{} => {}\n",
                                self.1.arena.get(k.clone()),
                                Showable(v, self.1)
                            )?;
                        }
                        write!(f, "{prefix}}}${}", Showable(captures, self.1))?;
                    }
                }
            }
            Global::Value(value) => {
                write!(f, "{}", Showable(value, self.1))?;
            }
        };
        Ok(())
    }
}

impl<'a, 'b, A: ArenaLike> std::fmt::Display for Showable<'a, 'b, &'a GlobalPtr, A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.1.deref_globals {
            write!(f, "{}", Showable(self.1.arena.get(self.0.clone()), self.1))?;
        } else {
            write!(f, "{}", self.0 .0)?;
        }
        Ok(())
    }
}

impl<'a, 'b, P, A: ArenaLike> std::fmt::Display for Showable<'a, 'b, &'a Value<P>, A>
where
    Showable<'a, 'b, &'a P, A>: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use crate::runtime::new::runtime::Value::*;
        match self.0 {
            Break => write!(f, "!")?,
            Pair(a, b) => {
                write!(f, "({}) {}", Showable(b, self.1), Showable(a, self.1))?;
            }
            Either(arc_str, payload) => {
                write!(
                    f,
                    ".{} {}",
                    self.1.arena.get(arc_str.clone()),
                    Showable(payload, self.1)
                )?;
            }
            ExternalFn(_) => {
                write!(f, "<external fn>")?;
            }
            ExternalArc(_) => {
                write!(f, "<external arc>")?;
            }
            Primitive(primitive) => {
                write!(f, "#{:?}", primitive)?;
            }
        };
        Ok(())
    }
}

use super::runtime::Package;
use std::sync::OnceLock;

impl<'a, 'b, A: ArenaLike> std::fmt::Display for Showable<'a, 'b, &'a OnceLock<Package>, A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let package = self.0;

        let Some(lock) = package.get() else {
            write!(f, "<unfilled>")?;
            return Ok(());
        };
        write!(f, "{}", Showable(&lock.body, self.1))?;
        Ok(())
    }
}

impl<'a, 'b, A: ArenaLike> std::fmt::Display for Showable<'a, 'b, &'a PackageBody, A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        const TAB: &'static str = "    ";
        let prefix = TAB.repeat(*self.1.depth.borrow());
        *self.1.depth.borrow_mut() += 1;
        let package = self.0;
        if package.debug_name.len() > 0 {
            write!(f, "{prefix}/* {} */\n", package.debug_name)?;
        }
        write!(f, "{prefix}@{}\n", Showable(&package.root, self.1))?;
        write!(f, "{prefix}{TAB}${}\n", Showable(&package.captures, self.1))?;
        for (a, b) in self.1.arena.get(package.redexes.clone()) {
            write!(
                f,
                "{prefix}{TAB}& {}\n{prefix}{TAB}~ {}",
                Showable(a, self.1),
                Showable(b, &self.1)
            )?;
        }
        *self.1.depth.borrow_mut() -= 1;
        Ok(())
    }
}

impl<'a, 'b, A: ArenaLike> std::fmt::Display for Showable<'a, 'b, &'a Instance, A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let id = self.0.identifier();
        match self.0.vars.0.try_lock() {
            Ok(lock) => {
                write!(f, "Instance@{:x} {{", (id >> 3) & 0xFF)?;
                for (k, v) in lock.iter().enumerate() {
                    if let Some(v) = v {
                        write!(f, "{}: {}, ", k, Showable(v, &self.1))?;
                    }
                }
                write!(f, "}}")?;
                Ok(())
            }
            Err(_) => {
                write!(f, "<locked>")?;
                Ok(())
            }
        }
    }
}
