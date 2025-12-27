// Direct compiler;
//
// Packages are created by:
// - Boxes
// - Definitions

use std::{
    collections::HashMap,
    fmt::Display,
    sync::{Arc, OnceLock},
};

use indexmap::IndexMap;
use tokio::time::Instant;

use crate::{
    location::Span,
    par::{
        language::{GlobalName, LocalName},
        process::{Captures, Command, Expression, Process, VariableUsage},
        program::{CheckedModule, Definition},
        types::{visit, Type, TypeDefs, TypeError},
    },
    runtime::{
        new::{
            arena::{Arena, Index, Indexable, TripleArena},
            freezer::Freezer,
            readback::Handle,
            reducer::{NetHandle, Reducer},
            runtime::{
                Global, GlobalCont, Instance, Linker, Node, Package, PackageBody, PackagePtr,
                Runtime, Value,
            },
            show::{Showable, Shower},
        },
        old::net::FanBehavior,
    },
};

pub type Result<T> = core::result::Result<T, String>;
macro_rules! err {
    ($($arg:tt)*) => {
        Err(format!($($arg)*))
    };
}

macro_rules! tdb {
    ($tab:expr, $fmt:expr, $($arg:tt)*) => {
        eprintln!(concat!("{}", $fmt), " ".repeat($tab * 4), $($arg)*)
    };
    ($tab:expr, $fmt:expr) => {
        eprintln!(concat!("{}", $fmt), " ".repeat($tab * 4))
    };
}
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Var {
    Name(LocalName),
    Loop(Option<LocalName>),
}

#[derive(Clone, Debug)]
pub struct VarState {
    value: Global,
    /// The list of destinations that will get plugged in to a fanout when the context is closed or the variable is moved out of.
    destinations: Vec<Global>,
}

#[derive(Default, Debug)]
pub struct Context {
    vars: HashMap<Var, VarState>,
}

impl Context {
    fn insert(&mut self, var: Var, global: Global) {
        self.vars.insert(
            var,
            VarState {
                value: global,
                destinations: vec![],
            },
        );
    }
}

#[derive(Default, Debug, Clone)]
pub struct PackData {
    names: Vec<Var>,
}

#[derive(Debug)]
pub struct PackageState {
    arena: Arena,
    context: Context,
    num_vars: usize,
    tab_level: usize,
    redexes: Vec<(Index<Global>, Index<Global>)>,
}

impl Default for PackageState {
    fn default() -> Self {
        Self {
            arena: Arena::higher_half(),
            context: Context::default(),
            num_vars: usize::default(),
            tab_level: usize::default(),
            redexes: Vec::default(),
        }
    }
}

impl PackageState {
    pub fn arena(&mut self) -> &mut Arena {
        &mut self.arena
    }
    pub fn multiplex_trees(&mut self, mut trees: Vec<Global>) -> Global {
        if trees.len() == 0 {
            Global::Value(Value::Break)
        } else if trees.len() == 1 {
            trees.pop().unwrap()
        } else {
            let new_trees = trees.split_off(trees.len() / 2);
            let (a, b) = (self.multiplex_trees(trees), self.multiplex_trees(new_trees));
            Global::Value(Value::Pair(self.arena().alloc(a), self.arena().alloc(b)))
        }
    }
    pub fn demultiplex_trees(&mut self, mut trees: Vec<Global>) -> Global {
        if trees.len() == 0 {
            Global::Destruct(GlobalCont::Continue)
        } else if trees.len() == 1 {
            trees.pop().unwrap()
        } else {
            let new_trees = trees.split_off(trees.len() / 2);
            let (a, b) = (self.multiplex_trees(trees), self.multiplex_trees(new_trees));
            Global::Destruct(GlobalCont::Par(
                self.arena().alloc(a),
                self.arena().alloc(b),
            ))
        }
    }
    fn capture(&mut self, captures: &Captures) -> Result<Context> {
        let mut target = Context::default();
        // TODO: somehow make this close less
        for (k, v) in self.context.vars.clone() {
            // either move, duplicate, or pass-through
            let do_captures = if let Var::Name(name) = &k {
                captures.contains(name)
            } else {
                true
            };
            let do_duplicate = if let Var::Name(name) = &k {
                matches!(captures.names.get(name), Some((_, VariableUsage::Copy)))
            } else {
                true
            };
            if do_captures && do_duplicate {
                let global = self.add_var_destination(&k)?;
                target.insert(k.clone(), global);
            } else if do_captures && !do_duplicate {
                let global = self.add_var_destination(&k)?;
                self.close_var(&k)?;
                target.insert(k.clone(), global);
            };
        }
        Ok(target)
    }
    fn pack_self(&mut self) -> (Global, PackData) {
        let cx = core::mem::take(&mut self.context);
        self.pack(cx)
    }
    fn pack(&mut self, mut context: Context) -> (Global, PackData) {
        let vars = core::mem::take(&mut context.vars);
        let mut pack_data = PackData::default();
        let mut trees = vec![];
        for (k, mut v) in vars {
            trees.push(self.add_var_destination_inplace(&mut v));
            self.close_var_inner(v);
            pack_data.names.push(k);
        }
        (self.multiplex_trees(trees), pack_data)
    }
    fn unpack_self(&mut self, global: Global, pack: &PackData) {
        self.context = self.unpack(global, pack)
    }
    fn unpack(&mut self, global: Global, pack: &PackData) -> Context {
        let mut context = Context::default();
        let mut trees = vec![];
        for var in &pack.names {
            let (a, b) = self.new_var();
            context.insert(var.clone(), a);
            trees.push(b);
        }
        let dest = self.demultiplex_trees(trees);
        self.link(global, dest);
        context
    }

    pub fn link(&mut self, a: Global, b: Global) {
        tdb!(self.tab_level + 1, "linking {:?} {:?}", &a, &b);
        let tup = (self.arena().alloc(a), self.arena().alloc(b));
        tdb!(self.tab_level + 2, "-> {:?}", tup);
        self.redexes.push(tup);
    }
    pub fn new_var(&mut self) -> (Global, Global) {
        let ret = (
            Global::Variable(self.num_vars),
            Global::Variable(self.num_vars),
        );
        self.num_vars += 1;
        ret
    }
    pub fn define_var(&mut self, name: Var) -> Global {
        let _ = self.close_var(&name);
        let (a, b) = self.new_var();
        self.context.insert(name, a);
        b
    }
    fn add_var_destination(&mut self, var: &Var) -> Result<Global> {
        let (a, b) = self.new_var();
        self.context
            .vars
            .get_mut(var)
            .expect(&format!("Couldn't find var {:?}", var))
            .destinations
            .push(a);
        Ok(b)
    }
    fn add_var_destination_inplace(&mut self, var: &mut VarState) -> Global {
        let (a, b) = self.new_var();
        var.destinations.push(a);
        b
    }
    fn close_var_inner(&mut self, mut var: VarState) {
        if var.destinations.len() == 1 {
            self.link(var.value, var.destinations.pop().unwrap());
        } else {
            let node = Global::Fanout(self.arena().alloc_clone(&var.destinations));
            self.link(var.value, node);
        }
    }
    fn close_var(&mut self, var: &Var) -> Result<()> {
        let var = self.context.vars.remove(var);
        if let Some(var) = var {
            self.close_var_inner(var);
        }
        Ok(())
    }
    fn close_all_vars(&mut self) {
        for var in core::mem::take(&mut self.context.vars).into_values() {
            self.close_var_inner(var);
        }
    }
    pub fn get_var(&mut self, var: &Var, usage: &VariableUsage) -> Result<Global> {
        if matches!(usage, VariableUsage::Copy) {
            Ok(self.add_var_destination(var)?)
        } else {
            let ret = self.add_var_destination(var)?;
            self.close_var(var)?;
            Ok(ret)
        }
    }
}

#[derive(Default)]
pub struct Compiler {
    permanent: Arena,
    current: Vec<PackageState>,
    type_defs: TypeDefs,
    definition_packages: HashMap<GlobalName, Index<OnceLock<Package>>>,
}

impl Compiler {
    pub fn enter(&mut self) {
        self.current().tab_level += 1;
    }
    pub fn exit(&mut self) {
        self.current().tab_level -= 1;
    }
    pub fn push_current(&mut self, num_vars: usize) {
        let tab_level = self.current.last_mut().map(|x| x.tab_level).unwrap_or(0);
        self.current.push(PackageState::default());
        self.current().num_vars = num_vars;
        self.current().tab_level = tab_level;
    }
    pub fn pop_current(&mut self) -> PackageState {
        let p = self.current.pop().unwrap();
        self.current().tab_level = p.tab_level;
        p
    }
    pub fn current(&mut self) -> &mut PackageState {
        self.current.last_mut().unwrap()
    }
    pub fn write_arena(&mut self) -> &mut Arena {
        self.current().arena()
    }
    pub fn read_arena(&self) -> &Arena {
        &self.permanent
    }
    pub fn intern(&mut self, s: &str) -> Index<str> {
        // TODO: This unnecessarily interns strings that are unused in the final net.
        self.permanent.intern(s)
    }
    pub fn empty_string(&self,) -> Index<str> {
        self.permanent.empty_string()
    }
    pub fn get<T: Indexable + ?Sized>(&self, index: Index<T>) -> &T {
        self.read_arena().get(index)
    }
    pub fn alloc<T: Indexable>(&mut self, data: T) -> Index<T> {
        self.write_arena().alloc(data)
    }
    pub fn alloc_clone<T: Indexable + ?Sized>(&mut self, data: &T) -> Index<T> {
        self.write_arena().alloc_clone(data)
    }

    fn compile_global_name(&mut self, global_name: &GlobalName) -> Global {
        let package = self
            .definition_packages
            .entry(global_name.clone())
            .or_insert_with(|| {
                self.current
                    .last_mut()
                    .unwrap()
                    .arena()
                    .alloc(OnceLock::<Package>::new())
            })
            .clone();

        let captures = self.alloc(Global::Value(Value::Break));
        let global = Global::Package(
            package,
            captures,
            crate::runtime::old::net::FanBehavior::Expand,
        );
        global
    }
    fn compile_command(
        &mut self,
        span: &Span,
        subject: &LocalName,
        usage: &VariableUsage,
        cmd: &Command<Type>,
    ) -> Result<()> {
        match cmd {
            Command::Link(expr) => {
                tdb!(self.current().tab_level, "link {}", subject);
                let var = self.current().get_var(&Var::Name(subject.clone()), usage)?;
                let expr = self.compile_expression(span, expr)?;
                self.current().link(var, expr);
                self.current().close_all_vars();
            }
            Command::Send(expr, proc) => {
                tdb!(self.current().tab_level, "send {}", subject);
                self.enter();
                let expr = self.compile_expression(span, expr)?;
                self.exit();
                let var = self.current().get_var(&Var::Name(subject.clone()), usage)?;
                let new = self.current().define_var(Var::Name(subject.clone()));
                let tgt = Global::Value(Value::Pair(self.alloc(new), self.alloc(expr)));
                self.current().link(var, tgt);
                self.compile_process(span, proc)?;
            }
            Command::Receive(local_name, _, _, proc, _) => {
                tdb!(self.current().tab_level, "recv {}", subject);
                let var = self.current().get_var(&Var::Name(subject.clone()), usage)?;
                let new = self.current().define_var(Var::Name(subject.clone()));
                let arg = self.current().define_var(Var::Name(local_name.clone()));
                let tgt = Global::Destruct(GlobalCont::Par(self.alloc(new), self.alloc(arg)));
                self.current().link(var, tgt);
                self.compile_process(span, proc)?;
            }
            Command::Signal(local_name, process) => {
                tdb!(self.current().tab_level, "signal {}", subject);
                let var = self.current().get_var(&Var::Name(subject.clone()), usage)?;
                let new = self.current().define_var(Var::Name(subject.clone()));
                let new = self.alloc(new);
                let tgt = Global::Value(Value::Either(
                    self.intern(&local_name.string.as_str()),
                    new,
                ));
                self.current().link(var, tgt);
                self.compile_process(span, process)?;
            }
            Command::Case(local_names, items, else_branch) => {
                tdb!(self.current().tab_level, "case {}", subject);
                let var = self
                    .current()
                    .get_var(&Var::Name(subject.clone()), &VariableUsage::Move)?;
                let (context, pack_data) = self.current().pack_self();
                let mut branches = vec![];
                let base_num_vars = self.current().num_vars;
                let mut max_num_vars = base_num_vars;
                for (name, proc) in local_names.iter().zip(items.iter()) {
                    tdb!(self.current().tab_level, "branch {}", name);
                    // TODO; this uses a different set of vars for each branch
                    // but this is not necessary
                    // and leads to increased compilation times
                    self.push_current(base_num_vars);
                    let name = self.intern(name.string.as_str());

                    let (c0, c1) = self.current().new_var();
                    self.current().unpack_self(c0, &pack_data);
                    let root = self.current().define_var(Var::Name(subject.clone()));

                    self.enter();
                    self.compile_process(span, proc)?;
                    self.exit();
                    let current = self.pop_current();
                    let package = self.finalize_package(current, root, c1, base_num_vars);
                    branches.push((name, package.body));
                    max_num_vars = max_num_vars.max(package.num_vars);
                    //self.pop_current();
                }
                if let Some(else_branch) = else_branch {
                    tdb!(self.current().tab_level, "else branch");
                    self.push_current(base_num_vars);
                    self.current().num_vars = base_num_vars;
                    let name = self.empty_string();

                    let (c0, c1) = self.current().new_var();
                    self.current().unpack_self(c0, &pack_data);
                    let root = self.current().define_var(Var::Name(subject.clone()));
                    self.enter();
                    self.compile_process(span, &else_branch)?;
                    self.exit();

                    let current = self.pop_current();
                    let package = self.finalize_package(current, root, c1, base_num_vars);
                    branches.push((name, package.body));
                    max_num_vars = max_num_vars.max(package.num_vars);
                    //self.pop_current();
                };
                self.current().num_vars = max_num_vars;
                let branches = self.alloc_clone(branches.as_ref());
                let context = self.alloc(context);
                self.current()
                    .link(var, Global::Destruct(GlobalCont::Choice(context, branches)));
            }
            Command::Break => {
                tdb!(self.current().tab_level, "break {}", subject);
                let var = self.current().get_var(&Var::Name(subject.clone()), usage)?;
                let tgt = Global::Value(Value::Break);
                self.current().link(var, tgt);
                self.current().close_all_vars();
            }
            Command::Continue(process) => {
                tdb!(self.current().tab_level, "continue {}", subject);
                let var = self.current().get_var(&Var::Name(subject.clone()), usage)?;
                let tgt = Global::Destruct(GlobalCont::Continue);
                self.current().link(var, tgt);
                self.compile_process(span, process)?;
            }
            Command::Begin {
                unfounded,
                label,
                captures,
                body,
            } => todo!(),
            Command::Loop(local_name, local_name1, captures) => todo!(),
            Command::SendType(_, process) => todo!(),
            Command::ReceiveType(local_name, process) => todo!(),
        }
        Ok(())
    }
    fn compile_process(&mut self, span: &Span, proc: &Process<Type>) -> Result<()> {
        match proc {
            Process::Let {
                span,
                name,
                annotation,
                typ,
                value,
                then,
            } => {
                tdb!(self.current().tab_level, "let {}", name);
                self.enter();
                let expr = self.compile_expression(span, &value)?;
                self.exit();
                self.current().context.insert(Var::Name(name.clone()), expr);
                self.compile_process(span, then)?;
            }
            Process::Do {
                span,
                name,
                usage,
                typ,
                command,
            } => {
                self.compile_command(span, name, usage, command)?;
            }
            Process::Telltypes(span, process) => todo!(),
            Process::Block(span, id, process, process1) => todo!(),
            Process::Goto(span, id, captures) => todo!(),
            Process::Unreachable(span) => todo!(),
        };
        Ok(())
    }
    fn compile_expression(&mut self, span: &Span, expr: &Expression<Type>) -> Result<Global> {
        match expr {
            Expression::Global(span, global_name, _) => {
                let global = self.compile_global_name(global_name);
                Ok(global)
            }
            Expression::Variable(span, local_name, _, variable_usage) => self
                .current()
                .get_var(&Var::Name(local_name.clone()), variable_usage),
            Expression::Box(span, captures, root, _) => {
                tdb!(self.current().tab_level, "box {:?}", captures);

                let child_context = self.current().capture(captures)?;
                let (captures_global, pack) = self.current().pack(child_context);
                let captures_global = self.alloc(captures_global);

                self.push_current(0);
                let (a, b) = self.current().new_var();
                self.current().unpack_self(a, &pack);
                let root = self.compile_expression(&span, &root)?;

                let current = self.pop_current();
                let package = self.finalize_package(current, root, b, 0);
                let package = OnceLock::from(package);
                let package = self.alloc(package);

                let global = Global::Package(package, captures_global, FanBehavior::Propagate);
                Ok(global)
            }
            Expression::Chan {
                span,
                captures,
                chan_name,
                chan_annotation,
                chan_type,
                expr_type,
                process,
            } => {
                tdb!(self.current().tab_level, "chan {}", chan_name);
                let child_context = self.current().capture(captures)?;
                let parent_context = core::mem::replace(&mut self.current().context, child_context);
                let created_chan = self.current().define_var(Var::Name(chan_name.clone()));
                self.enter();
                self.compile_process(span, &process)?;
                self.exit();
                self.current().context = parent_context;
                Ok(created_chan)
            }
            Expression::Primitive(span, primitive, _) => {
                Ok(Global::Value(Value::Primitive(primitive.clone())))
            }
            Expression::External(_, f, _) => Ok(Global::Value(Value::ExternalFn(*f))),
        }
    }
    fn finalize_package(
        &mut self,
        mut current: PackageState,
        root: Global,
        captures: Global,
        num_vars: usize,
    ) -> Package {
        current.close_all_vars();
        let num_vars = current.num_vars;
        let redexes = current.redexes;
        let arena = current.arena;
        let write_arena = self.permanent.postfix_arena();
        let arena = TripleArena {
            permanent: std::mem::take(&mut self.permanent),
            read: arena,
            write: write_arena,
        };
        let arena = Arc::new(arena);
        {
            let mut shower = Shower::from_arena(&arena);
            shower.deref_globals = true;
            println!("Package:\n\t{}", Showable(&root, &shower));
            println!("\t$ {}", Showable(&captures, &shower));
            for (a, b) in &redexes {
                println!("\t{} ~ {}", Showable(a, &shower), Showable(b, &shower));
            }
        }
        let mut runtime = Runtime::new(arena.clone());
        let instance = Instance::from_num_vars(num_vars);
        for (a, b) in redexes {
            runtime.link(
                Node::Global(instance.clone(), a),
                Node::Global(instance.clone(), b),
            );
        }
        let mut t = Instant::now();
        let redexes: Vec<_> = std::iter::from_fn(|| runtime.reduce())
            .map(|(a, b)| (Node::Linear(a.into()), b))
            .collect();
        println!(
            "Pre-reduction rewrites:\n{}",
            runtime.rewrites.show(t.elapsed())
        );
        drop(runtime);
        let mut arena = Arc::into_inner(arena).unwrap();
        let mut write = core::mem::take(&mut arena.write);
        let mut freezer = Freezer::new(&arena, &mut write);
        freezer.num_vars = num_vars;
        let root = freezer.freeze_global(&arena, &instance, &root);
        let captures = freezer.freeze_global(&arena, &instance, &captures);
        let redexes: Vec<_> = redexes
            .into_iter()
            .map(|(a, b)| {
                let a = freezer.freeze_node(&arena, &a);
                let b = freezer.freeze_node(&arena, &b);
                (a, b)
            })
            .collect();
        let redexes = freezer.write.alloc_clone(redexes.as_ref());
        // readback root, captures, and redexes into the arena
        // (now that it's pre-reduced)
        //
        // create a new package
        let package = Package {
            num_vars: freezer.num_vars,
            body: PackageBody {
                root,
                captures,
                debug_name: String::new(),
                redexes,
            },
        };
        let mut permanent = arena.permanent;
        permanent.append(&mut write);
        self.permanent = permanent;
        package
    }
    fn compile_definitions(
        &mut self,
        definitions: &IndexMap<GlobalName, (Definition<Arc<Expression<Type>>>, Type)>,
    ) -> Result<()> {
        for (k, (v, _type)) in definitions.iter() {
            let p = self.permanent.alloc(OnceLock::new());
            self.definition_packages.insert(k.clone(), p);
        }
        for (k, (v, _type)) in definitions.iter() {
            self.push_current(0);
            let root = self.compile_expression(&v.span, &v.expression)?;
            let current = self.pop_current();
            let package =
                self.finalize_package(current, root, Global::Destruct(GlobalCont::Continue), 0);
            let package_destination = self.definition_packages.get(k).unwrap();
            self.get(*package_destination).set(package).unwrap();
        }
        Ok(())
    }
}

fn compile_file(program: &CheckedModule) -> Result<Compiler> {
    let mut compiler = Compiler::default();
    compiler.push_current(0);
    compiler.compile_definitions(&program.definitions)?;
    Ok(compiler)
}

#[derive(Clone)]
pub struct Compiled {
    pub arena: Arc<Arena>,
    pub name_to_package: HashMap<GlobalName, PackagePtr>,
    pub type_defs: TypeDefs,
}

impl Display for Compiled {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.arena)
    }
}

impl Compiled {
    pub fn compile_file(
        module: &crate::par::program::CheckedModule,
    ) -> core::result::Result<Self, crate::runtime::RuntimeCompilerError> {
        let type_defs = module.type_defs.clone();
        let mut compiler = compile_file(module).unwrap();
        let mut arena = compiler.permanent;
        let mut closure = |ty: &Type| {
            fn helper(
                ty: &Type,
                defs: &TypeDefs,
                arena: &mut Arena,
            ) -> std::result::Result<(), TypeError> {
                match ty {
                    Type::Either(_, variants) | Type::Choice(_, variants) => {
                        for k in variants.keys() {
                            arena.intern(k.string.as_str());
                        }
                    }
                    _ => {}
                }
                visit::continue_deref(&ty, defs, |ty: &Type| helper(ty, &defs, arena))
            }
            helper(ty, &type_defs, &mut arena)
        };
        for (_, _, ty) in type_defs.clone().globals.values() {
            closure(ty).unwrap();
        }

        println!("Code:\n{}\n// END CODE", arena);

        Ok(Self {
            arena: Arc::new(arena),
            type_defs,
            name_to_package: compiler.definition_packages,
        })
    }

    pub fn get_with_name(&self, name: &GlobalName) -> Option<PackagePtr> {
        Some(self.name_to_package.get(name).cloned()?)
    }

    pub fn new_runtime(&self) -> Runtime<Arc<Arena>> {
        Runtime::from(self.arena.clone())
    }
    pub fn new_reducer(&self) -> Reducer {
        Reducer::from(Runtime::from(self.arena.clone()))
    }
    pub async fn instantiate(&self, handle: NetHandle, name: &GlobalName) -> Option<Handle> {
        let package = self.get_with_name(name)?;
        Handle::from_package(self.arena.clone(), handle, package)
            .await
            .ok()
    }
}
