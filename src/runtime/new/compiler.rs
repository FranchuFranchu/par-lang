// Direct compiler;
//
// Packages are created by:
// - Boxes
// - Definitions

use std::{
    cell::OnceCell,
    collections::{BTreeSet, HashMap},
    sync::{Arc, OnceLock},
};

use indexmap::IndexMap;

use crate::{
    location::Span,
    par::{
        language::{GlobalName, LocalName},
        process::{Captures, Command, Expression, Process, VariableUsage},
        program::{CheckedModule, Definition},
        types::{Type, TypeDefs},
    },
    runtime::{
        new::{
            arena::{Index, TripleArena},
            runtime::{
                Global, GlobalCont, Instance, Linker, Node, Package, PackagePtr, Runtime, Value,
            },
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

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Var {
    Name(LocalName),
    Loop(Option<LocalName>),
}

#[derive(Clone)]
pub struct VarState {
    value: Global,
    /// The list of destinations that will get plugged in to a fanout when the context is closed or the variable is moved out of.
    destinations: Vec<Global>,
}

#[derive(Default)]
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

#[derive(Default)]
pub struct PackData {
    names: Vec<Var>,
}

#[derive(Default)]
pub struct PackageState {
    context: Context,
    num_vars: usize,
    arena: TripleArena,
    redexes: Vec<(Index<Global>, Index<Global>)>,
}

impl PackageState {
    pub fn multiplex_trees(&mut self, mut trees: Vec<Global>) -> Global {
        if trees.len() == 0 {
            Global::Value(Value::Break)
        } else if trees.len() == 1 {
            trees.pop().unwrap()
        } else {
            let new_trees = trees.split_off(trees.len() / 2);
            let (a, b) = (self.multiplex_trees(trees), self.multiplex_trees(new_trees));
            Global::Value(Value::Pair(self.arena.alloc(a), self.arena.alloc(b)))
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
            Global::Destruct(GlobalCont::Par(self.arena.alloc(a), self.arena.alloc(b)))
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
                self.close_var(&k);
                target.insert(k.clone(), global);
            };
        }
        Ok(target)
    }
    fn pack(&mut self) -> (Global, PackData) {
        let vars = core::mem::take(&mut self.context.vars);
        let mut pack_data = PackData::default();
        let mut trees = vec![];
        for (k, mut v) in vars {
            trees.push(self.add_var_destination_inplace(&mut v));
            self.close_var_inner(v);
            pack_data.names.push(k);
        }
        (self.multiplex_trees(trees), pack_data)
    }
    fn unpack(&mut self, global: Global, pack: PackData) -> Context {
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
    fn set_context(&mut self, context: Context) {
        self.context = context;
    }

    pub fn link(&mut self, a: Global, b: Global) {
        self.redexes
            .push((self.arena.alloc(a), self.arena.alloc(b)));
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
        let (a, b) = self.new_var();
        self.context.insert(name, a);
        b
    }
    fn add_var_destination(&mut self, var: &Var) -> Result<Global> {
        let (a, b) = self.new_var();
        self.context
            .vars
            .get_mut(var)
            .ok_or(format!("Couldn't find var {:?}", var))?
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
            let node = Global::Fanout(self.arena.alloc_clone(&var.destinations));
            self.link(var.value, node);
        }
    }
    fn close_var(&mut self, var: &Var) -> Result<()> {
        let mut var = self
            .context
            .vars
            .remove(var)
            .ok_or(format!("Couldn't find var {:?}", var))?;
        self.close_var_inner(var);
        Ok(())
    }
    fn finalize(&mut self) -> (usize, Vec<(Index<Global>, Index<Global>)>) {
        for (name, var) in core::mem::take(&mut self.context.vars) {
            self.close_var_inner(var);
        }
        (
            core::mem::replace(&mut self.num_vars, 0),
            core::mem::take(&mut self.redexes),
        )
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

type CompileBox = (PackagePtr, Span, PackData, Arc<Expression<Type>>);

#[derive(Default)]
pub struct Compiler {
    current: PackageState,
    box_queue: Vec<CompileBox>,
    type_defs: TypeDefs,
    definition_packages: HashMap<GlobalName, Index<OnceLock<Package>>>,
}

impl Compiler {
    fn compile_global_name(&mut self, global_name: &GlobalName) -> Global {
        let package = self
            .definition_packages
            .entry(global_name.clone())
            .or_insert_with(|| self.current.arena.alloc(OnceLock::<Package>::new()))
            .clone();

        let captures = self.current.arena.alloc(Global::Value(Value::Break));
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
            Command::Link(expression) => todo!(),
            Command::Send(expression, process) => todo!(),
            Command::Receive(local_name, _, _, process, local_names) => todo!(),
            Command::Signal(local_name, process) => todo!(),
            Command::Case(local_names, items, process) => todo!(),
            Command::Break => todo!(),
            Command::Continue(process) => todo!(),
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
                let expr = self.compile_expression(span, &value)?;
                self.current.context.insert(Var::Name(name.clone()), expr);
                self.compile_process(span, then)?;
                Ok(())
            }
            Process::Do {
                span,
                name,
                usage,
                typ,
                command,
            } => {
                self.compile_command(span, name, usage, command)?;
                Ok(())
            }
            Process::Telltypes(span, process) => todo!(),
            Process::Block(span, id, process, process1) => todo!(),
            Process::Goto(span, id, captures) => todo!(),
            Process::Unreachable(span) => todo!(),
        }
    }
    fn compile_expression(&mut self, span: &Span, expr: &Expression<Type>) -> Result<Global> {
        match expr {
            Expression::Global(span, global_name, _) => {
                let global = self.compile_global_name(global_name);
                Ok(global)
            }
            Expression::Variable(span, local_name, _, variable_usage) => self
                .current
                .get_var(&Var::Name(local_name.clone()), variable_usage),
            Expression::Box(span, captures, expression, _) => {
                let box_package = self.current.arena.alloc(OnceLock::new());

                let child_context = self.current.capture(captures)?;
                let parent_context = core::mem::replace(&mut self.current.context, child_context);
                let (captures_global, pack_data) = self.current.pack();
                self.current.context = parent_context;
                let captures_global = self.current.arena.alloc(captures_global);

                self.box_queue.push((
                    box_package.clone(),
                    span.clone(),
                    pack_data,
                    expression.clone(),
                ));
                let global = Global::Package(box_package, captures_global, FanBehavior::Propagate);
                // Pass the captures to the queue
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
                let child_context = self.current.capture(captures)?;
                let parent_context = core::mem::replace(&mut self.current.context, child_context);
                let created_chan = self.current.define_var(Var::Name(chan_name.clone()));
                self.compile_process(span, &process)?;
                let (captures_global, pack_data) = self.current.pack();
                self.current.context = parent_context;
                Ok(created_chan)
            }
            Expression::Primitive(span, primitive, _) => todo!(),
            Expression::External(_, _, _) => todo!(),
        }
    }
    fn finalize_package(&mut self, root: Global, captures: Global) {
        let (num_vars, redexes) = self.current.finalize();
        self.current.arena.flush_to_temporary();
        let arena = Arc::new(core::mem::take(&mut self.current.arena));
        let mut runtime = Runtime::new(arena.clone());
        let mut instance = Instance::from_num_vars(self.current.num_vars);
        for (a, b) in redexes {
            runtime.link(
                Node::Global(instance.clone(), a),
                Node::Global(instance.clone(), b),
            );
        }
        let mut redexes: Vec<_> = std::iter::from_fn(|| runtime.reduce())
            .map(|(a, b)| (Node::Linear(a.into()), b))
            .collect();
        drop(runtime);
        let arena = Arc::into_inner(arena).unwrap();

        // readback root, captures, and redexes into the arena
        // (now that it's pre-reduced)
        //
        // create a new package
    }
    fn compile_definitions(
        &mut self,
        definitions: &IndexMap<GlobalName, (Definition<Arc<Expression<Type>>>, Type)>,
    ) -> Result<()> {
        for (k, (v, t)) in definitions.iter() {
            let root = self.compile_expression(&v.span, &v.expression)?;
            self.finalize_package(root, Global::Destruct(GlobalCont::Continue));
        }
        while let Some((package, span, pack, root)) = self.box_queue.pop() {
            let (a, b) = self.current.new_var();
            let context = self.current.unpack(a, pack);
            self.current.context = context;
        }
        Ok(())
    }
}

pub fn compile_file(program: &CheckedModule) -> Result<()> {
    let mut compiler = Compiler::default();
    compiler.compile_definitions(&program.definitions)?;
    Ok(())
}
