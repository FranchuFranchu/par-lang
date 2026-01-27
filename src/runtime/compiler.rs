use futures::{future::RemoteHandle, task::SpawnExt};
use indexmap::IndexSet;

use crate::{
    location::Span,
    par::{
        language::{GlobalName, LocalName},
        types::Type,
    },
    runtime::{
        flat::{
            self,
            compiler::{Compiled as V3Compiled, Var},
            stats::Rewrites,
        },
        readback::Handle,
    },
};
use std::collections::HashMap;

use std::fmt::Display;

#[derive(Clone, Debug)]
pub enum RuntimeCompilerError {
    /// Error that is emitted when a variable that was never bound/captured is used
    UnboundVar(Span, #[allow(unused)] Var),
    /// Error that is emitted when it is unclear how a variable is used (move/copy)
    UnknownVariableUsage(Span),
    GlobalNotFound(GlobalName),
    DependencyCycle {
        global: GlobalName,
        dependents: IndexSet<GlobalName>,
    },
    UnguardedLoop(Span, #[allow(unused)] Option<LocalName>),
}

impl RuntimeCompilerError {
    pub fn display(&self, _code: &str) -> String {
        "inet compilation error".to_string()
        //TODO: fix error messages
        /*match self {
            Error::UnboundVar(loc) => format!("Unbound variable\n{}", loc.display(code)),
            Error::UnusedVar(loc) => format!("Unused variable\n{}", loc.display(code)),
            Error::UnexpectedType(loc, ty) => {
                format!("Unexpected type: {:?}\n{}", ty, loc.display(code),)
            }
            Error::GlobalNotFound(name) => format!("Global not found: {:?}", name),
            Error::DependencyCycle { global, dependents } => format!(
                "Dependency cycle detected for global {:?} with dependents {:?}",
                global, dependents
            ),
            Error::UnguardedLoop(loc, name) => format!(
                "Unguarded loop with label {:?} at\n{}",
                name,
                loc.display(code)
            ),
        }*/
    }

    pub fn spans(&self) -> (Span, Vec<Span>) {
        use crate::location::Spanning;
        match self {
            Self::UnboundVar(span, _)
            | Self::UnknownVariableUsage(span)
            | Self::UnguardedLoop(span, _) => (span.clone(), vec![]),

            Self::GlobalNotFound(name) => (name.span(), vec![]),

            Self::DependencyCycle { global, dependents } => (
                global.span(),
                dependents.iter().map(|name| name.span()).collect(),
            ),
        }
    }
}

#[derive(Clone)]
pub struct Compiled {
    pub code: V3Compiled,
    pub name_to_ty: HashMap<GlobalName, Type>,
}

impl Display for Compiled {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.code.fmt(f)
    }
}

impl Compiled {
    pub fn compile_file(
        module: &crate::par::program::CheckedModule,
    ) -> Result<Self, RuntimeCompilerError> {
        Ok(Self {
            code: V3Compiled::compile_file(module)?,
            name_to_ty: module
                .definitions
                .iter()
                .map(|(a, (_, typ))| (a.clone(), typ.clone()))
                .collect(),
        })
    }
    pub fn get_type_of(&self, name: &GlobalName) -> Option<Type> {
        self.name_to_ty.get(name).cloned()
    }
    pub async fn start_and_instantiate(
        &self,
        name: &GlobalName,
    ) -> (Handle, RemoteHandle<Rewrites>) {
        let mut reducer = self.code.new_reducer();
        let net_handle = reducer.net_handle().clone();
        let spawner = reducer.spawner();
        let reducer_future = reducer.spawn_reducer();
        (
            Handle::from(self.code.instantiate(net_handle, name).unwrap()),
            spawner
                .spawn_with_handle(async move {
                    let reducer = reducer_future.await;
                    reducer.runtime.rewrites
                })
                .unwrap(),
        )
    }
}
