pub mod flat;
pub mod tree;
pub use compiler::Compiled;
pub use readback::Handle;
pub use tree::compiler::Error as RuntimeCompilerError;

pub mod compiler;
pub mod readback;

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
/// The behavior of a `Package` node when it interacts
/// with a fan node (duplicate or erase)
pub enum FanBehavior {
    /// Expand the package and then duplicate/erase it
    /// Used for side-effectful and top level packages
    Expand,
    /// Propagate the fan operator through the captures
    /// Used in boxes.
    Propagate,
}
