use std::collections::{BTreeMap, HashMap};
use std::fmt::Debug;
use std::sync::OnceLock;

use crate::runtime::new::{
    runtime::PackageBody,
    show::{Showable, Shower},
};

use super::runtime::{Global, Package};

#[derive(Debug)]
struct ArenaSlots<T> {
    inner: Vec<T>,
    start: usize,
    intern: HashMap<usize, T>,
}

impl<T> Default for ArenaSlots<T> {
    fn default() -> Self {
        Self {
            inner: vec![],
            start: 0,
            intern: HashMap::new(),
        }
    }
}
impl<T> ArenaSlots<T> {
    fn memory_usage(&self) -> usize {
        size_of::<T>() * self.inner.len()
    }
    fn get_one(&self, index: usize) -> &T {
        &self.inner[index - self.start]
    }
    fn get_slice(&self, index: usize, length: usize) -> &[T] {
        &self.inner[index - self.start..index - self.start + length]
    }
    fn alloc_one(&mut self, data: T) -> usize {
        let index = self.inner.len() + self.start;
        self.inner.push(data);
        index
    }
    fn alloc_slice(&mut self, data: &[T]) -> (usize, usize)
    where
        T: Clone,
    {
        let index = self.inner.len() + self.start;
        let len = data.len();
        self.inner.extend_from_slice(data);
        (index, len)
    }
    fn end_index(&self) -> usize {
        self.start + self.inner.len()
    }
    fn with_start(start: usize) -> Self {
        Self {
            start,
            ..Default::default()
        }
    }
    fn append(&mut self, other: &mut ArenaSlots<T>)
    where
        T: Debug,
    {
        assert!(other.start == self.end_index());
        self.inner.append(&mut other.inner);
        self.intern
            .extend(core::mem::take(&mut other.intern).into_iter());
    }
    fn contains(&self, index: usize) -> bool {
        (self.start..self.end_index()).contains(&index)
    }
    fn contains_range(&self, index: usize, len: usize) -> bool {
        self.contains(index) && (len == 0 || self.contains(index + len - 1))
    }
}

#[derive(Default)]
/// The `Arena` is a store for values from a finite set of types,
/// and returns indices into the arena. Allocation is done using [`Arena::alloc`],
/// and values can be accessed later with [`Arena::get`]
pub struct Arena {
    nodes: ArenaSlots<Global>,
    packages: ArenaSlots<OnceLock<Package>>,
    redexes: ArenaSlots<(Index<Global>, Index<Global>)>,
    case_branches: ArenaSlots<(Index<str>, PackageBody)>,

    strings_start: usize,
    strings: String,
    strings_intern: BTreeMap<String, Index<str>>,
}

type ArenaTrim = (usize, usize, usize, usize, usize);

impl Arena {
    fn slots_end_indices(&self) -> ArenaTrim {
        (
            self.nodes.end_index(),
            self.packages.end_index(),
            self.redexes.end_index(),
            self.case_branches.end_index(),
            self.strings_start + self.strings.len(),
        )
    }
    fn initialize_with_slot_start(
        (nodes, packages, redexes, case_branches, strings): ArenaTrim,
    ) -> Self {
        Arena {
            nodes: ArenaSlots::with_start(nodes),
            packages: ArenaSlots::with_start(packages),
            redexes: ArenaSlots::with_start(redexes),
            case_branches: ArenaSlots::with_start(case_branches),
            strings_start: strings,
            ..Default::default()
        }
    }

    fn append(&mut self, other: &mut Arena) {
        self.nodes.append(&mut other.nodes);
        self.packages.append(&mut other.packages);
        self.redexes.append(&mut other.redexes);
        self.case_branches.append(&mut other.case_branches);
        // TODO append strings
    }
    fn postfix_arena(&self) -> Arena {
        Self::initialize_with_slot_start(self.slots_end_indices())
    }

    /// Get a reference
    pub fn get<T: Indexable + ?Sized>(&self, index: Index<T>) -> &T {
        T::get(self, index)
    }
    pub fn alloc<T: Indexable>(&mut self, data: T) -> Index<T> {
        T::alloc(self, data)
    }
    pub fn alloc_clone<T: Indexable + ?Sized>(&mut self, data: &T) -> Index<T> {
        T::alloc_clone(self, data)
    }
    pub fn contains<T: Indexable + ?Sized>(&self, index: Index<T>) -> bool {
        T::contains(self, index)
    }
    pub fn memory_size(&self) -> usize {
        self.nodes.memory_usage()
            + self.packages.memory_usage()
            + self.redexes.memory_usage()
            + self.case_branches.memory_usage()
            + self.strings.len()
    }
    pub fn empty_string(&self) -> Index<str> {
        Index((0, 0))
    }
    pub fn intern(&mut self, s: &str) -> Index<str> {
        if s.is_empty() {
            self.empty_string()
        } else if let Some(s) = self.strings_intern.get(s) {
            s.clone()
        } else {
            let i = self.alloc_clone(s);
            self.strings_intern.insert(s.to_string(), i.clone());
            i
        }
    }
    pub fn interned(&self, s: &str) -> Option<Index<str>> {
        if s.is_empty() {
            Some(self.empty_string())
        } else {
            self.strings_intern.get(s).cloned()
        }
    }
}

impl std::fmt::Display for Arena {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let shower = Shower::from_arena(&self);
        for (idx, package) in self.packages.inner.iter().enumerate() {
            let Some(lock) = package.get() else {
                write!(f, "@{} = <unfilled>\n", idx)?;
                continue;
            };
            let lock = &lock.body;
            if lock.debug_name.len() > 0 {
                write!(f, "// {}\n", lock.debug_name)?;
            }
            write!(f, "@{} = {}", idx, Showable(&lock.root, &shower))?;
            write!(f, "\n    $ {}", Showable(&lock.captures, &shower))?;
            for (a, b) in self.get(lock.redexes.clone()) {
                write!(
                    f,
                    "\n     {} ~ {}",
                    Showable(a, &shower),
                    Showable(b, &shower)
                )?;
            }
            write!(f, "\n")?;
        }
        Ok(())
    }
}

pub struct Index<T: Indexable + ?Sized>(pub T::Store);

impl<T: Indexable + ?Sized> Copy for Index<T> {}

/// The `Indexable` trait is implemented by all types that are contained by an `Arena`.
/// It defines a [`Indexable::Store`] associated type, which determines what is needed to
/// index into a value of this type. For example, sized values usually require a `usize` to index them,
/// which represents the offset into the array that contains it
/// but a slice type requires a pair of offset and length.
pub trait Indexable {
    type Store: Copy + PartialEq + Eq + PartialOrd + Ord;
    fn get<'s>(store: &'s Arena, index: Index<Self>) -> &'s Self;
    fn contains<'s>(store: &'s Arena, index: Index<Self>) -> bool;
    fn alloc<'s>(store: &'s mut Arena, data: Self) -> Index<Self>
    where
        Self: Sized;
    fn alloc_clone<'s>(_: &'s mut Arena, _: &Self) -> Index<Self> {
        todo!() //Self::alloc(data.clone())
    }
}

macro_rules! slice_indexable {
    ($field:ident, $element:ty) => {
        impl Indexable for [$element] {
            type Store = (usize, usize);
            fn get<'s>(store: &'s Arena, index: Index<Self>) -> &'s Self {
                store.$field.get_slice(index.0 .0, index.0 .1)
            }
            fn alloc_clone<'s>(store: &'s mut Arena, data: &Self) -> Index<Self> {
                Index(store.$field.alloc_slice(data))
            }
            fn contains<'s>(store: &'s Arena, index: Index<Self>) -> bool {
                store.$field.contains_range(index.0 .0, index.0 .1)
            }
        }
        impl Iterator for Index<[$element]> {
            type Item = Index<$element>;
            fn next(&mut self) -> Option<Index<$element>> {
                if self.0 .1 == 0 {
                    None
                } else {
                    let ret = Index(self.0 .0);
                    self.0 .0 += 1;
                    self.0 .1 -= 1;
                    Some(ret)
                }
            }
        }
    };
}
macro_rules! sized_indexable {
    ($field:ident, $element:ty) => {
        impl Indexable for $element {
            type Store = usize;
            fn get<'s>(store: &'s Arena, index: Index<Self>) -> &'s Self {
                &store.$field.get_one(index.0)
            }
            fn alloc<'s>(store: &'s mut Arena, data: Self) -> Index<Self> {
                Index(store.$field.alloc_one(data))
            }
            fn contains<'s>(store: &'s Arena, index: Index<Self>) -> bool {
                store.$field.contains(index.0)
            }
        }
    };
}
slice_indexable!(case_branches, (Index<str>, PackageBody));
slice_indexable!(nodes, Global);
slice_indexable!(redexes, (Index<Global>, Index<Global>));
sized_indexable!(redexes, (Index<Global>, Index<Global>));
sized_indexable!(case_branches, (Index<str>, PackageBody));
sized_indexable!(packages, OnceLock<Package>);
sized_indexable!(nodes, Global);

impl Indexable for str {
    type Store = (usize, usize);
    fn get<'s>(store: &'s Arena, index: Index<Self>) -> &'s Self {
        &store.strings
            [index.0 .0 - store.strings_start..index.0 .0 + index.0 .1 - store.strings_start]
    }
    fn alloc_clone<'s>(store: &'s mut Arena, data: &Self) -> Index<Self> {
        let start = store.strings.len() + store.strings_start;
        store.strings.push_str(data);
        Index((start, data.len()))
    }
    fn contains<'s>(store: &'s Arena, index: Index<Self>) -> bool {
        fn contains_inner<'s>(store: &'s Arena, index: usize) -> bool {
            (store.strings_start..store.strings_start + store.strings.len()).contains(&index)
        }
        contains_inner(store, index.0 .0)
            && (index.0 .1 == 0 || contains_inner(store, index.0 .0 + index.0 .1 - 1))
    }
}

impl<T: Indexable + ?Sized> Clone for Index<T>
where
    T::Store: Clone,
{
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}
impl<T: Indexable + ?Sized> Debug for Index<T>
where
    T::Store: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl<T: Indexable + ?Sized> PartialEq for Index<T>
where
    T::Store: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.0.eq(&other.0)
    }
    fn ne(&self, other: &Self) -> bool {
        self.0.ne(&other.0)
    }
}
impl<T: Indexable + ?Sized> Eq for Index<T> where T::Store: Eq {}

impl<T: Indexable + ?Sized> PartialOrd for Index<T>
where
    T::Store: PartialOrd,
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.0.partial_cmp(&other.0)
    }
}
impl<T: Indexable + ?Sized> Ord for Index<T>
where
    T::Store: Ord,
{
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.cmp(&other.0)
    }
}

pub trait ArenaLike: Clone {
    fn get<T: Indexable + ?Sized>(&self, index: Index<T>) -> &T;
    fn empty_string(&self) -> Index<str>;
}

use std::sync::Arc;
impl ArenaLike for Arc<Arena> {
    fn get<T: Indexable + ?Sized>(&self, index: Index<T>) -> &T {
        Arena::get(self.as_ref(), index)
    }
    fn empty_string(&self) -> Index<str> {
        Arena::empty_string(self.as_ref())
    }
}
impl<'a> ArenaLike for &'a Arena {
    fn get<T: Indexable + ?Sized>(&self, index: Index<T>) -> &T {
        Arena::get(self, index)
    }
    fn empty_string(&self) -> Index<str> {
        Arena::empty_string(self)
    }
}

#[derive(Default)]
pub struct TripleArena {
    pub permanent: Arena,
    pub read: Arena,
    pub write: Arena,
}

impl TripleArena {
    pub fn get<T: Indexable + ?Sized>(&self, index: Index<T>) -> &T {
        if self.permanent.contains(index) {
            self.permanent.get(index)
        } else {
            self.read.get(index)
        }
    }
    pub fn alloc<T: Indexable>(&mut self, data: T) -> Index<T> {
        T::alloc(&mut self.write, data)
    }
    pub fn alloc_clone<T: Indexable + ?Sized>(&mut self, data: &T) -> Index<T> {
        T::alloc_clone(&mut self.write, data)
    }
    pub fn memory_size(&self) -> usize {
        0
    }
    pub fn empty_string(&self) -> Index<str> {
        self.permanent.empty_string()
    }
    pub fn intern(&mut self, s: &str) -> Index<str> {
        self.permanent
            .interned(s)
            .or_else(|| self.read.interned(s))
            .unwrap_or_else(|| self.write.intern(s))
    }
    pub fn interned(&self, s: &str) -> Option<Index<str>> {
        self.permanent
            .interned(s)
            .or_else(|| self.read.interned(s))
            .or_else(|| self.read.interned(s))
    }
    pub fn flush_to_temporary(&mut self) {
        self.read.append(&mut self.write);
    }
    pub fn flush_to_permanent(&mut self) {
        self.permanent.append(&mut self.write);
    }
    pub fn reset_buffers(&mut self) {
        self.write = self.permanent.postfix_arena();
        self.read = self.permanent.postfix_arena();
    }
}

impl ArenaLike for Arc<TripleArena> {
    fn get<T: Indexable + ?Sized>(&self, index: Index<T>) -> &T {
        TripleArena::get(self, index)
    }

    fn empty_string(&self) -> Index<str> {
        TripleArena::empty_string(&self)
    }
}
