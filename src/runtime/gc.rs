//! Garbage collector
//!
//! I don't know why I keep this module public, it probably won't stay that way.
//!
//! TODO : Still very unsafe : in particular, the `GC` has a mutable access to
//! every value it references... Ah ! But they should ONLY be mutated during
//! destruction, aka when 'no one' can access them... hum

use super::values::{NoDropValue, Value};
use crate::parser::Chunk;
use std::{collections::HashMap, fmt, mem::size_of, ptr::NonNull, sync::Arc};

/// Meta-information about a collectable value.
#[derive(Debug, Clone)]
pub struct GCHeader {
    /// Next collectable value.
    next: Option<NonNull<Collectable>>,
    /// Is the value still reacheable ?
    ///
    /// Used during the mark-and-sweep algorithm.
    marked: bool,
    /// Number of roots for this value.
    roots: u32,
}

impl GCHeader {
    /// Creates a header for a collectable object.
    ///
    /// This object will be rooted once to avoid collection.
    pub const fn new() -> Self {
        Self {
            next: None,
            marked: false,
            roots: 1,
        }
    }
}

/// The type of the collectable value.
#[derive(Debug, PartialEq)]
pub enum CollectableObject {
    /// Table object
    Table(HashMap<NoDropValue, NoDropValue>),
    /// Captured value
    Captured(NoDropValue),
    /// Nox function
    Function {
        chunk: Arc<Chunk>,
        captured_variables: Vec<NoDropValue>,
    },
}

impl Eq for CollectableObject {}

/// A collectable value living on the heap.
#[derive(Debug)]
pub struct Collectable {
    pub header: GCHeader,
    pub object: CollectableObject,
}

impl PartialEq for Collectable {
    fn eq(&self, other: &Self) -> bool {
        self.object == other.object
    }
}

impl fmt::Display for Collectable {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match &self.object {
            CollectableObject::Captured(value) => fmt::Display::fmt(value as &Value, formatter),
            CollectableObject::Function { .. } => formatter.write_str("<function>"),
            CollectableObject::Table(_) => formatter.write_str("<table>"),
        }
    }
}

impl Collectable {
    /// Add a root to the `Collectable`.
    #[inline]
    pub fn root(&mut self) {
        self.header.roots += 1
    }

    /// Remove a root
    ///
    /// # Safety
    ///
    /// If the root count reaches `0` via this function, the value **must** not
    /// be ready to be collected (aka there is a rooted object referencing this).
    #[inline]
    pub unsafe fn unroot(&mut self) {
        self.header.roots -= 1
    }

    /// If `self` is a captured value, return it.
    ///
    /// Else, return [`None`].
    #[inline]
    pub fn as_captured(&self) -> Option<&Value> {
        match &self.object {
            CollectableObject::Captured(value) => Some(value),
            _ => None,
        }
    }

    /// Returns the list of values rattached to this one.
    fn to_mark(&self) -> Vec<&Self> {
        match &self.object {
            CollectableObject::Captured(value) => match value.as_collectable() {
                None => vec![],
                Some(collectable) => vec![collectable],
            },
            CollectableObject::Function {
                captured_variables, ..
            } => {
                let mut to_mark = Vec::new();
                for captured in captured_variables {
                    match captured.as_collectable() {
                        None => {}
                        Some(collectable) => to_mark.push(collectable),
                    }
                }
                to_mark
            }
            CollectableObject::Table(table) => {
                let mut to_mark = Vec::new();
                for (key, value) in table {
                    match key.as_collectable() {
                        None => {}
                        Some(collectable) => to_mark.push(collectable),
                    }
                    match value.as_collectable() {
                        None => {}
                        Some(collectable) => to_mark.push(collectable),
                    }
                }
                to_mark
            }
        }
    }

    /// Returns the entire on-heap size of this object.
    fn size(&self) -> usize {
        size_of::<Collectable>()
            + match &self.object {
                CollectableObject::Table(table) => {
                    size_of::<(NoDropValue, NoDropValue)>() * table.capacity()
                }
                CollectableObject::Function {
                    captured_variables, ..
                } => size_of::<NoDropValue>() * captured_variables.capacity(),
                CollectableObject::Captured(_) => 0,
            }
    }
}

#[cfg(test)]
const INITIAL_THRESHOLD: usize = 10; // we test the behavior of the GC
#[cfg(not(test))]
const INITIAL_THRESHOLD: usize = 10000;

#[derive(Debug)]
pub struct GC {
    pub(super) allocated: usize,
    threshold: usize,
    first: Option<NonNull<Collectable>>,
}

impl Default for GC {
    fn default() -> Self {
        Self::new()
    }
}

impl GC {
    /// Creates a new empty garbage collector
    pub const fn new() -> Self {
        Self {
            allocated: 0,
            threshold: INITIAL_THRESHOLD,
            first: None,
        }
    }

    /// Drop a value, and updates the amount of allocated memory.
    ///
    /// # Safety
    ///
    /// The `value` reference immediately becomes invalid.
    unsafe fn drop_value(&mut self, mut value: NonNull<Collectable>) {
        let value = value.as_mut();
        self.allocated -= value.size();
        // we created this value using `leak`, so we free it with `from_raw`.
        drop(Box::from_raw(value as *mut Collectable))
    }

    /// Check that `additional` more bytes won't go over the threshold.
    ///
    /// If it does, a mark and sweep algorithm is launched, and the treshold is
    /// increased.
    fn check(&mut self, additional: usize) {
        if self.allocated + additional > self.threshold {
            #[cfg(debug_assertions)]
            println!(
                "=========\nthreshold ({}) reached, sweeping...",
                self.threshold
            );
            #[cfg(debug_assertions)]
            let old_allocated = self.allocated;
            self.mark_and_sweep();
            #[cfg(debug_assertions)]
            println!("freed {} bytes", old_allocated - self.allocated);
            loop {
                self.threshold = std::cmp::max(self.threshold, (self.allocated + additional) * 2);
                if self.allocated + additional <= self.threshold {
                    break;
                }
            }
            #[cfg(debug_assertions)]
            println!("new threshold = {}\n=========", self.threshold);
        }
    }

    /// Clones a [`Collectable`] value, creating a new, fresh one (aka a
    /// different pointer).
    ///
    /// Does not clone the GC properties (typically roots), but share any
    /// internal collectable value, such as captured variables and table keys/
    /// values.
    ///
    /// # Remarks
    ///
    /// The new value will be rooted.
    ///
    /// If the value is not collectable, simply clones it.
    pub fn clone_value(&mut self, value: &Value) -> Value {
        match value {
            Value::Collectable(ptr) => match &unsafe { ptr.as_ref() }.object {
                CollectableObject::Table(table) => {
                    let mut new_table = self.new_table();
                    if let Some(new_table) = new_table.as_table_mut() {
                        for (key, value) in table {
                            self.add_table_element_nodrop(
                                new_table,
                                unsafe { key.duplicate() },
                                unsafe { value.duplicate() },
                            );
                        }
                    }
                    new_table
                }
                CollectableObject::Function {
                    captured_variables,
                    chunk,
                } => self.new_function_nodrop(chunk.clone(), {
                    let mut values = Vec::new();
                    for v in captured_variables {
                        values.push(unsafe { v.duplicate() })
                    }
                    values
                }),
                CollectableObject::Captured(value) => self.new_captured((value as &Value).clone()),
            },
            _ => value.clone(),
        }
    }

    /// Insert the given [`Collectable`] in the garbage collector.
    fn make_collectable(&mut self, mut collectable: Collectable) -> Value {
        let additional = collectable.size();
        self.check(additional);
        collectable.header.next = self.first.take();
        let ptr = NonNull::from(Box::leak(Box::new(collectable)));
        self.first = Some(ptr);
        self.allocated += additional;
        Value::Collectable(ptr)
    }

    /// Creates a new garbage collected function
    ///
    /// This function will be rooted.
    pub fn new_function(&mut self, chunk: Arc<Chunk>, captured_variables: Vec<Value>) -> Value {
        self.new_function_nodrop(
            chunk,
            captured_variables
                .into_iter()
                .map(|value| unsafe { NoDropValue::new(value) })
                .collect(),
        )
    }

    /// `new_function` with `NoDropValue`s.
    fn new_function_nodrop(
        &mut self,
        chunk: Arc<Chunk>,
        mut captured_variables: Vec<NoDropValue>,
    ) -> Value {
        captured_variables.shrink_to_fit();
        let collectable = Collectable {
            header: GCHeader::new(),
            object: CollectableObject::Function {
                chunk,
                captured_variables,
            },
        };
        self.make_collectable(collectable)
    }

    /// Creates a new garbage collected value.
    ///
    /// If the value was already a captured variable, it is simply returned.
    ///
    /// The new value will be rooted
    pub fn new_captured(&mut self, value: Value) -> Value {
        if value.as_captured().is_some() {
            value
        } else {
            let collectable = Collectable {
                header: GCHeader::new(),
                object: CollectableObject::Captured(unsafe { NoDropValue::new(value) }),
            };
            self.make_collectable(collectable)
        }
    }

    /// Creates a new empty table.
    ///
    /// The new table will be rooted.
    pub fn new_table(&mut self) -> Value {
        let collectable = Collectable {
            header: GCHeader::new(),
            object: CollectableObject::Table(HashMap::new()),
        };
        self.make_collectable(collectable)
    }

    /// Add a `(key, value)` pair to the `table`.
    ///
    /// Updates the allocated memory of the GC.
    pub fn add_table_element(
        &mut self,
        table: &mut HashMap<NoDropValue, NoDropValue>,
        key: Value,
        value: Value,
    ) {
        unsafe {
            self.add_table_element_nodrop(table, NoDropValue::new(key), NoDropValue::new(value))
        }
    }

    fn add_table_element_nodrop(
        &mut self,
        table: &mut HashMap<NoDropValue, NoDropValue>,
        key: NoDropValue,
        value: NoDropValue,
    ) {
        let old_capacity = table.capacity() * size_of::<(Value, Value)>();
        if let Value::Nil = value.captured_value_ref() {
            table.remove(&key);
            // dropping this
            let removed = old_capacity - table.capacity() * size_of::<(Value, Value)>();
            self.allocated -= removed;
        } else {
            table.insert(key, value);
            let additional = table.capacity() * size_of::<(Value, Value)>() - old_capacity;
            self.check(additional);
            self.allocated += additional;
        }
    }

    /// Removes an element from the table, and updates the amount of allocated
    /// memory.
    pub fn remove_table_element(
        &mut self,
        table: &mut HashMap<NoDropValue, NoDropValue>,
        key: &NoDropValue,
    ) {
        let old_capacity = table.capacity() * size_of::<(Value, Value)>();
        table.remove(key);
        let new_capacity = table.capacity() * size_of::<(Value, Value)>();
        self.allocated -= old_capacity - new_capacity;
    }

    /// Unmark all values.
    ///
    /// This prepares the GC for a collection
    fn unmark_all(&mut self) {
        let mut to_unmark = self.first;

        while let Some(mut value) = to_unmark {
            unsafe { value.as_mut() }.header.marked = false;
            to_unmark = unsafe { value.as_mut() }.header.next;
        }
    }

    /// Mark the rooted variables, and the variables they lead to.
    ///
    /// This is the heart of the mark-and-sweep algorithm.
    fn mark(&mut self) {
        let mut to_mark = Vec::new();
        let mut next = self.first;
        while let Some(current_ptr) = next {
            let current = unsafe { current_ptr.as_ref() };
            if current.header.roots > 0 {
                to_mark.push(current_ptr)
            }
            next = current.header.next;
        }
        while let Some(mut current) = to_mark.pop() {
            let current = unsafe { current.as_mut() };
            if !current.header.marked {
                current.header.marked = true;
                for elem in current.to_mark() {
                    if !elem.header.marked {
                        to_mark.push(NonNull::from(elem))
                    }
                }
            }
        }
    }

    /// Delete all unmarked values.
    fn sweep(&mut self) {
        while let Some(mut ptr) = self.first {
            let value = unsafe { ptr.as_mut() };
            if value.header.marked {
                break;
            }
            self.first = value.header.next;
            unsafe { self.drop_value(ptr) }
        }
        let mut current = self.first;
        while let Some(mut value) = current {
            let value = unsafe { value.as_mut() };
            if let Some(mut next_ptr) = value.header.next {
                let next = unsafe { next_ptr.as_mut() };
                if !next.header.marked {
                    value.header.next = next.header.next;
                    unsafe { self.drop_value(next_ptr) }
                } else {
                    current = value.header.next;
                }
            } else {
                break;
            }
        }
    }

    /// Run a mark-and-sweep algorithm to free unused memory.
    pub fn mark_and_sweep(&mut self) {
        self.unmark_all();
        self.mark();
        self.sweep();
    }

    /// Delete **all** values associated with this GC.
    ///
    /// # Safety
    ///
    /// This is **incredibly** unsafe, as any pointer to a gc value becomes
    /// invalid. Only use if you ABSOLUTELY need it !
    pub unsafe fn force_empty(&mut self) {
        while let Some(mut ptr) = self.first {
            let value = ptr.as_mut();
            self.first = value.header.next.take();
            self.drop_value(ptr);
        }
    }
}

impl fmt::Display for GC {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let mut ptr = self.first;
        let mut i = 0;
        while let Some(to_print_ptr) = ptr {
            let to_print = unsafe { to_print_ptr.as_ref() };
            writeln!(formatter, " {} - at {:?} - {}", i, to_print_ptr, to_print)?;
            i += 1;
            ptr = to_print.header.next;
        }
        Ok(())
    }
}

impl Drop for GC {
    fn drop(&mut self) {
        self.mark_and_sweep();
        #[cfg(debug_assertions)]
        if self.allocated != 0 {
            use colored::Colorize;
            eprintln!(
                "{} {} {}",
                "!!! ALLOCATION ERROR :".red().bold(),
                self.allocated,
                "bytes still allocated !!!\n!!! Please report this error !!!"
                    .red()
                    .bold(),
            );
        }
    }
}
