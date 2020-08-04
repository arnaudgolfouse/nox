//! Garbage collector
//!
//! I don't know why I keep this module public, it probably won't stay that way.

use super::values::Value;
use crate::parser::Chunk;
use std::{collections::HashMap, fmt, mem::size_of, ptr::NonNull, sync::Arc};

#[derive(Debug, Clone)]
pub struct GCHeader {
    next: Option<NonNull<Collectable>>,
    marked: bool,
    roots: u32,
}

impl GCHeader {
    /// Creates a header for a collectable object.
    ///
    /// This object will be rooted once to avoid collection.
    pub fn new(next: Option<NonNull<Collectable>>) -> Self {
        Self {
            next,
            marked: false,
            roots: 1,
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum CollectableObject {
    Table(HashMap<Value, Value>),
    Captured(Value),
    Function {
        chunk: Arc<Chunk>,
        captured_variables: Vec<Value>,
    },
}

impl Eq for CollectableObject {}

#[derive(Debug)]
pub struct Collectable {
    pub header: GCHeader,
    pub object: CollectableObject,
}

impl PartialEq for Collectable {
    fn eq(&self, other: &Collectable) -> bool {
        self.object == other.object
    }
}

impl fmt::Display for Collectable {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match &self.object {
            CollectableObject::Captured(value) => fmt::Display::fmt(value, formatter),
            CollectableObject::Function { .. } => formatter.write_str("<function>"),
            CollectableObject::Table(_) => formatter.write_str("<table>"),
        }
    }
}

impl Collectable {
    fn new_function(
        next: Option<NonNull<Collectable>>,
        chunk: Arc<Chunk>,
        captured_variables: Vec<Value>,
    ) -> Self {
        Self {
            header: GCHeader::new(next),
            object: CollectableObject::Function {
                chunk,
                captured_variables,
            },
        }
    }

    #[inline]
    pub fn root(&mut self) {
        self.header.roots += 1
    }

    #[inline]
    pub fn unroot(&mut self) {
        self.header.roots -= 1
    }

    #[inline]
    pub fn as_captured(&self) -> Option<&Value> {
        match &self.object {
            CollectableObject::Captured(value) => Some(value),
            _ => None,
        }
    }

    fn to_mark(&self) -> Vec<&Collectable> {
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

    fn size(&self) -> usize {
        let size = size_of::<Collectable>();
        match &self.object {
            CollectableObject::Table(table) => {
                size + size_of::<(Value, Value)>() * table.capacity()
            }
            CollectableObject::Function {
                captured_variables, ..
            } => size + size_of::<Value>() * captured_variables.capacity(),
            CollectableObject::Captured(_) => size,
        }
    }
}

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
    pub fn new() -> Self {
        Self {
            allocated: 0,
            threshold: INITIAL_THRESHOLD,
            first: None,
        }
    }

    /// Drop a value, and updates the amount of allocated memory.
    fn drop_value(&mut self, value: &mut Collectable) {
        self.allocated -= value.size();
        unsafe { std::ptr::drop_in_place(value as *mut _) };
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
                self.threshold = std::cmp::max(
                    self.threshold,
                    ((self.allocated + additional) as f64 * 1.7) as usize,
                );
                if self.allocated + additional <= self.threshold {
                    break;
                }
            }
            #[cfg(debug_assertions)]
            println!("new threshold = {}\n=========", self.threshold);
        }
    }

    /// Clones a collectable value, creating a new, fresh one (aka a different
    /// pointer).
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
    ///
    /// # Safety
    ///
    /// The old value **must** be rooted in order to avoid collection during the
    /// copy !
    pub unsafe fn clone_value(&mut self, value: &Value) -> Value {
        match value {
            Value::Collectable(ptr) => match &ptr.as_ref().object {
                CollectableObject::Table(table) => {
                    let mut new_table = self.new_table();
                    if let Some(new_table) = new_table.as_table_mut() {
                        for (key, value) in table {
                            self.add_table_element(new_table, key.duplicate(), value.duplicate());
                        }
                    }
                    new_table
                }
                CollectableObject::Function {
                    captured_variables,
                    chunk,
                } => self.new_function(chunk.clone(), Value::duplicate_vec(captured_variables)),
                CollectableObject::Captured(value) => self.new_captured(value.duplicate()),
            },
            _ => value.duplicate(),
        }
    }

    /// Creates a new garbage collected function.
    ///
    /// This function will be rooted
    pub fn new_function(&mut self, chunk: Arc<Chunk>, mut captured_variables: Vec<Value>) -> Value {
        captured_variables.shrink_to_fit();
        let mut collectable = Collectable::new_function(None, chunk, captured_variables);
        let additional = collectable.size();
        self.check(additional);
        collectable.header.next = self.first.take();
        let ptr = unsafe { NonNull::new_unchecked(Box::into_raw(Box::new(collectable))) };
        self.first = Some(ptr);
        self.allocated += additional;
        Value::Collectable(ptr)
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
            let mut collectable = Collectable {
                header: GCHeader::new(None),
                object: CollectableObject::Captured(value),
            };
            let additional = collectable.size();
            self.check(additional);
            collectable.header.next = self.first.take();
            let ptr = unsafe { NonNull::new_unchecked(Box::into_raw(Box::new(collectable))) };
            self.first = Some(ptr);
            self.allocated += additional;
            Value::Collectable(ptr)
        }
    }

    /// Creates a new empty table.
    ///
    /// The new table will be rooted.
    pub fn new_table(&mut self) -> Value {
        let mut collectable = Collectable {
            header: GCHeader::new(None),
            object: CollectableObject::Table(HashMap::new()),
        };
        let additional = collectable.size();
        self.check(additional);
        collectable.header.next = self.first.take();
        let ptr = unsafe { NonNull::new_unchecked(Box::into_raw(Box::new(collectable))) };
        self.first = Some(ptr);
        self.allocated += additional;
        Value::Collectable(ptr)
    }

    /// Add a `(key, value)` pair to the `table`.
    ///
    /// Updates the allocated memory of the GC.
    pub fn add_table_element(
        &mut self,
        table: &mut HashMap<Value, Value>,
        key: Value,
        value: Value,
    ) {
        let old_capacity = table.capacity() * size_of::<(Value, Value)>();
        table.insert(key, value);
        let additional = table.capacity() * size_of::<(Value, Value)>() - old_capacity;
        self.check(additional);
        self.allocated += additional;
    }

    /// Removes an element from the table, and updates the amount of allocated
    /// memory.
    pub fn remove_table_element(&mut self, table: &mut HashMap<Value, Value>, key: &Value) {
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
        while let Some(mut value) = self.first {
            let value = unsafe { value.as_mut() };
            if value.header.marked {
                break;
            }
            self.first = value.header.next;
            self.drop_value(value);
        }
        let mut current = self.first;
        while let Some(mut value) = current {
            let value = unsafe { value.as_mut() };
            if let Some(mut next) = value.header.next {
                let next = unsafe { next.as_mut() };
                if !next.header.marked {
                    value.header.next = next.header.next;
                    self.drop_value(next);
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
            self.drop_value(value);
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
        //unsafe { self.force_empty() }
        self.mark_and_sweep(); // oooh, risky
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
