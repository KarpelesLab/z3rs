//! A replica of the slot layout of z3's `cmd_context::m_func_decls`.
//!
//! z3 keeps user function declarations in a `dictionary<func_decls>` — an
//! open-addressing `core_hashtable` keyed by symbol (`z3/src/util/hashtable.h`).
//! `get-model` appends every declared function the solver's model does not
//! interpret (`cmd_context::add_declared_functions`) by iterating that table in
//! *slot order*, so the order of those entries in the printed model is the
//! table's physical layout. This module reproduces the layout exactly: the
//! symbol hash (`string_hash(name, 17)`, stored with the interned string), the
//! linear probing with reuse of the last tombstone seen, the growth rule
//! (`(size + deleted) * 4 > capacity * 3` doubles the table before an insert),
//! tombstones on erase, their in-place purge, and `reset`'s shrinking rule.

use crate::util::hash::string_hash;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

/// z3's `DEFAULT_HASHTABLE_INITIAL_CAPACITY`.
const INITIAL_CAPACITY: usize = 8;
/// z3's `SMALL_TABLE_CAPACITY`.
const SMALL_TABLE_CAPACITY: usize = 64;

#[derive(Clone, Debug)]
enum Slot {
    Free,
    Deleted,
    Used {
        name: String,
        hash: u32,
        count: usize,
    },
}

/// The symbol-keyed declaration table, tracking per name how many declarations
/// (overloads) it holds so a name leaves the table with its last declaration.
#[derive(Clone, Debug)]
pub struct DeclTable {
    slots: Vec<Slot>,
    size: usize,
    deleted: usize,
}

impl Default for DeclTable {
    fn default() -> Self {
        DeclTable {
            slots: vec![Slot::Free; INITIAL_CAPACITY],
            size: 0,
            deleted: 0,
        }
    }
}

/// z3's symbol hash: `string_hash` of the name seeded with 17.
fn symbol_hash(name: &str) -> u32 {
    string_hash(name.as_bytes(), 17)
}

impl DeclTable {
    /// Re-place every used entry of `slots` into a fresh table of `capacity`
    /// slots, in source slot order (z3's `move_table`).
    fn move_table(slots: &[Slot], capacity: usize) -> Vec<Slot> {
        let mut out = vec![Slot::Free; capacity];
        for s in slots {
            if let Slot::Used { hash, .. } = s {
                let mut i = (*hash as usize) & (capacity - 1);
                while !matches!(out[i], Slot::Free) {
                    i = (i + 1) & (capacity - 1);
                }
                out[i] = s.clone();
            }
        }
        out
    }

    /// Record one declaration of `name` (`insert_if_not_there` on the table,
    /// then adding the declaration to the name's overload set).
    pub fn insert(&mut self, name: &str) {
        if (self.size + self.deleted) * 4 > self.slots.len() * 3 {
            self.slots = Self::move_table(&self.slots, self.slots.len() * 2);
            self.deleted = 0;
        }
        let hash = symbol_hash(name);
        let cap = self.slots.len();
        let begin = (hash as usize) & (cap - 1);
        let mut del: Option<usize> = None;
        for k in 0..cap {
            let i = (begin + k) & (cap - 1);
            match &mut self.slots[i] {
                Slot::Used { name: n, count, .. } => {
                    if n == name {
                        *count += 1;
                        return;
                    }
                }
                Slot::Deleted => del = Some(i),
                Slot::Free => {
                    let at = match del {
                        Some(d) => {
                            self.deleted -= 1;
                            d
                        }
                        None => i,
                    };
                    self.slots[at] = Slot::Used {
                        name: String::from(name),
                        hash,
                        count: 1,
                    };
                    self.size += 1;
                    return;
                }
            }
        }
    }

    /// Drop one declaration of `name`; the name leaves the table (z3's
    /// `remove`) once its last declaration is gone.
    pub fn erase(&mut self, name: &str) {
        let cap = self.slots.len();
        let begin = (symbol_hash(name) as usize) & (cap - 1);
        for k in 0..cap {
            let i = (begin + k) & (cap - 1);
            match &mut self.slots[i] {
                Slot::Used { name: n, count, .. } if n == name => {
                    *count -= 1;
                    if *count > 0 {
                        return;
                    }
                    let next = (i + 1) & (cap - 1);
                    self.size -= 1;
                    if matches!(self.slots[next], Slot::Free) {
                        self.slots[i] = Slot::Free;
                    } else {
                        self.slots[i] = Slot::Deleted;
                        self.deleted += 1;
                        if self.deleted > self.size && self.deleted > SMALL_TABLE_CAPACITY {
                            self.slots = Self::move_table(&self.slots, cap);
                            self.deleted = 0;
                        }
                    }
                    return;
                }
                Slot::Free => return,
                _ => {}
            }
        }
    }

    /// Empty the table as z3's `reset` does (keeping, or halving, the capacity).
    pub fn reset(&mut self) {
        if self.size == 0 && self.deleted == 0 {
            return;
        }
        let cap = self.slots.len();
        let overhead = self
            .slots
            .iter()
            .filter(|s| matches!(s, Slot::Free))
            .count();
        let cap = if cap > 16 && overhead * 4 > cap * 3 {
            cap / 2
        } else {
            cap
        };
        self.slots = vec![Slot::Free; cap];
        self.size = 0;
        self.deleted = 0;
    }

    /// The declared names in slot (iteration) order.
    pub fn names(&self) -> impl Iterator<Item = &str> {
        self.slots.iter().filter_map(|s| match s {
            Slot::Used { name, .. } => Some(name.as_str()),
            _ => None,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn slot_order_matches_z3() {
        // z3 5.3.2 lists the unused constants of `a b i j` as `i b j`.
        let mut t = DeclTable::default();
        for n in ["a", "b", "i", "j"] {
            t.insert(n);
        }
        let order: Vec<&str> = t.names().filter(|n| *n != "a").collect();
        assert_eq!(order, ["i", "b", "j"]);
    }
}
