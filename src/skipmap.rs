use crate::cmp::{Cmp, MemtableKeyCmp};
use crate::rand::rngs::StdRng;
use crate::rand::{RngCore, SeedableRng};
use crate::types::{LdbIterator, Shared, share};

use bytes::Bytes;
use std::cmp::Ordering;
use std::mem::size_of;
use std::sync::Arc;

const MAX_HEIGHT: usize = 12;
const BRANCHING_FACTOR: u32 = 4;

/// A node in a skipmap contains links to the next node and others that are further away (skips);
/// `skips[0]` is the immediate element after, that is, the element contained in `next`.
struct Node {
    skips: Vec<Option<usize>>,
    // next is implicitly skips[0]
    key: Bytes,
    value: Bytes,
}

/// Implements the backing store for a `MemTable`. The important methods are `insert()` and
/// `contains()`; in order to get full key and value for an entry, use a `SkipMapIter` instance,
/// `seek()` to the key to look up (this is as fast as any lookup in a skip map), and then call
/// `current()`.
struct InnerSkipMap {
    arena: Vec<Node>,
    head: usize,
    rand: StdRng,
    len: usize,
    // approximation of memory used.
    approx_mem: usize,
    cmp: Arc<Box<dyn Cmp>>,
}

// InnerSkipMap is Send + Sync because all fields are Send + Sync (Vec, Bytes, Arc, StdRng).
// No unsafe impl needed.

pub struct SkipMap {
    map: Shared<InnerSkipMap>,
}

impl SkipMap {
    /// Returns a SkipMap that wraps the comparator inside a MemtableKeyCmp.
    pub fn new_memtable_map(cmp: Arc<Box<dyn Cmp>>) -> SkipMap {
        SkipMap::new(Arc::new(Box::new(MemtableKeyCmp(cmp))))
    }

    /// Returns a SkipMap that uses the specified comparator.
    pub fn new(cmp: Arc<Box<dyn Cmp>>) -> SkipMap {
        let mut s = Vec::new();
        s.resize(MAX_HEIGHT, None);
        
        // Head node (dummy)
        let head_node = Node {
            skips: s,
            key: Bytes::new(),
            value: Bytes::new(),
        };

        let mut arena = Vec::with_capacity(1024);
        arena.push(head_node);

        SkipMap {
            map: share(InnerSkipMap {
                arena,
                head: 0,
                rand: StdRng::seed_from_u64(0xdeadbeef),
                len: 0,
                approx_mem: size_of::<Self>() + MAX_HEIGHT * size_of::<Option<usize>>(),
                cmp,
            }),
        }
    }

    pub fn len(&self) -> usize {
        self.map.borrow().len
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn approx_memory(&self) -> usize {
        self.map.borrow().approx_mem
    }

    pub fn contains(&self, key: &[u8]) -> bool {
        self.map.borrow().contains(key)
    }

    /// inserts a key into the table. key may not be empty.
    pub fn insert(&mut self, key: Vec<u8>, val: Vec<u8>) {
        assert!(!key.is_empty());
        self.map.borrow_mut().insert(key, val);
    }

    pub fn iter(&self) -> SkipMapIter {
        SkipMapIter {
            map: self.map.clone(),
            current: self.map.borrow().head,
        }
    }
}

impl InnerSkipMap {
    fn node(&self, idx: usize) -> &Node {
        &self.arena[idx]
    }

    fn node_mut(&mut self, idx: usize) -> &mut Node {
        &mut self.arena[idx]
    }

    fn random_height(&mut self) -> usize {
        let mut height = 1;

        while height < MAX_HEIGHT && self.rand.next_u32().is_multiple_of(BRANCHING_FACTOR) {
            height += 1;
        }

        height
    }

    fn contains(&self, key: &[u8]) -> bool {
        // get_greater_or_equal returns the node >= key.
        // If we found exact match, it returns that node.
        if let Some(idx) = self.get_greater_or_equal(key) {
            self.node(idx).key.starts_with(key)
        } else {
            false
        }
    }

    /// Returns the node index with key or the next greater one
    /// Returns None if the given key lies past the greatest key in the table.
    fn get_greater_or_equal(&self, key: &[u8]) -> Option<usize> {
        let mut current = self.head;
        let mut level = self.node(self.head).skips.len() - 1;

        loop {
            // Check next node at this level
            if let Some(next) = self.node(current).skips[level] {
                let next_node = self.node(next);
                let ord = self.cmp.cmp(&next_node.key, key);

                match ord {
                    Ordering::Less => {
                        current = next;
                        continue;
                    }
                    Ordering::Equal => return Some(next),
                    Ordering::Greater => {
                        // next is greater, so we don't advance `current`.
                        // We go down a level to find something closer.
                    }
                }
            }
            if level == 0 {
                break;
            }
            level -= 1;
        }

        // `current` is the largest node < key (or head).
        // The node we want is `current.next` (skips[0]).
        self.node(current).skips[0]
    }

    /// Finds the node immediately before the node with key.
    /// Returns None if no smaller key was found.
    fn get_next_smaller(&self, key: &[u8]) -> Option<usize> {
        let mut current = self.head;
        let mut level = self.node(self.head).skips.len() - 1;

        loop {
            if let Some(next) = self.node(current).skips[level] {
                let next_node = self.node(next);
                let ord = self.cmp.cmp(&next_node.key, key);

                if let Ordering::Less = ord {
                    current = next;
                    continue;
                }
            }

            if level == 0 {
                break;
            }
            level -= 1;
        }

        if current == self.head {
            None
        } else {
            Some(current)
        }
    }

    fn insert(&mut self, key: Vec<u8>, val: Vec<u8>) {
        assert!(!key.is_empty());

        let mut prevs: [usize; MAX_HEIGHT] = [self.head; MAX_HEIGHT];
        let new_height = self.random_height();
        
        let mut level = MAX_HEIGHT - 1;
        let mut current = self.head;

        loop {
            if let Some(next) = self.node(current).skips[level] {
                let next_node = self.node(next);
                let ord = self.cmp.cmp(&next_node.key, &key);

                assert!(ord != Ordering::Equal, "No duplicates allowed");

                if ord == Ordering::Less {
                    current = next;
                    continue;
                }
            }

            if level < new_height {
                prevs[level] = current;
            }

            if level == 0 {
                break;
            } else {
                level -= 1;
            }
        }

        // Construct new node
        let mut new_skips = Vec::new();
        new_skips.resize(new_height, None);
        
        let new_idx = self.arena.len();
        let new_node = Node {
            skips: new_skips,
            key: key.into(),
            value: val.into(),
        };
        self.arena.push(new_node);

        // Update links
        for i in 0..new_height {
            let prev_idx = prevs[i];
            let prev_skip = self.node(prev_idx).skips[i];
            
            self.node_mut(new_idx).skips[i] = prev_skip;
            self.node_mut(prev_idx).skips[i] = Some(new_idx);
        }

        let new_node_ref = self.node(new_idx);
        let added_mem = size_of::<Node>()
            + size_of::<Option<usize>>() * new_node_ref.skips.len()
            + new_node_ref.key.len()
            + new_node_ref.value.len();
        self.approx_mem += added_mem;
        self.len += 1;
    }

    fn dbg_print(&self) {
        let mut current = self.head;
        loop {
            let current_node = self.node(current);
            eprintln!(
                "{:?} {:?}/{:?} - {:?}",
                current, current_node.key, current_node.value, current_node.skips
            );
            if let Some(next) = current_node.skips[0] {
                current = next;
            } else {
                break;
            }
        }
    }
}

pub struct SkipMapIter {
    map: Shared<InnerSkipMap>,
    current: usize,
}

impl LdbIterator for SkipMapIter {
    fn advance(&mut self) -> bool {
        let guard = self.map.borrow();
        let r = if let Some(next) = guard.node(self.current).skips[0] {
            self.current = next;
            true
        } else {
            false
        };
        drop(guard);
        
        if !r {
            self.reset();
        }
        r
    }
    
    fn reset(&mut self) {
        self.current = self.map.borrow().head;
    }
    
    fn seek(&mut self, key: &[u8]) {
        let guard = self.map.borrow();
        if let Some(idx) = guard.get_greater_or_equal(key) {
            self.current = idx;
        } else {
            self.current = guard.head;
        }
    }
    
    fn valid(&self) -> bool {
        let guard = self.map.borrow();
        self.current != guard.head && self.current < guard.arena.len()
    }
    
    fn current(&self) -> Option<(Bytes, Bytes)> {
        let guard = self.map.borrow();
        if self.current != guard.head && self.current < guard.arena.len() {
             let node = guard.node(self.current);
             Some((
                 Bytes::copy_from_slice(&node.key),
                 Bytes::copy_from_slice(&node.value),
             ))
        } else {
            None
        }
    }
    
    fn prev(&mut self) -> bool {
        let guard = self.map.borrow();
        if self.current != guard.head {
            let current_key = &guard.node(self.current).key;
            if let Some(prev) = guard.get_next_smaller(current_key) {
                self.current = prev;
                return true;
            }
        }
        drop(guard);
        self.reset();
        false
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::cmp::MemtableKeyCmp;
    use crate::options;
    use crate::test_util::{test_iterator_properties, LdbIteratorIter};
    use crate::types::current_key_val;

    pub fn make_skipmap() -> SkipMap {
        let mut skm = SkipMap::new(options::for_test().cmp);
        let keys = vec![
            "aba", "abb", "abc", "abd", "abe", "abf", "abg", "abh", "abi", "abj", "abk", "abl",
            "abm", "abn", "abo", "abp", "abq", "abr", "abs", "abt", "abu", "abv", "abw", "abx",
            "aby", "abz",
        ];

        for k in keys {
            skm.insert(k.as_bytes().to_vec(), "def".as_bytes().to_vec());
        }
        skm
    }

    #[test]
    fn test_insert() {
        let skm = make_skipmap();
        assert_eq!(skm.len(), 26);
        skm.map.borrow().dbg_print();
    }

    #[test]
    #[should_panic]
    fn test_no_dupes() {
        let mut skm = make_skipmap();
        // this should panic
        skm.insert("abc".as_bytes().to_vec(), "def".as_bytes().to_vec());
        skm.insert("abf".as_bytes().to_vec(), "def".as_bytes().to_vec());
    }

    #[test]
    fn test_contains() {
        let skm = make_skipmap();
        assert!(skm.contains(b"aby"));
        assert!(skm.contains(b"abc"));
        assert!(skm.contains(b"abz"));
        assert!(!skm.contains(b"ab{"));
        assert!(!skm.contains(b"123"));
        assert!(!skm.contains(b"aaa"));
        assert!(!skm.contains(b"456"));
    }

    #[test]
    fn test_find() {
        let skm = make_skipmap();
        assert_eq!(
            skm.map.borrow().node(skm.map.borrow().get_greater_or_equal(b"abf").unwrap()).key,
            b"abf".as_slice()
        );
        assert!(skm.map.borrow().get_greater_or_equal(b"ab{").is_none());
        assert_eq!(
            skm.map.borrow().node(skm.map.borrow().get_greater_or_equal(b"aaa").unwrap()).key,
            b"aba".as_slice()
        );
        assert_eq!(
             skm.map.borrow().node(skm.map.borrow().get_greater_or_equal(b"ab").unwrap()).key,
             b"aba".as_slice()
        );
        assert_eq!(
             skm.map.borrow().node(skm.map.borrow().get_greater_or_equal(b"abc").unwrap()).key,
             b"abc".as_slice()
        );
        assert!(skm.map.borrow().get_next_smaller(b"ab0").is_none());
        assert_eq!(
             skm.map.borrow().node(skm.map.borrow().get_next_smaller(b"abd").unwrap()).key,
             b"abc".as_slice()
        );
        assert_eq!(
             skm.map.borrow().node(skm.map.borrow().get_next_smaller(b"ab{").unwrap()).key,
             b"abz".as_slice()
        );
    }

    #[test]
    fn test_empty_skipmap_find_memtable_cmp() {
        // Regression test: Make sure comparator isn't called with empty key.
        let cmp: Arc<Box<dyn Cmp>> = Arc::new(Box::new(MemtableKeyCmp(options::for_test().cmp)));
        let skm = SkipMap::new(cmp);

        let mut it = skm.iter();
        it.seek(b"abc");
        assert!(!it.valid());
    }

    #[test]
    fn test_skipmap_iterator_0() {
        let skm = SkipMap::new(options::for_test().cmp);
        let mut i = 0;

        for (_, _) in LdbIteratorIter::wrap(&mut skm.iter()) {
            i += 1;
        }

        assert_eq!(i, 0);
        assert!(!skm.iter().valid());
    }

    #[test]
    fn test_skipmap_iterator_init() {
        let skm = make_skipmap();
        let mut iter = skm.iter();

        assert!(!iter.valid());
        iter.next();
        assert!(iter.valid());
        iter.reset();
        assert!(!iter.valid());

        iter.next();
        assert!(iter.valid());
        iter.prev();
        assert!(!iter.valid());
    }

    #[test]
    fn test_skipmap_iterator() {
        let skm = make_skipmap();
        let mut i = 0;

        for (k, v) in LdbIteratorIter::wrap(&mut skm.iter()) {
            assert!(!k.is_empty());
            assert!(!v.is_empty());
            i += 1;
        }
        assert_eq!(i, 26);
    }

    #[test]
    fn test_skipmap_iterator_seek_valid() {
        let skm = make_skipmap();
        let mut iter = skm.iter();

        iter.next();
        assert!(iter.valid());
        assert_eq!(current_key_val(&iter).unwrap().0, "aba".as_bytes().to_vec());
        iter.seek(b"abz");
        assert_eq!(
            current_key_val(&iter).unwrap(),
            ("abz".as_bytes().to_vec(), "def".as_bytes().to_vec())
        );
        // go back to beginning
        iter.seek(b"aba");
        assert_eq!(
            current_key_val(&iter).unwrap(),
            (b"aba".to_vec(), b"def".to_vec())
        );

        iter.seek(b"");
        assert!(iter.valid());
        iter.prev();
        assert!(!iter.valid());

        while iter.advance() {}
        assert!(!iter.valid());
        assert!(!iter.prev());
        assert_eq!(current_key_val(&iter), None);
    }

    #[test]
    fn test_skipmap_behavior() {
        let mut skm = SkipMap::new(options::for_test().cmp);
        let keys = vec!["aba", "abb", "abc", "abd"];
        for k in keys {
            skm.insert(k.as_bytes().to_vec(), "def".as_bytes().to_vec());
        }
        test_iterator_properties(skm.iter());
    }

    #[test]
    fn test_skipmap_iterator_prev() {
        let skm = make_skipmap();
        let mut iter = skm.iter();

        iter.next();
        assert!(iter.valid());
        iter.prev();
        assert!(!iter.valid());
        iter.seek(b"abc");
        iter.prev();
        assert_eq!(
            current_key_val(&iter).unwrap(),
            ("abb".as_bytes().to_vec(), "def".as_bytes().to_vec())
        );
    }

    #[test]
    fn test_skipmap_iterator_concurrent_insert() {
        time_test!();
        // Asserts that the map can be mutated while an iterator exists; this is intentional.
        let mut skm = make_skipmap();
        let mut iter = skm.iter();

        assert!(iter.advance());
        skm.insert("abccc".as_bytes().to_vec(), "defff".as_bytes().to_vec());
        // Assert that value inserted after obtaining iterator is present.
        for (k, _) in LdbIteratorIter::wrap(&mut iter) {
            if k == "abccc".as_bytes() {
                return;
            }
        }
        panic!("abccc not found in map.");
    }
}
