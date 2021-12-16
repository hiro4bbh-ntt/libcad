//! The union-find data structure module.

use crate::ops::TotallyComparable;
use std::collections::BTreeMap;
use std::fmt;

/// A Union-Find data structure.
#[derive(Clone, Debug)]
pub struct UnionFind<T: TotallyComparable>(BTreeMap<T, Option<T>>);

impl<T: TotallyComparable> UnionFind<T> {
    /// Returns an empty structure.
    pub fn empty() -> UnionFind<T> {
        UnionFind(BTreeMap::new())
    }
    /// Returns the number of the disjoint sets.
    pub fn size(&self) -> usize {
        let mut size = 0;
        for (_, s) in self.0.iter() {
            if s.is_none() {
                size += 1;
            }
        }
        size
    }
    /// Returns an iterator on the pairs of the element and set representative.
    pub fn iter(&self) -> impl Iterator<Item = (&T, &T)> {
        self.0.iter().map(move |(s, t)| match t {
            Some(t) => (s, self.find(t).unwrap()),
            None => (s, s),
        })
    }
    /// Returns the repsentative in the same set with `t`.
    pub fn find<'a>(&'a self, t: &'a T) -> Option<&'a T> {
        match self.0.get(t)? {
            Some(s) => self.find(s),
            None => Some(t),
        }
    }
    /// Merges the two set containing `t1` and `t2`.
    pub fn union(&mut self, t1: &T, t2: &T) {
        let (s, t, tail) = match self.find(t1) {
            Some(s1) => match self.find(t2) {
                Some(s2) => match s1 == s2 {
                    true => return,
                    false => (s1.clone(), s2.clone(), false),
                },
                None => (t2.clone(), s1.clone(), false),
            },
            None => (t1.clone(), t2.clone(), true),
        };
        if tail {
            self.0.insert(t.clone(), None);
        }
        self.0.insert(s, Some(t));
    }
}

impl<T: TotallyComparable> fmt::Display for UnionFind<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{{")?;
        for (i, (t, s)) in self.0.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", t)?;
            match s {
                Some(s) => write!(f, "->{}", s)?,
                None => {}
            }
        }
        write!(f, "}}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn union_find() {
        let mut eqset = UnionFind::empty();
        assert_eq!("{}", eqset.to_string());
        eqset.union(&1, &2);
        assert_eq!("{1->2, 2}", eqset.to_string());
        eqset.union(&1, &3);
        assert_eq!("{1->2, 2, 3->2}", eqset.to_string());
        eqset.union(&2, &3);
        assert_eq!("{1->2, 2, 3->2}", eqset.to_string());
        eqset.union(&4, &5);
        assert_eq!("{1->2, 2, 3->2, 4->5, 5}", eqset.to_string());
        assert_eq!(2, eqset.size());
        eqset.union(&1, &4);
        assert_eq!("{1->2, 2->5, 3->2, 4->5, 5}", eqset.to_string());
        assert_eq!(1, eqset.size());
        assert_eq!(Some(&5), eqset.find(&2));
        assert_eq!(None, eqset.find(&6));
    }
}
