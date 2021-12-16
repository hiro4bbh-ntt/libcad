//! The `std::fmt`-related utility.

use std::fmt;

/// A wrapper object for displaying objects in the iterator.
/// ```rust
/// use libcad::fmt::DisplayIter;
/// assert_eq!("(1)", DisplayIter("(", vec![1].iter(), ",", ")").to_string());
/// assert_eq!("(1,2,3)", DisplayIter("(", vec![1, 2, 3].iter(), ",", ")").to_string());
/// assert_eq!("()", DisplayIter("(", Vec::<isize>::new().iter(), ",", ")").to_string());
/// ```
#[derive(Clone, Debug)]
pub struct DisplayIter<'a, T: fmt::Display, I: Clone + Iterator<Item = T>>(
    pub &'a str,
    pub I,
    pub &'a str,
    pub &'a str,
);

impl<'a, T: fmt::Display, I: Clone + Iterator<Item = T>> fmt::Display for DisplayIter<'a, T, I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", self.0)?;
        for (i, e) in self.1.clone().enumerate() {
            if i > 0 {
                write!(f, "{}", self.2)?;
            }
            write!(f, "{}", e)?;
        }
        write!(f, "{}", self.3)
    }
}

/// A wrapper object for displaying objects in the iterator on a map object.
/// ```rust
/// use libcad::btree_map;
/// use libcad::fmt::DisplayMapIter;
/// use std::collections::BTreeMap;
/// assert_eq!("(A->1)", DisplayMapIter("(", btree_map!["A" => 1].iter(), "->", ",", ")").to_string());
/// assert_eq!("(A->1,B->2,C->3)", DisplayMapIter("(", btree_map!["A" => 1, "B" => 2, "C" => 3].iter(), "->", ",", ")").to_string());
/// assert_eq!("()", DisplayMapIter("(", BTreeMap::<&str, isize>::new().iter(), "->", ",", ")").to_string());
/// ```
#[derive(Clone, Debug)]
pub struct DisplayMapIter<'a, K: fmt::Display, V: fmt::Display, I: Clone + Iterator<Item = (K, V)>>(
    pub &'a str,
    pub I,
    pub &'a str,
    pub &'a str,
    pub &'a str,
);

impl<'a, K: fmt::Display, V: fmt::Display, I: Clone + Iterator<Item = (K, V)>> fmt::Display
    for DisplayMapIter<'a, K, V, I>
{
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", self.0)?;
        for (i, (k, v)) in self.1.clone().enumerate() {
            if i > 0 {
                write!(f, "{}", self.3)?;
            }
            write!(f, "{}{}{}", k, self.2, v)?;
        }
        write!(f, "{}", self.4)
    }
}
