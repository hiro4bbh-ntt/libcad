//! libcad is a Casting Analysis Device, which is a static analysis framework for LLVM Intermediate Representation (LLIR).

// This too terrible lint not concerning side effects enabled by default from Rust 1.56.0.
#![allow(clippy::branches_sharing_code)]

/// A macro constructing a `std::collections::BTreeMap` object.
/// ```rust
/// use libcad::btree_map;
/// use std::collections::BTreeMap;
/// assert_eq!("{\"A\": 1}", format!("{:?}", btree_map!["A"=>1]));
/// assert_eq!("{\"A\": 1, \"B\": 2}", format!("{:?}", btree_map!["A"=>1, "B"=>2]));
/// let m: BTreeMap<&str, isize> = btree_map![];
/// assert_eq!("{}", format!("{:?}", m));
/// ```
#[macro_export]
macro_rules! btree_map {
    [] => { std::collections::BTreeMap::new() };
    [ $( $key:expr => $value:expr ),+ ] => {{
        let mut map = std::collections::BTreeMap::new();
        $(map.insert($key, $value);)*
        map
    }};
}

/// A macro constructing a `std::collections::BTreeSet` object.
/// ```rust
/// use libcad::btree_set;
/// use std::collections::BTreeSet;
/// assert_eq!("{\"A\"}", format!("{:?}", btree_set!["A"]));
/// assert_eq!("{\"A\", \"B\"}", format!("{:?}", btree_set!["A", "B"]));
/// let s: BTreeSet<&str> = btree_set![];
/// assert_eq!("{}", format!("{:?}", s));
/// ```
#[macro_export]
macro_rules! btree_set {
    [] => { std::collections::BTreeSet::new() };
    [ $( $value:expr ),+ ] => {{
        let mut set = std::collections::BTreeSet::new();
        $(set.insert($value);)*
        set
    }};
}

include!(concat!(env!("OUT_DIR"), "/ident_macro.rs"));
include!(concat!(env!("OUT_DIR"), "/global_ident_macro.rs"));
include!(concat!(env!("OUT_DIR"), "/label_macro.rs"));

pub mod annot;
pub mod fmt;
pub mod llir;
pub mod num;
pub mod ops;
pub mod reader;
pub mod solver;
pub mod symbol;
pub mod typechk;
