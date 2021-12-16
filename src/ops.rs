//! The `std::ops`-related utility.

use std::fmt;

/// An object is clonable and debuggable and displayable.
pub trait Object: Clone + fmt::Debug + fmt::Display {}
impl<T: Clone + fmt::Debug + fmt::Display> Object for T {}

/// An equatable is an object and equatable.
pub trait Equatable: Object + PartialEq + Eq {}
impl<T: Object + PartialEq + Eq> Equatable for T {}

/// A comparable is an equatable and partially ordered.
pub trait Comparable: Equatable + PartialOrd {}
impl<T: Equatable + Ord + PartialOrd> Comparable for T {}

/// A totally comparable is a comparable and totally ordered.
pub trait TotallyComparable: Comparable + Ord {}
impl<T: Comparable + Ord> TotallyComparable for T {}
