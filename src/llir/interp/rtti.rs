//! The RunTime Type Information (RTTI) module of the interpreter.

use crate::symbol::Ident;
use std::fmt;

/// A extension name of a runtime type.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ExtName {
    /// A target field of `cast-match`.
    CastTarget(Ident),
    /// A `i`-th tag field of `cast-match`.
    CastTag(Ident, usize),
    /// A target field of the base struct of `downcast-match`.
    DowncastTarget(Ident),
    /// A target field of the inherit struct of `downcast-match`.
    DowncastSubtarget(Ident, usize),
    /// A `i`-th tag field of `restrict-cast-match`.
    DowncastTag(Ident, usize),
    /// A base of `restrict`.
    RestrictBase(Ident),
}

impl ExtName {
    /// Returns the identifier of `*cast-match`.
    pub fn id(&self) -> Ident {
        match self {
            ExtName::CastTarget(id)
            | ExtName::CastTag(id, _)
            | ExtName::DowncastTarget(id)
            | ExtName::DowncastSubtarget(id, _)
            | ExtName::DowncastTag(id, _)
            | ExtName::RestrictBase(id) => *id,
        }
    }
    /// Returns `true` if `DowncastTarget`.
    pub fn is_downcast_target(&self) -> bool {
        matches!(self, ExtName::DowncastTarget(_))
    }
    /// Returns `true` if `DowncastSubtarget`.
    pub fn is_downcast_subtarget(&self) -> bool {
        matches!(self, ExtName::DowncastSubtarget(..))
    }
    /// Returns `true` if `DowncastTag`.
    pub fn is_downcast_tag(&self) -> bool {
        matches!(self, ExtName::DowncastTag(..))
    }
    /// Returns `true` if `RestrictBase`.
    pub fn is_restrict_base(&self) -> bool {
        matches!(self, ExtName::RestrictBase(..))
    }
    /// Returns `true` if `*Target`.
    pub fn is_any_target(&self) -> bool {
        matches!(self, ExtName::CastTarget(_) | ExtName::DowncastTarget(_))
    }
    /// Returns `true` if `*Tag`.
    pub fn is_any_tag(&self) -> bool {
        matches!(
            self,
            ExtName::CastTag(..) | ExtName::DowncastTag(..) | ExtName::RestrictBase(_)
        )
    }
}

impl fmt::Display for ExtName {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ExtName::CastTarget(id) => write!(f, "!{}.cast-target", id),
            ExtName::CastTag(id, n) => write!(f, "!{}.cast-tag{}", id, n),
            ExtName::DowncastTarget(id) => write!(f, "!{}.downcast-target", id),
            ExtName::DowncastSubtarget(id, n) => write!(f, "!{}.downcast-subtarget{}", id, n),
            ExtName::DowncastTag(id, n) => write!(f, "!{}.downcast-tag{}", id, n),
            ExtName::RestrictBase(id) => write!(f, "!{}.restrict-base", id),
        }
    }
}

/// A extension identifier of a runtime type.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ExtIdent {
    /// The extension name.
    pub name: ExtName,
    /// The ID of the refinement application.
    pub appid: usize,
    /// The offset in the base struct.
    pub offset: i64,
}

impl fmt::Display for ExtIdent {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}@{}{:+}", self.name, self.appid, self.offset)
    }
}
