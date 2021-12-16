//! The symbol module.

use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt;
use std::hash::Hash;
use std::rc::Rc;

/// A symbol.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Symbol(pub(crate) usize);

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", self.0)
    }
}

/// A symbol table.
#[derive(Debug)]
pub struct SymbolTable<T> {
    obj2sym: HashMap<Rc<T>, Symbol>,
    sym2obj: Vec<Rc<T>>,
}

impl<T: Clone + Eq + Hash> SymbolTable<T> {
    pub fn new(preset: Vec<T>) -> SymbolTable<T> {
        let mut tbl = SymbolTable {
            obj2sym: HashMap::new(),
            sym2obj: Vec::new(),
        };
        for item in preset {
            tbl.gensym(item);
        }
        tbl
    }
    pub fn gensym(&mut self, obj: T) -> Symbol {
        if let Some(sym) = self.obj2sym.get(&obj) {
            return *sym;
        }
        let sym = Symbol(self.sym2obj.len());
        let obj = Rc::new(obj);
        self.sym2obj.push(obj.clone());
        self.obj2sym.insert(obj, sym);
        sym
    }
    pub fn get(&self, sym: Symbol) -> Option<&T> {
        self.sym2obj.get(sym.0).map(|obj| obj.as_ref())
    }
}

include!(concat!(env!("OUT_DIR"), "/ident_preset.rs"));

thread_local! {
    static SYMTBL: RefCell<SymbolTable<String>> = {
        let preset = IDENT_PRESET
            .iter()
            .map(|sym| sym.to_string())
            .collect::<Vec<_>>();
        RefCell::new(SymbolTable::new(preset))
    };
}

/// Returns the symbol indicating the given string.
pub fn gensym(s: String) -> Symbol {
    SYMTBL.with(|symtbl| symtbl.borrow_mut().gensym(s))
}

/// Returns the string of the given symbol.
pub fn symget(sym: Symbol) -> Option<String> {
    SYMTBL.with(|symtbl| symtbl.borrow().get(sym).cloned())
}

/// An identifier that is symbol.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Ident(pub Symbol);

impl Ident {
    /// Returns the string of the identifier.
    pub fn get(&self) -> String {
        symget(self.0).unwrap()
    }
}

impl From<&str> for Ident {
    fn from(s: &str) -> Ident {
        Ident::from(String::from(s))
    }
}

impl From<String> for Ident {
    fn from(s: String) -> Ident {
        Ident(gensym(s))
    }
}

impl fmt::Display for Ident {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.get())
    }
}
