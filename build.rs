use std::env;
use std::fs;
use std::fs::File;
use std::io;
use std::io::BufWriter;
use std::path::Path;
use std::process::Command;

#[derive(Clone, Copy, Debug, PartialEq)]
enum Kind {
    Ident,
    GlobalIdent,
    Label,
}

struct IdentPresetGenerator<'a> {
    preset: Vec<(&'a str, Kind)>,
}

impl IdentPresetGenerator<'_> {
    pub fn write_preset_to<W>(&mut self, mut w: W) -> io::Result<()>
    where
        W: io::Write,
    {
        write!(
            w,
            r#"static IDENT_PRESET: [&str; {}] = ["#,
            self.preset.len()
        )?;
        for (keyword, _) in &self.preset {
            write!(w, r#"{:?},"#, keyword)?;
        }
        write!(w, r#"];"#)
    }
    pub fn write_idents_to<W>(&mut self, mut w: W, kind: &Kind) -> io::Result<()>
    where
        W: io::Write,
    {
        let (macroname, prefix, suffix) = match kind {
            Kind::Ident => ("ident", "crate::symbol::Ident(crate::symbol::Symbol(", "))"),
            Kind::GlobalIdent => (
                "global_ident",
                "crate::llir::syntax::GlobalIdent(crate::symbol::Symbol(",
                "))",
            ),
            Kind::Label => (
                "label",
                "crate::llir::syntax::Label::from(crate::llir::syntax::LocalIdent(crate::symbol::Symbol(",
                ")))",
            ),
        };
        write!(w, r#"macro_rules! {} {{"#, macroname)?;
        for (i, (keyword, k)) in self.preset.iter().enumerate() {
            if k == kind {
                write!(w, r#"({:?}) => {{ {}{}{} }};"#, keyword, prefix, i, suffix)?;
            }
        }
        write!(w, r#"}}"#)
    }
    fn write_to_files(&mut self, path: &Path) -> io::Result<()> {
        self.write_preset_to(BufWriter::new(File::create(path.join("ident_preset.rs"))?))?;
        self.write_idents_to(
            BufWriter::new(File::create(path.join("ident_macro.rs"))?),
            &Kind::Ident,
        )?;
        self.write_idents_to(
            BufWriter::new(File::create(path.join("global_ident_macro.rs"))?),
            &Kind::GlobalIdent,
        )?;
        self.write_idents_to(
            BufWriter::new(File::create(path.join("label_macro.rs"))?),
            &Kind::Label,
        )
    }
}

fn generate_ident_preset(path: &Path) {
    let mut gen = IdentPresetGenerator {
        preset: vec![
            ("!=", Kind::Ident),
            ("$0", Kind::Ident),
            ("$1", Kind::Ident),
            ("$2", Kind::Ident),
            ("$3", Kind::Ident),
            ("$4", Kind::Ident),
            ("$5", Kind::Ident),
            ("$6", Kind::Ident),
            ("$7", Kind::Ident),
            ("$8", Kind::Ident),
            ("$9", Kind::Ident),
            ("<", Kind::Ident),
            ("<=", Kind::Ident),
            ("==", Kind::Ident),
            ("and", Kind::Ident),
            ("apply-refiner", Kind::Ident),
            ("baseptr", Kind::Ident),
            ("bitand", Kind::Ident),
            ("bitlshr", Kind::Ident),
            ("cast", Kind::Ident),
            ("cast-match", Kind::Ident),
            ("column", Kind::Label),
            ("define", Kind::Ident),
            ("define-refiner", Kind::Ident),
            ("deref", Kind::Ident),
            ("directory", Kind::Label),
            ("double", Kind::Ident),
            ("downcast", Kind::Ident),
            ("false", Kind::Ident),
            ("fieldptr", Kind::Ident),
            ("file", Kind::Label),
            ("filename", Kind::Label),
            ("float", Kind::Ident),
            ("free", Kind::GlobalIdent),
            ("func", Kind::Ident),
            ("i1", Kind::Ident),
            ("i8", Kind::Ident),
            ("i16", Kind::Ident),
            ("i32", Kind::Ident),
            ("i64", Kind::Ident),
            ("line", Kind::Label),
            ("llvm.dbg.declare", Kind::GlobalIdent),
            ("llvm.dbg.label", Kind::GlobalIdent),
            ("llvm.dbg.value", Kind::GlobalIdent),
            ("llvm.memcpy.p0i8.p0i8.i64", Kind::GlobalIdent),
            ("malloc", Kind::GlobalIdent),
            ("ptr", Kind::Ident),
            ("refine-type", Kind::Ident),
            ("restrict", Kind::Ident),
            ("restrict-cast-match", Kind::Ident),
            ("scope", Kind::Label),
            ("true", Kind::Ident),
            ("varfunc", Kind::Ident),
            ("void", Kind::Ident),
            ("_ZdlPv", Kind::GlobalIdent),
            ("_Znwm", Kind::GlobalIdent),
        ],
    };
    gen.write_to_files(path).unwrap();
}

fn compile_tests_cpp(path: &Path) {
    let pwd = env::var("PWD").unwrap();
    let cxx = env::var("CXX").unwrap_or_else(|_| String::from("clang++"));
    for name in &[
        "pointer_subtyping_unsoundness",
        "tagged_union",
        "tagged_union_vuln",
        "tagged_union_restrict",
        "tagged_union_restrict_vuln",
        "tagged_union_unsupported",
        "single_inherit_class",
        "single_inherit_class_vuln",
    ] {
        let cppfilename = format!("./tests/cpp/{}.cpp", name);
        let cppfilepath = Path::new(&pwd).join(&cppfilename);
        let cppfilets = fs::metadata(&cppfilepath).unwrap().modified().unwrap();
        let outfilename = format!("{}.ll", name);
        let outfilepath = path.join(&outfilename);
        if let Ok(outfilemd) = fs::metadata(&outfilepath) {
            let outfilets = outfilemd.modified().unwrap();
            if cppfilets < outfilets {
                continue;
            }
        }
        let output = Command::new(cxx.clone())
            .args(&[
                // Emit LLIR text representations.
                "-S",
                "-emit-llvm",
                // Emit with debug information.
                "-g",
                // Disable all optimizations.
                "-O0",
                // Fix the target architecture `x86_64`.
                // This is because some architectures or ABIs do not fully capture type information.
                // See also: https://lists.llvm.org/pipermail/cfe-dev/2013-January/027302.html .
                "-arch",
                "x86_64",
                "-o",
                outfilepath.to_str().unwrap(),
                cppfilepath.to_str().unwrap(),
            ])
            .output()
            .unwrap();
        if !output.status.success() {
            panic!(
                "failed to compile {} by {} with {}\n{}",
                cppfilename,
                cxx,
                output.status,
                String::from_utf8(output.stderr).unwrap()
            );
        }
    }
}

fn main() {
    let out_dir = env::var("OUT_DIR").unwrap();
    let out_dir_path = Path::new(&out_dir);
    generate_ident_preset(out_dir_path);
    compile_tests_cpp(out_dir_path);
}
