use libcad::annot;
use libcad::fmt::DisplayMapIter;
use libcad::llir::abi::DataLayout;
use libcad::llir::interp;
use libcad::llir::interp::rtti::ExtIdent;
use libcad::llir::syntax::{GlobalIdent, Module, Typedefs};
use libcad::typechk;
use std::{env, fs, process};

#[derive(Clone, Debug)]
struct InterpCmdArgs {
    annot: Option<String>,
    filename: Option<String>,
    insns: Option<String>,
    verbose: bool,
}

#[derive(Clone, Debug)]
struct TypeChkCmdArgs {
    all: bool,
    annot: Option<String>,
    debug: bool,
    filenames: Vec<String>,
    verbose: bool,
}

#[derive(Clone, Debug)]
enum CmdArgs {
    Interp(InterpCmdArgs),
    TypeChk(TypeChkCmdArgs),
}

impl CmdArgs {
    fn parse<T>(argp: &mut T) -> Result<CmdArgs, String>
    where
        T: Iterator<Item = String>,
    {
        match argp.next() {
            Some(name) if name == "interp" => {
                let mut args = InterpCmdArgs {
                    annot: None,
                    filename: None,
                    insns: None,
                    verbose: false,
                };
                while let Some(arg) = &argp.next() {
                    match arg.as_ref() {
                        "--" => {}
                        "--annot" => match args.annot {
                            Some(_) => return Err("multiple annot specified".to_string()),
                            None => args.annot = argp.next(),
                        },
                        "--verbose" => args.verbose = true,
                        arg if arg.starts_with("--") => {
                            return Err(format!("unknown interp option: {}", arg))
                        }
                        _ => {
                            if args.insns.is_none() {
                                args.insns = Some(arg.clone());
                            } else if args.filename.is_none() {
                                args.filename = Some(arg.clone());
                            } else {
                                return Err("multiple file unsupported".to_string());
                            }
                        }
                    }
                }
                Ok(CmdArgs::Interp(args))
            }
            Some(name) if name == "typechk" => {
                let mut args = TypeChkCmdArgs {
                    all: false,
                    annot: None,
                    debug: false,
                    filenames: Vec::new(),
                    verbose: false,
                };
                while let Some(arg) = &argp.next() {
                    match arg.as_ref() {
                        "--" => {}
                        "--all" => args.all = true,
                        "--annot" => match args.annot {
                            Some(_) => return Err("multiple annot specified".to_string()),
                            None => args.annot = argp.next(),
                        },
                        "--debug" => args.debug = true,
                        "--verbose" => args.verbose = true,
                        arg if arg.starts_with("--") => {
                            return Err(format!("unknown typechk option: {}", arg))
                        }
                        _ => args.filenames.push(arg.clone()),
                    }
                }
                Ok(CmdArgs::TypeChk(args))
            }
            Some(name) => Err(format!("unknown command: {}", name)),
            None => Err("specify command".to_string()),
        }
    }
}

fn read_file(filename: &str) -> Result<String, String> {
    match fs::read_to_string(filename) {
        Ok(s) => Ok(s),
        Err(err) => Err(format!("{}: {}", filename, err)),
    }
}

fn load_module_from_file(filename: &str, log: bool) -> Result<Module<ExtIdent>, String> {
    if log {
        eprintln!("loading module {} ...", filename);
    }
    Module::parse(&read_file(filename)?, filename)
}

fn load_annotfile(filename: String, log: bool) -> Result<annot::AnnotFile, String> {
    if log {
        eprintln!("loading annotation {} ...", filename);
    }
    annot::AnnotFile::parse(&read_file(&filename)?, filename)
}

fn interp(args: &InterpCmdArgs) -> Result<(), String> {
    let mut interp = match &args.filename {
        Some(filename) => {
            let module = load_module_from_file(filename, args.verbose)?;
            let datalayout = module.target_datalayout().clone();
            let mut typedefs = module.typedefs().clone();
            if let Some(annotname) = &args.annot {
                let annot = load_annotfile(String::from(annotname), args.verbose)?;
                annot.rewrite_typedefs(&mut typedefs, &datalayout)?;
            }
            let mut interp = interp::Interp::new(datalayout, typedefs);
            for (funcname, (funcdecl, blocks)) in module.funcs() {
                if args.verbose {
                    eprintln!("importing {}", funcdecl.sig);
                }
                let func =
                    interp::syntax::Func::new_with_funcdecl(funcdecl.clone(), blocks.clone());
                if let Err(err) = interp.define_func(*funcname, func) {
                    return Err(format!("define {}: {}", funcname, err));
                }
            }
            interp
        }
        None => interp::Interp::new(DataLayout::lp64(), Typedefs::empty()),
    };
    let entryname = GlobalIdent::from("__cad_entry__");
    let insns = match &args.insns {
        Some(insns) => format!("define void {}() {{ {} }}", entryname, insns),
        None => return Err("specify insns".to_string()),
    };
    let entryfunc = match interp::syntax::Func::try_parse(&insns) {
        Ok(func) => func,
        Err(err) => return Err(format!("malformed insns: {}", err)),
    };
    if let Err(err) = interp.define_func(entryname, entryfunc) {
        return Err(format!("define __cad_entry__: {}", err));
    }
    if let Err(err) = interp.start(entryname) {
        return Err(format!("start: {}", err));
    }
    loop {
        let state = interp.state().clone();
        if let interp::syntax::State::Finished(_) = state {
            eprintln!("{}", state);
            return Ok(());
        }
        match interp.step() {
            Ok(cont) => eprintln!("{}: {}", state, cont),
            Err(err) => return Err(format!("{}: {}", state, err)),
        }
    }
}

fn typechk(args: &TypeChkCmdArgs) -> Result<(), String> {
    let annotfile = match &args.annot {
        Some(filename) => load_annotfile(String::from(filename), true)?,
        None => annot::AnnotFile::empty(),
    };
    if args.debug {
        eprint!("{}", annotfile);
    }
    for filename in &args.filenames {
        let mut module = load_module_from_file(filename, true)?;
        let datalayout = module.target_datalayout().clone(); // Avoid borrowck.
        annotfile.rewrite_typedefs(module.typedefs_mut(), &datalayout)?;
        let mut typechk = typechk::TypeChk::new(&annotfile, &module)?;
        if let Err(err) = typechk.check_types() {
            for (loc, err) in typechk.errors() {
                eprintln!("error(typechk): {}: {}", loc, err);
            }
            eprintln!("{}", err);
            return Ok(());
        }
        if !annotfile.is_empty() {
            if let Err(err) = typechk.check_casts() {
                eprintln!("{}: {}", typechk.annotfile().filename(), err);
                return Ok(());
            }
        }
        let report = typechk.report();
        if !annotfile.is_empty() {
            eprintln!("typechk(cast):");
            for warn in &report.castwarns {
                if args.verbose || !warn.msg.is_valid() {
                    match args.debug {
                        true => eprintln!("  {:?}", warn),
                        false => eprintln!("  {}", warn),
                    }
                }
            }
            eprintln!("  {}", report.summarize_castwarns());
        }
        if args.all {
            eprintln!("typechk:");
            for warn in &report.typewarns {
                match args.debug {
                    true => eprintln!("  {:?}", warn),
                    false => eprintln!("  {}", warn),
                }
            }
            eprintln!("  {}", report.summarize_typewarns());
        }
        if args.verbose {
            eprintln!(
                "  typeset: {}",
                DisplayMapIter("[", typechk.env().typeset().iter(), " -> ", ", ", "]")
            );
            eprintln!(
                "  varset: {}",
                DisplayMapIter("[", typechk.env().varset().iter(), " -> ", ", ", "]")
            );
            eprintln!("  effectset:");
            for (loc, effect) in typechk.env().effectset() {
                eprintln!("    {}: {}", loc.with_lineinfo(typechk.module()), effect);
            }
        }
    }
    Ok(())
}

fn start() -> Result<(), String> {
    match CmdArgs::parse(&mut env::args().skip(1))? {
        CmdArgs::Interp(args) => interp(&args),
        CmdArgs::TypeChk(args) => typechk(&args),
    }
}

fn main() {
    if let Err(err) = start() {
        eprintln!("error: {}", err);
        process::exit(1);
    }
}
