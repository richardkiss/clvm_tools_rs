use std::borrow::Borrow;
use std::collections::HashMap;
use std::rc::Rc;

use clvmr::allocator::Allocator;

use crate::classic::clvm::__type_compatibility__::{Bytes, BytesFromType};
use crate::classic::clvm_tools::clvmc::compile_clvm_text;

use crate::compiler::cldb::hex_to_modern_sexp;
use crate::compiler::clvm::convert_from_clvm_rs;
use crate::compiler::compiler::KNOWN_DIALECTS;
use crate::compiler::comptypes::{CompileErr, CompilerOpts};
use crate::compiler::runtypes::RunFailure;
use crate::compiler::sexp::{decode_string, enlist, parse_sexp, SExp};
use crate::compiler::srcloc::Srcloc;

#[derive(Clone, Debug, PartialEq, Eq)]
enum IncludeProcessType {
    Bin,
    Hex,
    SExpression,
    Compiled,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum IncludeType {
    Basic(Vec<u8>),
    Processed(Vec<u8>, IncludeProcessType, Vec<u8>),
}

pub fn process_include(
    opts: Rc<dyn CompilerOpts>,
    name: &str,
) -> Result<Vec<Rc<SExp>>, CompileErr> {
    let filename_and_content = opts.read_new_file(opts.filename(), name.to_string())?;
    let content = filename_and_content.1;

    let start_of_file = Srcloc::start(name);

    parse_sexp(start_of_file.clone(), &decode_string(&content))
        .map_err(|e| CompileErr(e.0.clone(), e.1))
        .and_then(|x| match x[0].proper_list() {
            None => Err(CompileErr(
                start_of_file,
                "Includes should contain a list of forms".to_string(),
            )),
            Some(v) => {
                let res: Vec<Rc<SExp>> = v.iter().map(|x| Rc::new(x.clone())).collect();
                Ok(res)
            }
        })
}

fn compose_defconst(loc: Srcloc, name: &[u8], sexp: Rc<SExp>) -> Rc<SExp> {
    Rc::new(enlist(
        loc.clone(),
        &[
            Rc::new(SExp::Atom(loc.clone(), b"defconst".to_vec())),
            Rc::new(SExp::Atom(loc.clone(), name.to_vec())),
            Rc::new(SExp::Cons(
                loc.clone(),
                Rc::new(SExp::Atom(loc, vec![1])),
                sexp,
            )),
        ],
    ))
}

fn process_embed(
    loc: Srcloc,
    opts: Rc<dyn CompilerOpts>,
    fname: &str,
    kind: IncludeProcessType,
    constant_name: &[u8],
) -> Result<Vec<Rc<SExp>>, CompileErr> {
    let mut allocator = Allocator::new();
    let run_to_compile_err = |e| match e {
        RunFailure::RunExn(l, x) => CompileErr(
            l,
            format!(
                "failed to convert compiled clvm to expression: throw ({})",
                x
            ),
        ),
        RunFailure::RunErr(l, e) => CompileErr(
            l,
            format!("failed to convert compiled clvm to expression: {}", e),
        ),
    };

    let (full_name, content) = opts.read_new_file(opts.filename(), fname.to_string())?;
    let content = match kind {
        IncludeProcessType::Bin => Rc::new(SExp::Atom(loc.clone(), content)),
        IncludeProcessType::Hex => hex_to_modern_sexp(
            &mut allocator,
            &HashMap::new(),
            loc.clone(),
            &decode_string(&content),
        )
        .map_err(run_to_compile_err)?,
        IncludeProcessType::SExpression => {
            let parsed = parse_sexp(Srcloc::start(&full_name), &decode_string(&content))
                .map_err(|e| CompileErr(e.0, e.1))?;
            if parsed.len() != 1 {
                return Err(CompileErr(loc, format!("More than one form in {}", fname)));
            }

            parsed[0].clone()
        }
        IncludeProcessType::Compiled => {
            let mut symtab = HashMap::new();
            let newly_compiled = compile_clvm_text(
                &mut allocator,
                &opts.get_search_paths(),
                &mut symtab,
                &decode_string(&content),
                &full_name,
            )
            .map_err(|e| CompileErr(loc.clone(), format!("Subcompile failed: {}", e.1)))?;
            convert_from_clvm_rs(&mut allocator, loc.clone(), newly_compiled)
                .map_err(run_to_compile_err)?
        }
    };

    Ok(vec![compose_defconst(loc, constant_name, content)])
}

/* Expand include inline in forms */
fn process_pp_form(
    opts: Rc<dyn CompilerOpts>,
    body: Rc<SExp>,
    dependencies: bool, // Only export dependencies
) -> Result<Vec<Rc<SExp>>, CompileErr> {
    // Support using the preprocessor to collect dependencies recursively.
    let recurse_dependencies = |opts: Rc<dyn CompilerOpts>, fname: &str| {
        if KNOWN_DIALECTS.contains_key(&fname.to_string()) {
            return Ok(vec![]);
        }

        let (full_name, content) = opts.read_new_file(opts.filename(), fname.to_string())?;
        let parsed = parse_sexp(Srcloc::start(&full_name), &decode_string(&content))
            .map_err(|e| CompileErr(e.0, e.1))?;
        if parsed.is_empty() {
            return Ok(vec![]);
        }

        let program_form = parsed[0].clone();
        let mut dep_res = vec![Rc::new(SExp::atom_from_string(parsed[0].loc(), &full_name))];
        if let Some(l) = program_form.proper_list() {
            for elt in l.iter() {
                let mut new_deps = process_pp_form(opts.clone(), Rc::new(elt.clone()), true)?;
                dep_res.append(&mut new_deps);
            }
        }

        Ok(dep_res)
    };

    let include_type: Option<IncludeType> = body
        .proper_list()
        .map(|x| x.iter().map(|elt| elt.atomize()).collect())
        .map(|x: Vec<SExp>| {
            match &x[..] {
                [SExp::Atom(_, inc), SExp::Atom(_, fname)] => {
                    if inc == b"include" {
                        return Ok(Some(IncludeType::Basic(fname.clone())));
                    }
                }

                [SExp::Atom(_, compile_file), SExp::Atom(_, name), SExp::Atom(_, fname)] => {
                    if compile_file == b"compile-file" {
                        return Ok(Some(IncludeType::Processed(
                            fname.clone(),
                            IncludeProcessType::Compiled,
                            name.clone()
                        )));
                    }
                }

                [SExp::Atom(_, embed_file), SExp::Atom(_, name), SExp::Atom(_, kind), SExp::Atom(_, fname)] => {
                    if embed_file == b"embed-file" {
                        if kind == b"hex" {
                            return Ok(Some(IncludeType::Processed(
                                fname.clone(),
                                IncludeProcessType::Hex,
                                name.clone()
                            )));
                        } else if kind == b"bin" {
                            return Ok(Some(IncludeType::Processed(
                                fname.clone(),
                                IncludeProcessType::Bin,
                                name.clone()
                            )));
                        } else if kind == b"sexp" {
                            return Ok(Some(IncludeType::Processed(
                                fname.clone(),
                                IncludeProcessType::SExpression,
                                name.clone()
                            )));
                        } else {
                            return Err(CompileErr(
                                body.loc(),
                                format!("bad include kind in embed-file {}", body)
                            ));
                        }
                    }
                }

                [] => {}

                // Ensure that legal empty or atom expressions don't try include
                _ => {
                    // Include is only allowed as a proper form.  It's a keyword in
                    // this language.
                    if let SExp::Atom(_, inc) = &x[0] {
                        if inc == b"include" {
                            return Err(CompileErr(
                                body.loc(),
                                format!("bad tail in include {}", body),
                            ));
                        }
                    }
                }
            }

            Ok(None)
        })
        .unwrap_or_else(|| Ok(None))?;

    match include_type {
        Some(IncludeType::Basic(f)) => {
            if dependencies {
                recurse_dependencies(opts, &decode_string(&f))
            } else {
                process_include(
                    opts,
                    &Bytes::new(Some(BytesFromType::Raw(f.to_vec()))).decode(),
                )
            }
        }
        Some(IncludeType::Processed(f, kind, name)) => {
            if dependencies {
                if kind == IncludeProcessType::Compiled {
                    recurse_dependencies(opts, &decode_string(&f))
                } else {
                    Ok(vec![])
                }
            } else {
                process_embed(
                    body.loc(),
                    opts,
                    &Bytes::new(Some(BytesFromType::Raw(f.to_vec()))).decode(),
                    kind,
                    &name,
                )
            }
        }
        _ => {
            if dependencies {
                Ok(vec![])
            } else {
                Ok(vec![body])
            }
        }
    }
}

fn preprocess_(opts: Rc<dyn CompilerOpts>, body: Rc<SExp>) -> Result<Vec<Rc<SExp>>, CompileErr> {
    match body.borrow() {
        SExp::Cons(_, head, rest) => match rest.borrow() {
            SExp::Nil(_nl) => process_pp_form(opts, head.clone(), false),
            _ => {
                let lst = process_pp_form(opts.clone(), head.clone(), false)?;
                let mut rs = preprocess_(opts, rest.clone())?;
                let mut result = lst;
                result.append(&mut rs);
                Ok(result)
            }
        },
        _ => Ok(vec![body]),
    }
}

fn inject_std_macros(body: Rc<SExp>) -> SExp {
    match body.proper_list() {
        Some(v) => {
            let include_form = Rc::new(SExp::Cons(
                body.loc(),
                Rc::new(SExp::atom_from_string(body.loc(), "include")),
                Rc::new(SExp::Cons(
                    body.loc(),
                    Rc::new(SExp::quoted_from_string(body.loc(), "*macros*")),
                    Rc::new(SExp::Nil(body.loc())),
                )),
            ));
            let mut v_clone: Vec<Rc<SExp>> = v.iter().map(|x| Rc::new(x.clone())).collect();
            let include_copy: &SExp = include_form.borrow();
            v_clone.insert(0, Rc::new(include_copy.clone()));
            enlist(body.loc(), &v_clone)
        }
        _ => {
            let body_clone: &SExp = body.borrow();
            body_clone.clone()
        }
    }
}

pub fn preprocess(opts: Rc<dyn CompilerOpts>, cmod: Rc<SExp>) -> Result<Vec<Rc<SExp>>, CompileErr> {
    let tocompile = if opts.stdenv() {
        let injected = inject_std_macros(cmod);
        Rc::new(injected)
    } else {
        cmod
    };

    preprocess_(opts, tocompile)
}

// Visit all files used during compilation.
pub fn gather_dependencies(
    opts: Rc<dyn CompilerOpts>,
    real_input_path: &str,
    file_content: &str,
) -> Result<Vec<String>, CompileErr> {
    let mut result_deps = Vec::new();
    let loc = Srcloc::start(real_input_path);

    let parsed = parse_sexp(loc.clone(), file_content).map_err(|e| CompileErr(e.0, e.1))?;

    if parsed.is_empty() {
        return Ok(vec![]);
    }

    let mut result_elts = Vec::new();
    if let Some(l) = parsed[0].proper_list() {
        for elt in l.iter() {
            let mut new_deps = process_pp_form(opts.clone(), Rc::new(elt.clone()), true)?;
            result_elts.append(&mut new_deps);
        }
    } else {
        return Err(CompileErr(loc, "malformed list body".to_string()));
    };

    for e in result_elts.iter().map(|e| e.atomize()) {
        if let SExp::Atom(_, a) = e {
            result_deps.push(decode_string(&a));
        }
    }

    Ok(result_deps)
}
