//! source / `sources::LoadedFile` から `poly` dump までをつなぐ debug 用入口。
//!
//! FS 探索そのものは呼び出し側に置き、この module は集まった `LoadedFile` を infer の
//! module tree と `poly` dump へ接続する。scheme 化はまだ未接続なので、現時点の dump は
//! body / ref resolution / constraint session を見るための debug footing。

use std::fmt::Write as _;

use parser::sink::YulangLanguage;
use poly::expr::{Def, DefId};
use rowan::SyntaxNode;
use sources::{LoadedFile, Path, SourceFile};

use crate::LoadedFilesError;
use crate::lower_module_map;
use crate::lowering::{BodyLowering, BodyLoweringError, lower_binding_bodies, lower_loaded_files};

/// poly dump と、その dump を作った lowering state。
///
/// `text` は `poly::dump` の compact 表現。`lowering` には制約 machine、SCC event、
/// `DefId` 型 slot、dump label が残る。現時点では SCC が出した量化 event を scheme 化して
/// `Def::Let.scheme` へ書き戻す段階はまだない。
pub struct PolyDumpOutput {
    pub text: String,
    pub lowering: BodyLowering,
}

pub struct PolyModuleDumpOutput {
    pub text: String,
    pub lowering: BodyLowering,
    pub defs: Vec<DefId>,
}

/// 複数 loaded files を1つの module tree として lower し、`poly` compact dump を返す。
pub fn dump_loaded_files(files: &[LoadedFile]) -> Result<PolyDumpOutput, LoadedFilesError> {
    let lowering = lower_loaded_files(files)?;
    Ok(dump_lowering(lowering))
}

/// 複数 loaded files を body lowering まで進め、raw poly debug dump を返す。
pub fn dump_loaded_files_raw(files: &[LoadedFile]) -> Result<PolyDumpOutput, LoadedFilesError> {
    let lowering = lower_loaded_files(files)?;
    Ok(dump_lowering_raw(lowering))
}

/// 複数 loaded files を body lowering まで進め、指定 module 直下の値だけを dump する。
pub fn dump_loaded_files_in_module(
    files: &[LoadedFile],
    module_path: &Path,
    raw: bool,
) -> Result<Option<PolyModuleDumpOutput>, LoadedFilesError> {
    let lowering = lower_loaded_files(files)?;
    Ok(dump_lowering_in_module(lowering, module_path, raw))
}

/// 1つの loaded file を lower し、`poly` compact dump を返す。
pub fn dump_loaded_file(file: &LoadedFile) -> PolyDumpOutput {
    let lowering = lower_loaded_file(file);
    dump_lowering(lowering)
}

/// 1つの loaded file を lower し、raw poly debug dump を返す。
pub fn dump_loaded_file_raw(file: &LoadedFile) -> PolyDumpOutput {
    let lowering = lower_loaded_file(file);
    dump_lowering_raw(lowering)
}

/// source 文字列を `sources::load` に通してから dump する。
///
/// module path は root を表す空 path にする。FS 探索や `mod foo;` の追跡はここでは行わない。
pub fn dump_source(source: &str) -> PolyDumpOutput {
    let files = sources::load(vec![SourceFile {
        module_path: Path::default(),
        source: source.to_string(),
    }]);
    let [file] = files.as_slice() else {
        unreachable!("one input source should produce one loaded file");
    };
    dump_loaded_file(file)
}

/// source 文字列を `sources::load` に通してから raw dump する。
pub fn dump_source_raw(source: &str) -> PolyDumpOutput {
    let files = sources::load(vec![SourceFile {
        module_path: Path::default(),
        source: source.to_string(),
    }]);
    let [file] = files.as_slice() else {
        unreachable!("one input source should produce one loaded file");
    };
    dump_loaded_file_raw(file)
}

/// 1つの loaded file を body lowering まで進める。
pub fn lower_loaded_file(file: &LoadedFile) -> BodyLowering {
    let root = SyntaxNode::<YulangLanguage>::new_root(file.cst.clone());
    let lower = lower_module_map(&root);
    lower_binding_bodies(&root, lower)
}

/// 既に作った lowering state を dump text へ変換する。
pub fn dump_lowering(lowering: BodyLowering) -> PolyDumpOutput {
    let text = poly::dump::dump_arena_with_labels(&lowering.session.poly, &lowering.labels);
    PolyDumpOutput { text, lowering }
}

/// 既に作った lowering state を raw dump text へ変換する。
pub fn dump_lowering_raw(lowering: BodyLowering) -> PolyDumpOutput {
    let text = poly::dump::dump_arena_raw_with_labels(&lowering.session.poly, &lowering.labels);
    PolyDumpOutput { text, lowering }
}

/// 既に作った lowering state から、指定 module 直下の値だけを dump text へ変換する。
pub fn dump_lowering_in_module(
    lowering: BodyLowering,
    module_path: &Path,
    raw: bool,
) -> Option<PolyModuleDumpOutput> {
    let (text, defs) = dump_lowering_module_text(&lowering, module_path, raw)?;
    Some(PolyModuleDumpOutput {
        text,
        lowering,
        defs,
    })
}

fn dump_lowering_module_text(
    lowering: &BodyLowering,
    module_path: &Path,
    raw: bool,
) -> Option<(String, Vec<DefId>)> {
    let module = lowering.modules.module_by_path(module_path)?;
    let values = lowering.modules.module_value_decls(module);
    let types = lowering.modules.module_type_decls(module);
    let children = lowering.modules.module_child_decls(module);
    let defs = values.iter().map(|decl| decl.def).collect::<Vec<_>>();
    let summary = module_summary(
        lowering,
        module_path,
        &defs,
        values.len(),
        types.len(),
        children.len(),
    );
    let body = if raw {
        poly::dump::dump_defs_raw_with_labels(&lowering.session.poly, &lowering.labels, &defs)
    } else {
        poly::dump::dump_defs_with_labels(&lowering.session.poly, &lowering.labels, &defs)
    };
    let mut text = summary;
    text.push('\n');
    text.push_str(&body);
    Some((text, defs))
}

fn module_summary(
    lowering: &BodyLowering,
    module_path: &Path,
    defs: &[DefId],
    value_count: usize,
    type_count: usize,
    child_module_count: usize,
) -> String {
    let def_set = defs.iter().copied().collect::<rustc_hash::FxHashSet<_>>();
    let mut typed_lets = 0;
    let mut missing_schemes = 0;
    let mut bodyless_decls = 0;
    let mut dirty_stack_schemes = 0;
    for def in defs {
        match lowering.session.poly.defs.get(*def) {
            Some(Def::Let { scheme, body, .. }) => {
                if let Some(scheme) = scheme {
                    typed_lets += 1;
                    if poly::dump::format_scheme(&lowering.session.poly.typ, scheme)
                        .contains("stack(")
                    {
                        dirty_stack_schemes += 1;
                    }
                } else {
                    missing_schemes += 1;
                }
                if body.is_none() {
                    bodyless_decls += 1;
                }
            }
            Some(Def::Mod { .. }) | Some(Def::Arg) | None => {
                missing_schemes += 1;
                bodyless_decls += 1;
            }
        }
    }
    let local_errors = lowering
        .errors
        .iter()
        .filter(|error| body_error_def(error).is_some_and(|def| def_set.contains(&def)))
        .count();

    let mut out = String::new();
    let _ = writeln!(out, "module {}", format_path(module_path));
    let _ = writeln!(out, "values: {value_count}");
    let _ = writeln!(out, "types: {type_count}");
    let _ = writeln!(out, "child modules: {child_module_count}");
    let _ = writeln!(out, "typed lets: {typed_lets}");
    let _ = writeln!(out, "missing schemes: {missing_schemes}");
    let _ = writeln!(out, "bodyless declarations: {bodyless_decls}");
    let _ = writeln!(out, "dirty stack schemes: {dirty_stack_schemes}");
    let _ = writeln!(
        out,
        "lowering errors: {local_errors} local / {} total",
        lowering.errors.len()
    );
    out
}

pub fn body_error_def(error: &BodyLoweringError) -> Option<DefId> {
    match error {
        BodyLoweringError::MissingBindingDecl { .. }
        | BodyLoweringError::MissingModuleDecl { .. }
        | BodyLoweringError::RootExpr { .. } => None,
        BodyLoweringError::MissingBody { def, .. }
        | BodyLoweringError::NonLetDef { def, .. }
        | BodyLoweringError::Expr { def, .. } => Some(*def),
        BodyLoweringError::Analysis(error) => error.primary_def(),
    }
}

fn format_path(path: &Path) -> String {
    if path.segments.is_empty() {
        return "<root>".to_string();
    }
    path.segments
        .iter()
        .map(|segment| segment.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn path(segments: &[&str]) -> Path {
        Path {
            segments: segments
                .iter()
                .map(|s| sources::Name((*s).into()))
                .collect(),
        }
    }

    #[test]
    fn dumps_single_source_with_def_and_ref_labels() {
        let output = dump_source("my a = 1\nmy b = a\n");

        assert_eq!(output.lowering.errors, Vec::new());
        assert_eq!(
            output.text,
            "roots d0:a d1:b\nmy d0:a: int = e0:1\nmy d1:b: int = e1:r0:a->d0:a\n"
        );
    }

    #[test]
    fn dumps_loaded_files_as_connected_module_tree() {
        let files = sources::load(vec![
            SourceFile {
                module_path: path(&[]),
                source: "mod foo;\nmy x = 1\n".into(),
            },
            SourceFile {
                module_path: path(&["foo"]),
                source: "my y = 2\n".into(),
            },
        ]);
        let output = dump_loaded_files(&files).unwrap();

        assert_eq!(output.lowering.errors, Vec::new());
        assert_eq!(
            output.text,
            "roots d0:foo d1:x\nd0:foo mod {\n  my d2:\"foo.y\": int = e1:2\n}\nmy d1:x: int = e0:1\n"
        );
    }

    #[test]
    fn lowers_infix_op_def_and_use() {
        let output = dump_source("pub infix (+) 5.0.0 5.0.1 = \\x -> \\y -> x\nmy a = 1 + 2\n");

        assert_eq!(output.lowering.errors, Vec::new());
        assert!(output.text.contains("\"#op:infix:+\""), "{}", output.text);
        assert!(output.text.contains("my d1:a: int"), "{}", output.text);
    }

    #[test]
    fn lowers_lazy_infix_op_with_thunked_operands() {
        let output =
            dump_source("pub lazy infix(also) 2.0.0 2.0.1 = \\a -> \\b -> b()\nmy x = 1 also 2\n");

        assert_eq!(output.lowering.errors, Vec::new());
        // 被演算子が `\() -> ...` thunk に包まれ、結果は本体 `b()` の戻り＝ int になる。
        assert!(output.text.contains("my d1:x: int"), "{}", output.text);
        assert!(
            output.text.contains("(fn p2:() -> e5:1)"),
            "{}",
            output.text
        );
        assert!(
            output.text.contains("(fn p3:() -> e7:2)"),
            "{}",
            output.text
        );
    }

    #[test]
    fn lowers_nullfix_op_as_thunked_def_and_unit_application() {
        let output = dump_source("pub nullfix(zero) = 1\nmy a = zero\n");

        assert_eq!(output.lowering.errors, Vec::new());
        // def 側は thunk 化され、use site は unit 適用で評価される。
        assert!(
            output.text.contains("\"#op:nullfix:zero\": () -> int"),
            "{}",
            output.text
        );
        assert!(output.text.contains("my d1:a: int"), "{}", output.text);
    }

    #[test]
    fn lowers_prefix_and_suffix_op_uses() {
        let output = dump_source(
            "pub prefix (-) 8.0.0 = \\x -> x\npub suffix (?!) 8.0.0 = \\x -> x\nmy a = -1\nmy b = 2?!\n",
        );

        assert_eq!(output.lowering.errors, Vec::new());
        assert!(output.text.contains("my d2:a: int"), "{}", output.text);
        assert!(output.text.contains("my d3:b: int"), "{}", output.text);
    }

    #[test]
    fn dumps_use_mod_loaded_file_as_module_tree() {
        let files = sources::load(vec![
            SourceFile {
                module_path: path(&[]),
                source: "use mod foo::*\n".into(),
            },
            SourceFile {
                module_path: path(&["foo"]),
                source: "my y = 2\n".into(),
            },
        ]);
        let output = dump_loaded_files(&files).unwrap();

        assert_eq!(output.lowering.errors, Vec::new());
        assert_eq!(
            output.text,
            "roots d0:foo\nd0:foo mod {\n  my d1:\"foo.y\": int = e0:2\n}\n"
        );
    }
}
