//! source / `sources::LoadedFile` から `poly` dump までをつなぐ debug 用入口。
//!
//! FS 探索そのものは呼び出し側に置き、この module は集まった `LoadedFile` を infer の
//! module tree と `poly` dump へ接続する。scheme 化はまだ未接続なので、現時点の dump は
//! body / ref resolution / constraint session を見るための debug footing。

use rowan::SyntaxNode;
use sources::{LoadedFile, Path, SourceFile};
use yulang_parser::sink::YulangLanguage;

use crate::LoadedFilesError;
use crate::lower_module_map;
use crate::lowering::{BodyLowering, lower_binding_bodies, lower_loaded_files};

/// poly dump と、その dump を作った lowering state。
///
/// `text` は `poly::dump` の compact 表現。`lowering` には制約 machine、SCC event、
/// `DefId` 型 slot、dump label が残る。現時点では SCC が出した量化 event を scheme 化して
/// `Def::Let.scheme` へ書き戻す段階はまだない。
pub struct PolyDumpOutput {
    pub text: String,
    pub lowering: BodyLowering,
}

/// 複数 loaded files を1つの module tree として lower し、`poly` compact dump を返す。
pub fn dump_loaded_files(files: &[LoadedFile]) -> Result<PolyDumpOutput, LoadedFilesError> {
    let lowering = lower_loaded_files(files)?;
    Ok(dump_lowering(lowering))
}

/// 1つの loaded file を lower し、`poly` compact dump を返す。
pub fn dump_loaded_file(file: &LoadedFile) -> PolyDumpOutput {
    let lowering = lower_loaded_file(file);
    dump_lowering(lowering)
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
            "roots d0:a d1:b\nmy d0:a = e0:1\nmy d1:b = e1:r0:a->d0:a\n"
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
            "roots d0:foo d1:x\nd0:foo mod {\n  my d2:\"foo.y\" = e1:2\n}\nmy d1:x = e0:1\n"
        );
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
            "roots d0:foo\nd0:foo mod {\n  my d1:\"foo.y\" = e0:2\n}\n"
        );
    }
}
