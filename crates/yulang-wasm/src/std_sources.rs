use std::path::PathBuf;
use std::sync::OnceLock;

use yulang_sources::{
    InlineSource, SourceOptions, SourceOrigin, SourceSet, collect_inline_source_files_with_options,
    parse_source_meta,
};
use yulang_typed_ir::{Name, Path};

pub fn source_set(source: &str) -> SourceSet {
    collect_inline_source_files_with_options(
        source,
        inline_sources(),
        SourceOptions {
            std_root: None,
            implicit_prelude: true,
            search_paths: Vec::new(),
        },
    )
}

pub fn warm_source_set() -> SourceSet {
    let source = STD_SOURCES
        .iter()
        .map(|source| format!("use std::{}::*\n", source.name))
        .collect::<String>();
    source_set(&source)
}

pub fn inline_sources() -> impl Iterator<Item = InlineSource> {
    cached_inline_sources().iter().cloned()
}

fn cached_inline_sources() -> &'static [InlineSource] {
    static SOURCES: OnceLock<Vec<InlineSource>> = OnceLock::new();
    SOURCES
        .get_or_init(|| {
            STD_SOURCES
                .iter()
                .map(|source| {
                    let source_text = source.text.to_string();
                    InlineSource {
                        path: PathBuf::from(format!("<std>/{}.yu", source.name)),
                        module_path: module_path(source.name),
                        origin: SourceOrigin::Std,
                        meta: Some(parse_source_meta(&source_text)),
                        source: source_text,
                    }
                })
                .collect()
        })
        .as_slice()
}

struct StdSource {
    name: &'static str,
    text: &'static str,
}

include!("../std_sources_manifest.rs");

const STD_SOURCES: &[StdSource] = yulang_std_sources!("../../../lib/std/");

fn module_path(name: &str) -> Path {
    Path {
        segments: vec![Name("std".to_string()), Name(name.to_string())],
    }
}
