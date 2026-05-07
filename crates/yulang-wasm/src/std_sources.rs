use std::path::PathBuf;
use std::sync::OnceLock;

use yulang_core_ir::{Name, Path};
use yulang_source::{
    InlineSource, SourceOptions, SourceOrigin, SourceSet, collect_inline_source_files_with_options,
    parse_source_meta,
};

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

const STD_SOURCES: &[StdSource] = &[
    StdSource {
        name: "console",
        text: include_str!("../../../lib/std/console.yu"),
    },
    StdSource {
        name: "error",
        text: include_str!("../../../lib/std/error.yu"),
    },
    StdSource {
        name: "flow",
        text: include_str!("../../../lib/std/flow.yu"),
    },
    StdSource {
        name: "fs",
        text: include_str!("../../../lib/std/fs.yu"),
    },
    StdSource {
        name: "fold",
        text: include_str!("../../../lib/std/fold.yu"),
    },
    StdSource {
        name: "index",
        text: include_str!("../../../lib/std/index.yu"),
    },
    StdSource {
        name: "junction",
        text: include_str!("../../../lib/std/junction.yu"),
    },
    StdSource {
        name: "list",
        text: include_str!("../../../lib/std/list.yu"),
    },
    StdSource {
        name: "opt",
        text: include_str!("../../../lib/std/opt.yu"),
    },
    StdSource {
        name: "ops",
        text: include_str!("../../../lib/std/ops.yu"),
    },
    StdSource {
        name: "prelude",
        text: include_str!("../../../lib/std/prelude.yu"),
    },
    StdSource {
        name: "range",
        text: include_str!("../../../lib/std/range.yu"),
    },
    StdSource {
        name: "str",
        text: include_str!("../../../lib/std/str.yu"),
    },
    StdSource {
        name: "undet",
        text: include_str!("../../../lib/std/undet.yu"),
    },
    StdSource {
        name: "var",
        text: include_str!("../../../lib/std/var.yu"),
    },
];

fn module_path(name: &str) -> Path {
    Path {
        segments: vec![Name("std".to_string()), Name(name.to_string())],
    }
}
