use std::env;
use std::fs;
use std::path::{Path as FsPath, PathBuf};

use yulang_core_ir::{Name, Path};
use yulang_source::{
    InlineSource, SourceOptions, SourceOrigin, collect_inline_source_files_with_options,
    parse_source_meta,
};

fn main() {
    println!("cargo:rerun-if-changed=../../lib/std");

    let source_set = std_source_set();
    let lowered = yulang_infer::lower_source_set(&source_set);
    let artifacts = yulang_infer::build_compiled_unit_artifacts(&source_set, &lowered.state);
    let out_dir = PathBuf::from(env::var_os("OUT_DIR").expect("OUT_DIR should be set"));
    let path = out_dir.join("std_compiled_unit_artifacts.json");
    let json = serde_json::to_string(&artifacts).expect("serialize std compiled unit artifacts");
    fs::write(path, json).expect("write std compiled unit artifacts");
}

fn std_source_set() -> yulang_source::SourceSet {
    let source = STD_SOURCES
        .iter()
        .map(|source| format!("use std::{}::*\n", source.name))
        .collect::<String>();
    collect_inline_source_files_with_options(
        &source,
        STD_SOURCES.iter().map(|source| {
            let source_text = source.text.to_string();
            InlineSource {
                path: FsPath::new("<std>").join(format!("{}.yu", source.name)),
                module_path: module_path(source.name),
                origin: SourceOrigin::Std,
                meta: Some(parse_source_meta(&source_text)),
                source: source_text,
            }
        }),
        SourceOptions {
            std_root: None,
            implicit_prelude: true,
            search_paths: Vec::new(),
        },
    )
}

fn module_path(name: &str) -> Path {
    Path {
        segments: vec![Name("std".to_string()), Name(name.to_string())],
    }
}

struct StdSource {
    name: &'static str,
    text: &'static str,
}

const STD_SOURCES: &[StdSource] = &[
    StdSource {
        name: "console",
        text: include_str!("../../lib/std/console.yu"),
    },
    StdSource {
        name: "flow",
        text: include_str!("../../lib/std/flow.yu"),
    },
    StdSource {
        name: "fs",
        text: include_str!("../../lib/std/fs.yu"),
    },
    StdSource {
        name: "fold",
        text: include_str!("../../lib/std/fold.yu"),
    },
    StdSource {
        name: "index",
        text: include_str!("../../lib/std/index.yu"),
    },
    StdSource {
        name: "junction",
        text: include_str!("../../lib/std/junction.yu"),
    },
    StdSource {
        name: "list",
        text: include_str!("../../lib/std/list.yu"),
    },
    StdSource {
        name: "opt",
        text: include_str!("../../lib/std/opt.yu"),
    },
    StdSource {
        name: "prelude",
        text: include_str!("../../lib/std/prelude.yu"),
    },
    StdSource {
        name: "range",
        text: include_str!("../../lib/std/range.yu"),
    },
    StdSource {
        name: "str",
        text: include_str!("../../lib/std/str.yu"),
    },
    StdSource {
        name: "undet",
        text: include_str!("../../lib/std/undet.yu"),
    },
    StdSource {
        name: "var",
        text: include_str!("../../lib/std/var.yu"),
    },
];
