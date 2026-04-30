use std::path::PathBuf;

use yulang_core_ir::{Name, Path};
use yulang_source::InlineSource;

pub fn inline_sources() -> impl Iterator<Item = InlineSource> {
    STD_SOURCES.iter().map(|source| InlineSource {
        path: PathBuf::from(format!("<std>/{}.yu", source.name)),
        module_path: module_path(source.name),
        source: source.text.to_string(),
    })
}

struct StdSource {
    name: &'static str,
    text: &'static str,
}

const STD_SOURCES: &[StdSource] = &[
    StdSource {
        name: "flow",
        text: include_str!("../../../lib/std/flow.yu"),
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
