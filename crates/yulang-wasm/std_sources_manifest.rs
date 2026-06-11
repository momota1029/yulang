macro_rules! yulang_std_sources {
    ($prefix:literal) => {
        &[
            StdSource {
                name: "bool",
                text: include_str!(concat!($prefix, "bool.yu")),
            },
            StdSource {
                name: "control",
                text: include_str!(concat!($prefix, "control.yu")),
            },
            StdSource {
                name: "control::flow",
                text: include_str!(concat!($prefix, "control/flow.yu")),
            },
            StdSource {
                name: "control::junction",
                text: include_str!(concat!($prefix, "control/junction.yu")),
            },
            StdSource {
                name: "control::nondet",
                text: include_str!(concat!($prefix, "control/nondet.yu")),
            },
            StdSource {
                name: "control::throw",
                text: include_str!(concat!($prefix, "control/throw.yu")),
            },
            StdSource {
                name: "control::var",
                text: include_str!(concat!($prefix, "control/var.yu")),
            },
            StdSource {
                name: "core",
                text: include_str!(concat!($prefix, "core.yu")),
            },
            StdSource {
                name: "core::cmp",
                text: include_str!(concat!($prefix, "core/cmp.yu")),
            },
            StdSource {
                name: "core::convert",
                text: include_str!(concat!($prefix, "core/convert.yu")),
            },
            StdSource {
                name: "core::fmt",
                text: include_str!(concat!($prefix, "core/fmt.yu")),
            },
            StdSource {
                name: "core::ops",
                text: include_str!(concat!($prefix, "core/ops.yu")),
            },
            StdSource {
                name: "core::seq",
                text: include_str!(concat!($prefix, "core/seq.yu")),
            },
            StdSource {
                name: "data",
                text: include_str!(concat!($prefix, "data.yu")),
            },
            StdSource {
                name: "data::fold",
                text: include_str!(concat!($prefix, "data/fold.yu")),
            },
            StdSource {
                name: "data::index",
                text: include_str!(concat!($prefix, "data/index.yu")),
            },
            StdSource {
                name: "data::list",
                text: include_str!(concat!($prefix, "data/list.yu")),
            },
            StdSource {
                name: "data::opt",
                text: include_str!(concat!($prefix, "data/opt.yu")),
            },
            StdSource {
                name: "data::range",
                text: include_str!(concat!($prefix, "data/range.yu")),
            },
            StdSource {
                name: "data::result",
                text: include_str!(concat!($prefix, "data/result.yu")),
            },
            StdSource {
                name: "float",
                text: include_str!(concat!($prefix, "float.yu")),
            },
            StdSource {
                name: "int",
                text: include_str!(concat!($prefix, "int.yu")),
            },
            StdSource {
                name: "io",
                text: include_str!(concat!($prefix, "io.yu")),
            },
            StdSource {
                name: "io::console",
                text: include_str!(concat!($prefix, "io/console.yu")),
            },
            StdSource {
                name: "io::file",
                text: include_str!(concat!($prefix, "io/file.yu")),
            },
            StdSource {
                name: "num",
                text: include_str!(concat!($prefix, "num.yu")),
            },
            StdSource {
                name: "num::frac",
                text: include_str!(concat!($prefix, "num/frac.yu")),
            },
            StdSource {
                name: "prelude",
                text: include_str!(concat!($prefix, "prelude.yu")),
            },
            StdSource {
                name: "text",
                text: include_str!(concat!($prefix, "text.yu")),
            },
            StdSource {
                name: "text::bytes",
                text: include_str!(concat!($prefix, "text/bytes.yu")),
            },
            StdSource {
                name: "text::char",
                text: include_str!(concat!($prefix, "text/char.yu")),
            },
            StdSource {
                name: "text::parse",
                text: include_str!(concat!($prefix, "text/parse.yu")),
            },
            StdSource {
                name: "text::path",
                text: include_str!(concat!($prefix, "text/path.yu")),
            },
            StdSource {
                name: "text::str",
                text: include_str!(concat!($prefix, "text/str.yu")),
            },
        ]
    };
}
