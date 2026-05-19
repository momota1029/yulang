macro_rules! yulang_std_sources {
    ($prefix:literal) => {
        &[
            StdSource {
                name: "bytes",
                text: include_str!(concat!($prefix, "bytes.yu")),
            },
            StdSource {
                name: "char",
                text: include_str!(concat!($prefix, "char.yu")),
            },
            StdSource {
                name: "error",
                text: include_str!(concat!($prefix, "error.yu")),
            },
            StdSource {
                name: "flow",
                text: include_str!(concat!($prefix, "flow.yu")),
            },
            StdSource {
                name: "fs",
                text: include_str!(concat!($prefix, "fs.yu")),
            },
            StdSource {
                name: "fold",
                text: include_str!(concat!($prefix, "fold.yu")),
            },
            StdSource {
                name: "index",
                text: include_str!(concat!($prefix, "index.yu")),
            },
            StdSource {
                name: "junction",
                text: include_str!(concat!($prefix, "junction.yu")),
            },
            StdSource {
                name: "list",
                text: include_str!(concat!($prefix, "list.yu")),
            },
            StdSource {
                name: "opt",
                text: include_str!(concat!($prefix, "opt.yu")),
            },
            StdSource {
                name: "ops",
                text: include_str!(concat!($prefix, "ops.yu")),
            },
            StdSource {
                name: "out",
                text: include_str!(concat!($prefix, "out.yu")),
            },
            StdSource {
                name: "path",
                text: include_str!(concat!($prefix, "path.yu")),
            },
            StdSource {
                name: "parse",
                text: include_str!(concat!($prefix, "parse.yu")),
            },
            StdSource {
                name: "prelude",
                text: include_str!(concat!($prefix, "prelude.yu")),
            },
            StdSource {
                name: "range",
                text: include_str!(concat!($prefix, "range.yu")),
            },
            StdSource {
                name: "result",
                text: include_str!(concat!($prefix, "result.yu")),
            },
            StdSource {
                name: "str",
                text: include_str!(concat!($prefix, "str.yu")),
            },
            StdSource {
                name: "undet",
                text: include_str!(concat!($prefix, "undet.yu")),
            },
            StdSource {
                name: "var",
                text: include_str!(concat!($prefix, "var.yu")),
            },
        ]
    };
}
