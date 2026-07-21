use super::*;
use poly::expr::CastRuleKind;

#[test]
fn missing_ordinary_cast_boundaries_currently_pass_lowering_and_check() {
    let cases = [
        ("struct-field", "struct S { x: bool }\nS { x: 42 }\n"),
        ("function-result", "my f(): bool = 42\nf()\n"),
    ];

    for (name, source) in cases {
        let mut output = lower_source(source);

        assert!(output.errors.is_empty(), "{name}: {:?}", output.errors);
        assert!(
            output.session.take_diagnostics().is_empty(),
            "{name}: current check should accept the missing cast"
        );
        assert!(
            output
                .session
                .casts
                .candidates(&["int".into()], &["bool".into()])
                .is_empty(),
            "{name}: no int-to-bool declaration should be synthesized"
        );
        assert!(output.session.poly.cast_rules.iter().all(|rule| {
            rule.kind != CastRuleKind::Value
                || rule.source != ["int".to_string()]
                || rule.target != ["bool".to_string()]
        }));

        // Future oracle: Missing. OCAST-F should reject this already-required int -> bool
        // boundary; the general function-result shape audit remains outside this witness.
    }
}

#[test]
fn source_local_cast_registries_have_cardinality_parity() {
    let declarations = [
        "",
        "pub cast(x: int): target = target { value: x }\n",
        concat!(
            "pub cast(x: int): target = target { value: x }\n",
            "pub cast(x: int): target = target { value: x }\n",
        ),
    ];

    for (expected_count, declarations) in declarations.into_iter().enumerate() {
        let output = lower_source(&format!("struct target {{ value: int }}\n{declarations}"));
        let source = ["int".to_string()];
        let target = ["target".to_string()];
        let infer_candidates = output.session.casts.candidates(&source, &target);
        let poly_candidates = output
            .session
            .poly
            .cast_rules
            .iter()
            .filter(|rule| {
                rule.kind == CastRuleKind::Value && rule.source == source && rule.target == target
            })
            .collect::<Vec<_>>();

        assert_eq!(infer_candidates.len(), expected_count);
        assert_eq!(poly_candidates.len(), expected_count);
        assert_eq!(
            infer_candidates
                .iter()
                .map(|rule| poly::dump::format_scheme(&output.session.poly.typ, &rule.scheme))
                .collect::<Vec<_>>(),
            poly_candidates
                .iter()
                .map(|rule| poly::dump::format_scheme(&output.session.poly.typ, &rule.scheme))
                .collect::<Vec<_>>()
        );

        // Future oracle by expected_count: 0 = Missing, 1 = Unique, 2 = Ambiguous. The two
        // registries must feed the future adapters the same declaration cardinality.
    }
}

#[test]
fn repository_std_value_cast_pairs_are_each_unique_in_both_registries() {
    let output = lower_repository_std();
    let expected_pairs = [
        (
            vec!["std".into(), "text".into(), "path".into(), "path".into()],
            vec!["std".into(), "text".into(), "bytes".into(), "bytes".into()],
        ),
        (
            vec!["int".to_string()],
            vec!["std".into(), "num".into(), "frac".into(), "frac".into()],
        ),
        (vec!["int".to_string()], vec!["float".to_string()]),
        (
            vec!["std".into(), "num".into(), "frac".into(), "frac".into()],
            vec!["float".to_string()],
        ),
    ];
    let value_rules = output
        .session
        .poly
        .cast_rules
        .iter()
        .filter(|rule| rule.kind == CastRuleKind::Value)
        .collect::<Vec<_>>();

    assert_eq!(value_rules.len(), expected_pairs.len());
    for (source, target) in expected_pairs {
        assert_eq!(
            output.session.casts.candidates(&source, &target).len(),
            1,
            "missing infer pair {source:?} -> {target:?}; durable pairs: {:?}",
            value_rules
                .iter()
                .map(|rule| (&rule.source, &rule.target))
                .collect::<Vec<_>>()
        );
        assert_eq!(
            value_rules
                .iter()
                .filter(|rule| rule.source == source && rule.target == target)
                .count(),
            1
        );

        // Future oracle: Unique. These are the four real-std compatibility canaries for OCAST-F/G.
    }
}

fn lower_source(source: &str) -> BodyLowering {
    let root = parse(source);
    let lower = lower_module_map(&root);
    lower_binding_bodies(&root, lower)
}

fn lower_repository_std() -> BodyLowering {
    fn collect_yu_files(directory: &std::path::Path, files: &mut Vec<std::path::PathBuf>) {
        for entry in std::fs::read_dir(directory).expect("read repository std directory") {
            let path = entry.expect("read repository std entry").path();
            if path.is_dir() {
                collect_yu_files(&path, files);
            } else if path.extension().and_then(|extension| extension.to_str()) == Some("yu") {
                files.push(path);
            }
        }
    }

    let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("canonical repository root");
    let lib = repository.join("lib");
    let mut paths = vec![lib.join("std.yu")];
    collect_yu_files(&lib.join("std"), &mut paths);
    paths.sort();

    let mut files = vec![sources::SourceFile {
        module_path: sources::Path::default(),
        source: "use std::prelude::*\nmod std;\n".to_string(),
    }];
    files.extend(paths.into_iter().map(|path| {
        let relative = path.strip_prefix(&lib).expect("std source below lib");
        let mut module = relative.to_path_buf();
        module.set_extension("");
        let segments = module
            .components()
            .map(|component| {
                let std::path::Component::Normal(segment) = component else {
                    panic!("normal std module path component")
                };
                sources::Name(segment.to_str().expect("utf-8 std module path").to_string())
            })
            .collect();
        sources::SourceFile {
            module_path: sources::Path { segments },
            source: std::fs::read_to_string(&path).expect("read repository std source"),
        }
    }));
    let loaded = sources::load(files);
    let output = crate::lowering::lower_loaded_files(&loaded).expect("lower repository std");
    assert!(output.errors.is_empty(), "{:?}", output.errors);
    output
}
