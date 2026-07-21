use super::*;
use crate::casts::{
    OrdinaryCastShadowOutcome, OrdinaryCastShadowSeam, begin_ordinary_cast_shadow_capture,
    finish_ordinary_cast_shadow_capture,
};
use poly::cast_resolution::{OrdinaryCastResolution, classify_ordinary_cast_candidates};
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
fn missing_boundary_shadow_observation_matches_the_ocast_a_oracle() {
    let cases = [
        "struct S { x: bool }\nS { x: 42 }\n",
        "my f(): bool = 42\nf()\n",
    ];

    for source in cases {
        begin_ordinary_cast_shadow_capture();
        let output = lower_source(source);
        let witnesses = finish_ordinary_cast_shadow_capture()
            .into_iter()
            .filter(|witness| {
                witness.seam == OrdinaryCastShadowSeam::NominalConstraint
                    && witness.source == ["int".to_string()]
                    && witness.target == ["bool".to_string()]
            })
            .collect::<Vec<_>>();

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        assert!(!witnesses.is_empty(), "required int -> bool boundary");
        assert!(witnesses.iter().all(|witness| {
            witness.outcome == OrdinaryCastShadowOutcome::Missing
                && witness.candidate_defs.is_empty()
        }));
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
fn source_local_infer_and_poly_classification_match_the_ocast_a_oracle() {
    let declarations = [
        "",
        "pub cast(x: int): target = target { value: x }\n",
        concat!(
            "pub cast(x: int): target = target { value: x }\n",
            "pub cast(x: int): target = target { value: x }\n",
        ),
    ];

    for (candidate_count, declarations) in declarations.into_iter().enumerate() {
        let output = lower_source(&format!("struct target {{ value: int }}\n{declarations}"));
        let source = ["int".to_string()];
        let target = ["target".to_string()];
        let infer_resolution = output.session.casts.resolve_value(&source, &target);
        let poly_resolution = classify_ordinary_cast_candidates(
            output.session.poly.cast_rules.iter().filter(|rule| {
                rule.kind == CastRuleKind::Value && rule.source == source && rule.target == target
            }),
        );
        let expected = match candidate_count {
            0 => OrdinaryCastShadowOutcome::Missing,
            1 => OrdinaryCastShadowOutcome::Unique,
            _ => OrdinaryCastShadowOutcome::Ambiguous,
        };

        assert_eq!(resolution_outcome(&infer_resolution), expected);
        assert_eq!(resolution_outcome(&poly_resolution), expected);
    }
}

#[test]
fn source_local_cast_registration_retains_def_without_changing_scheme() {
    let output = lower_source(concat!(
        "struct target { value: int }\n",
        "pub cast(x: int): target = target { value: x }\n",
    ));
    let source = ["int".to_string()];
    let target = ["target".to_string()];
    let infer_rule = output
        .session
        .casts
        .candidates(&source, &target)
        .first()
        .expect("source-local infer value rule");
    let poly_rule = output
        .session
        .poly
        .cast_rules
        .iter()
        .find(|rule| {
            rule.kind == CastRuleKind::Value && rule.source == source && rule.target == target
        })
        .expect("source-local durable value rule");

    assert_eq!(infer_rule.def, Some(poly_rule.def));
    assert_eq!(infer_rule.scheme.quantifiers, poly_rule.scheme.quantifiers);
    assert_eq!(
        infer_rule.scheme.role_predicates,
        poly_rule.scheme.role_predicates
    );
    assert_eq!(
        infer_rule.scheme.recursive_bounds,
        poly_rule.scheme.recursive_bounds
    );
    assert_eq!(
        infer_rule.scheme.stack_quantifiers,
        poly_rule.scheme.stack_quantifiers
    );
    assert_eq!(infer_rule.scheme.predicate, poly_rule.scheme.predicate);
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

#[test]
fn repository_std_infer_and_poly_classification_are_unique() {
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

    for (source, target) in expected_pairs {
        let OrdinaryCastResolution::Unique(infer_rule) =
            output.session.casts.resolve_value(&source, &target)
        else {
            panic!("std infer cast must be unique: {source:?} -> {target:?}")
        };
        let OrdinaryCastResolution::Unique(poly_rule) = classify_ordinary_cast_candidates(
            output.session.poly.cast_rules.iter().filter(|rule| {
                rule.kind == CastRuleKind::Value && rule.source == source && rule.target == target
            }),
        ) else {
            panic!("std durable cast must be unique: {source:?} -> {target:?}")
        };

        assert_eq!(infer_rule.def, Some(poly_rule.def));
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

fn resolution_outcome<R>(resolution: &OrdinaryCastResolution<R>) -> OrdinaryCastShadowOutcome {
    match resolution {
        OrdinaryCastResolution::Missing => OrdinaryCastShadowOutcome::Missing,
        OrdinaryCastResolution::Unique(_) => OrdinaryCastShadowOutcome::Unique,
        OrdinaryCastResolution::Ambiguous(_) => OrdinaryCastShadowOutcome::Ambiguous,
    }
}
