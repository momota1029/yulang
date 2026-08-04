use super::act_copy_census::{
    ActTemplateCatalogSource, SyntheticActCopyKind, capture_synthetic_act_copy_census,
};
use super::*;
use poly::expr::Def;

const VAR_TEMPLATE: &str = concat!(
    "pub act ref_update 'a:\n",
    "  pub update: 'a -> 'a\n",
    "pub type ref 'e 'a with:\n",
    "  struct self:\n",
    "    get: () -> ['e] 'a\n",
    "    update_effect: () -> [ref_update 'a; 'e] ()\n",
    "  pub r.update(f: 'a -> 'a): ['e] () =\n",
    "    my loop(x: [_] _) = catch x:\n",
    "      ref_update::update v, k -> loop:k:f v\n",
    "    loop:r.update_effect()\n",
    "pub act var 't:\n",
    "  pub get: () -> 't\n",
    "  pub set: 't -> ()\n",
    "  my var_ref(): std::control::var::ref '[var 't] 't = std::control::var::ref {\n",
    "    get: \\() -> get(),\n",
    "    update_effect: \\() -> set:std::control::var::ref_update::update:get()\n",
    "  }\n",
    "  my run(v: 't, x: [_] 'r): 'r = catch x:\n",
    "    get(), k -> run v: k v\n",
    "    set v, k -> run v: k()\n",
);
const FLOW_TEMPLATE: &str = concat!(
    "pub act sub 'a:\n",
    "  pub return: 'a -> never\n",
    "  pub sub(x: [_] 'a): 'a = catch x:\n",
    "    return a, _ -> a\n",
    "    a -> a\n",
    "pub act label_sub 'a:\n",
    "  pub return: 'a -> never\n",
    "  pub struct label { marker: unit }\n",
    "  our control_label = label { marker: () }\n",
    "  pub sub(x: [_] 'a): 'a = catch x:\n",
    "    return a, _ -> a\n",
    "    sub::return a, _ -> a\n",
    "    a -> a\n",
);

#[test]
fn m1_0_census_distinguishes_cold_embedded_and_warm_prefix_legacy_routes() {
    let source = mixed_source(1);
    let cold_files = std_loaded(&format!("mod std;\n{source}"));
    let (cold, cold_census) =
        capture_synthetic_act_copy_census(|| lower_loaded_files(&cold_files).unwrap());
    assert!(cold.errors.is_empty(), "cold: {:?}", cold.errors);
    assert_legacy_cell(
        cold_census.cell(
            SyntheticActCopyKind::Var,
            ActTemplateCatalogSource::Embedded,
        ),
        1,
    );
    assert_legacy_cell(
        cold_census.cell(
            SyntheticActCopyKind::LabelSub,
            ActTemplateCatalogSource::Embedded,
        ),
        1,
    );
    assert_eq!(
        cold_census.cell(SyntheticActCopyKind::Var, ActTemplateCatalogSource::Prefix),
        Default::default(),
    );

    let prefix = std_prefix();
    let suffix = sources::load(vec![source_file(&[], &source)]);
    let (warm, warm_census) = capture_synthetic_act_copy_census(|| {
        lower_loaded_files_with_prefix(&prefix, &suffix).unwrap()
    });
    assert!(warm.errors.is_empty(), "warm: {:?}", warm.errors);
    assert_legacy_cell(
        warm_census.cell(SyntheticActCopyKind::Var, ActTemplateCatalogSource::Prefix),
        1,
    );
    assert_legacy_cell(
        warm_census.cell(
            SyntheticActCopyKind::LabelSub,
            ActTemplateCatalogSource::Prefix,
        ),
        1,
    );
    assert_eq!(
        warm_census.cell(
            SyntheticActCopyKind::LabelSub,
            ActTemplateCatalogSource::Embedded,
        ),
        Default::default(),
    );
    assert_warm_cold_normalized_scheme_parity(&cold, &warm, SyntheticActCopyKind::Var);
    assert_warm_cold_normalized_scheme_parity(&cold, &warm, SyntheticActCopyKind::LabelSub);
}

#[test]
fn m1_0_legacy_cost_fixtures_pin_warm_and_cold_var_and_label_sub_slopes() {
    let prefix = std_prefix();
    let mut var_timings = Vec::new();
    let mut label_timings = Vec::new();
    let mut cold_var_timings = Vec::new();
    let mut cold_label_timings = Vec::new();
    for count in 1..=3 {
        let (var, var_census) = warm_case(&prefix, &var_source(count));
        assert_legacy_cell(
            var_census.cell(SyntheticActCopyKind::Var, ActTemplateCatalogSource::Prefix),
            count,
        );
        assert_eq!(var.modules.synthetic_var_act_copy_ids().len(), count);
        assert_instances_have_one_normalized_scheme_view(
            &var,
            SyntheticActCopyKind::Var,
            var.modules.synthetic_var_act_copy_ids(),
        );
        var_timings.push(var.timing.synthetic_act_copy);

        let (label, label_census) = warm_case(&prefix, &label_source(count));
        assert_legacy_cell(
            label_census.cell(
                SyntheticActCopyKind::LabelSub,
                ActTemplateCatalogSource::Prefix,
            ),
            count,
        );
        assert_eq!(
            label.modules.synthetic_sub_label_act_copy_ids().len(),
            count
        );
        assert_instances_have_one_normalized_scheme_view(
            &label,
            SyntheticActCopyKind::LabelSub,
            label.modules.synthetic_sub_label_act_copy_ids(),
        );
        label_timings.push(label.timing.synthetic_act_copy);

        let (cold_var, cold_var_census) = cold_case(&var_source(count));
        assert_legacy_cell(
            cold_var_census.cell(
                SyntheticActCopyKind::Var,
                ActTemplateCatalogSource::Embedded,
            ),
            count,
        );
        cold_var_timings.push(cold_var.timing.synthetic_act_copy);

        let (cold_label, cold_label_census) = cold_case(&label_source(count));
        assert_legacy_cell(
            cold_label_census.cell(
                SyntheticActCopyKind::LabelSub,
                ActTemplateCatalogSource::Embedded,
            ),
            count,
        );
        cold_label_timings.push(cold_label.timing.synthetic_act_copy);
    }

    eprintln!("M1-0 warm var synthetic-copy timings: {var_timings:?}");
    eprintln!("M1-0 warm label_sub synthetic-copy timings: {label_timings:?}");
    eprintln!("M1-0 cold var synthetic-copy timings: {cold_var_timings:?}");
    eprintln!("M1-0 cold label_sub synthetic-copy timings: {cold_label_timings:?}");
    assert!(var_timings.iter().all(|elapsed| *elapsed > Duration::ZERO));
    assert!(
        label_timings
            .iter()
            .all(|elapsed| *elapsed > Duration::ZERO)
    );
    assert!(
        var_timings[2] > var_timings[0],
        "var fixture lost its positive cost slope"
    );
    assert!(
        label_timings[2] > label_timings[0],
        "label_sub fixture lost its positive cost slope"
    );
    assert!(
        cold_var_timings[2] > cold_var_timings[0],
        "cold var fixture lost its positive cost slope"
    );
    assert!(
        cold_label_timings[2] > cold_label_timings[0],
        "cold label_sub fixture lost its positive cost slope"
    );
}

fn warm_case(
    prefix: &BodyLoweringPrefix,
    source: &str,
) -> (
    BodyLowering,
    act_copy_census::SyntheticActCopyCensusSnapshot,
) {
    let suffix = sources::load(vec![source_file(&[], source)]);
    let (output, census) = capture_synthetic_act_copy_census(|| {
        lower_loaded_files_with_prefix(prefix, &suffix).unwrap()
    });
    assert!(output.errors.is_empty(), "{source}\n{:?}", output.errors);
    (output, census)
}

fn cold_case(
    source: &str,
) -> (
    BodyLowering,
    act_copy_census::SyntheticActCopyCensusSnapshot,
) {
    let files = std_loaded(&format!("mod std;\n{source}"));
    let (output, census) =
        capture_synthetic_act_copy_census(|| lower_loaded_files(&files).unwrap());
    assert!(output.errors.is_empty(), "{source}\n{:?}", output.errors);
    (output, census)
}

fn assert_warm_cold_normalized_scheme_parity(
    cold: &BodyLowering,
    warm: &BodyLowering,
    kind: SyntheticActCopyKind,
) {
    let (cold_ids, warm_ids) = match kind {
        SyntheticActCopyKind::Var => (
            cold.modules.synthetic_var_act_copy_ids(),
            warm.modules.synthetic_var_act_copy_ids(),
        ),
        SyntheticActCopyKind::LabelSub => (
            cold.modules.synthetic_sub_label_act_copy_ids(),
            warm.modules.synthetic_sub_label_act_copy_ids(),
        ),
    };
    assert_eq!(cold_ids.len(), 1);
    assert_eq!(warm_ids.len(), 1);
    assert_eq!(
        normalized_legacy_scheme_view(cold, kind, cold_ids[0]),
        normalized_legacy_scheme_view(warm, kind, warm_ids[0]),
    );
}

fn assert_legacy_cell(cell: act_copy_census::SyntheticActCopyCensusCell, expected: usize) {
    assert_eq!(cell.not_attempted, expected);
    assert_eq!(cell.legacy_cst_lowerings, expected);
    assert_eq!(cell.eligible, 0);
    assert_eq!(cell.miss, 0);
    assert_eq!(cell.fallback, 0);
}

fn assert_instances_have_one_normalized_scheme_view(
    output: &BodyLowering,
    kind: SyntheticActCopyKind,
    ids: Vec<TypeDeclId>,
) {
    let views = ids
        .into_iter()
        .map(|id| normalized_legacy_scheme_view(output, kind, id))
        .collect::<Vec<_>>();
    let Some(expected) = views.first() else {
        panic!("fixture must contain a synthetic copy");
    };
    assert!(views.iter().all(|view| view == expected), "{views:#?}");
}

/// Binder names and the per-site nominal prefix are deliberately removed. M1-2 can compare its
/// detached scheme importer against this legacy baseline without depending on arena allocation.
fn normalized_legacy_scheme_view(
    output: &BodyLowering,
    kind: SyntheticActCopyKind,
    id: TypeDeclId,
) -> Vec<(String, String)> {
    let decl = output
        .modules
        .type_decl_by_id(id)
        .expect("synthetic act decl");
    let family = crate::namespace_path(&output.modules.type_decl_path(&decl));
    let companion = output
        .modules
        .type_companion(id)
        .expect("synthetic companion");
    let names: &[&str] = match kind {
        SyntheticActCopyKind::Var => &["get", "set", "var_ref", "run"],
        SyntheticActCopyKind::LabelSub => &["return", "label", "control_label", "sub"],
    };
    names
        .iter()
        .map(|name| {
            let def = output.modules.value_decls(companion, &Name((*name).into()))[0].def;
            let Some(Def::Let {
                scheme: Some(scheme),
                ..
            }) = output.session.poly.defs.get(def)
            else {
                panic!("{name} must have a finalized scheme");
            };
            let rewrite = |path: &[String]| {
                path.strip_prefix(family.as_slice())
                    .map(|suffix| {
                        std::iter::once("<synthetic-act>".to_string())
                            .chain(suffix.iter().cloned())
                            .collect()
                    })
                    .unwrap_or_else(|| path.to_vec())
            };
            (
                (*name).to_string(),
                poly::dump::format_scheme_with_path_rewriter(
                    &output.session.poly.typ,
                    scheme,
                    &rewrite,
                ),
            )
        })
        .collect()
}

fn std_prefix() -> BodyLoweringPrefix {
    let files = std_loaded("mod std;\n");
    let output = lower_loaded_files(&files).expect("lower M1-0 std prefix");
    assert!(output.errors.is_empty(), "prefix: {:?}", output.errors);
    output.into_prefix()
}

fn std_loaded(root: &str) -> Vec<LoadedFile> {
    sources::load(vec![
        source_file(&[], root),
        source_file(&["std"], "pub mod control;\n"),
        source_file(&["std", "control"], "pub mod var;\npub mod flow;\n"),
        source_file(&["std", "control", "var"], VAR_TEMPLATE),
        source_file(&["std", "control", "flow"], FLOW_TEMPLATE),
    ])
}

fn source_file(path: &[&str], source: &str) -> sources::SourceFile {
    sources::SourceFile {
        module_path: Path {
            segments: path.iter().map(|segment| Name((*segment).into())).collect(),
        },
        source: source.to_string(),
    }
}

fn mixed_source(count: usize) -> String {
    format!("{}\n{}", var_source(count), label_source(count))
}

fn var_source(count: usize) -> String {
    let mut source = "my var_case =\n".to_string();
    for index in 0..count {
        source.push_str(&format!("  my $v{index} = {index}\n"));
    }
    source.push_str("  0\nvar_case\n");
    source
}

fn label_source(count: usize) -> String {
    let mut source = String::new();
    for index in 0..count {
        source.push_str(&format!(
            "my label_case_{index} = sub 'label{index}: {index}\n"
        ));
    }
    source.push_str("label_case_0\n");
    source
}
