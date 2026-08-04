use super::stage0_tests::root_value_def;
use super::*;
use crate::constraints::{
    GlobalAlphaConsequenceCensusSnapshot, capture_global_alpha_consequence_census,
};
use crate::interface_oracle::{BoundaryInterface, SchemeAlphaView};
use poly::expr::Def;

const RMW_X3: &str = concat!(
    "my rmw = { my $a = 0; &a = $a; &a = $a; &a = $a; $a }\n",
    "rmw\n",
);

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

#[test]
fn rmw_x3_global_alpha_consequence_census_and_exported_scheme_parity() {
    let prefix_files = minimal_var_std_loaded("mod std;\n");
    let prefix_output = lower_loaded_files(&prefix_files).expect("lower repository std prefix");
    assert!(
        prefix_output.errors.is_empty(),
        "prefix errors: {:?}",
        prefix_output.errors
    );
    let prefix = prefix_output.into_prefix();

    let (instrumented, census) = capture_global_alpha_consequence_census(|| rmw_case(&prefix));
    let legacy = rmw_case(&prefix);

    eprintln!("RMW x3 global alpha consequence census: {census:#?}");
    assert_census_partition(census);
    assert_eq!(
        (
            census.exact_duplicate_or_trivial,
            census.locally_isomorphic_but_distinct,
            census.globally_alpha_equivalent,
            census.genuinely_novel,
        ),
        (9_818, 898, 0, 28),
        "RMW x3 four-bucket census drifted",
    );
    assert_eq!((census.pair_candidates, census.accepted), (10_744, 926));
    assert_eq!((census.exact_duplicates, census.trivial), (9_534, 284));
    assert_eq!(census.max_component_constraints, 1_285);
    assert_eq!(census.oracle_comparisons, 428_275);
    assert_eq!(
        census.oracle_mismatches, 0,
        "strict alpha construction drifted"
    );
    assert_eq!(
        exported_rmw_scheme_alpha(&instrumented),
        exported_rmw_scheme_alpha(&legacy),
        "shadow census must preserve the trusted exported-scheme alpha view",
    );
}

fn assert_census_partition(census: GlobalAlphaConsequenceCensusSnapshot) {
    assert!(
        census.pair_candidates > 0,
        "RMW fixture must exercise replay"
    );
    assert!(census.accepted > 0, "RMW fixture must accept consequences");
    assert_eq!(census.classified_total(), census.pair_candidates);
    assert_eq!(
        census.locally_isomorphic_but_distinct
            + census.globally_alpha_equivalent
            + census.genuinely_novel,
        census.accepted,
    );
    assert_eq!(
        census.exact_duplicate_or_trivial,
        census.exact_duplicates + census.trivial,
    );
}

fn rmw_case(prefix: &BodyLoweringPrefix) -> BodyLowering {
    let suffix = sources::load(vec![sources::SourceFile {
        module_path: sources::Path {
            segments: Vec::new(),
        },
        source: RMW_X3.into(),
    }]);
    let output = lower_loaded_files_with_prefix(prefix, &suffix).expect("lower RMW x3 suffix");
    assert!(output.errors.is_empty(), "RMW errors: {:?}", output.errors);
    output
}

fn minimal_var_std_loaded(root: &str) -> Vec<LoadedFile> {
    sources::load(vec![
        source_file(&[], root),
        source_file(&["std"], "pub mod control;\n"),
        source_file(&["std", "control"], "pub mod var;\n"),
        source_file(&["std", "control", "var"], VAR_TEMPLATE),
    ])
}

fn source_file(path: &[&str], source: &str) -> sources::SourceFile {
    sources::SourceFile {
        module_path: sources::Path {
            segments: path
                .iter()
                .map(|segment| sources::Name((*segment).into()))
                .collect(),
        },
        source: source.into(),
    }
}

fn exported_rmw_scheme_alpha(output: &BodyLowering) -> SchemeAlphaView {
    let def = root_value_def(&output.modules, "rmw");
    let Some(Def::Let {
        scheme: Some(scheme),
        ..
    }) = output.session.poly.defs.get(def)
    else {
        panic!("RMW binding must have an exported scheme")
    };
    SchemeAlphaView::characterize_current_scheme(
        output.session.infer.constraints().types(),
        scheme,
        BoundaryInterface::EMPTY,
    )
    .view
}
