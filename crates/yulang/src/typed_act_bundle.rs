//! Reproducible release asset for cold synthetic-act template profiles.

#[cfg(test)]
use infer::typed_act_bundle::verify_profile_external_anchors;
use infer::typed_act_bundle::{
    SemanticStdManifest, SemanticStdModule, TypedActTemplateBundle, TypedActTemplateBundleError,
    TypedActTemplateProfileKind, capture_profile_from_legacy_lowering,
};
use std::sync::OnceLock;

pub const CHECKED_IN_TYPED_ACT_TEMPLATE_BUNDLE: &[u8] =
    include_bytes!("../assets/typed_act_templates.bin");

static DECODED_TYPED_ACT_TEMPLATE_BUNDLE: OnceLock<Option<TypedActTemplateBundle>> =
    OnceLock::new();

pub(crate) fn lower_loaded_files_with_embedded_typed_act_catalog(
    files: &[sources::LoadedFile],
) -> Result<infer::lowering::BodyLowering, infer::LoadedFilesError> {
    let bundle = DECODED_TYPED_ACT_TEMPLATE_BUNDLE
        .get_or_init(|| TypedActTemplateBundle::decode(CHECKED_IN_TYPED_ACT_TEMPLATE_BUNDLE).ok());
    lower_loaded_files_with_typed_act_bundle(bundle.as_ref(), files)
}

fn lower_loaded_files_with_typed_act_bundle(
    bundle: Option<&TypedActTemplateBundle>,
    files: &[sources::LoadedFile],
) -> Result<infer::lowering::BodyLowering, infer::LoadedFilesError> {
    let Some(profile) = bundle
        .as_ref()
        .and_then(|bundle| infer::typed_act_bundle::profile_for_loaded_files(bundle, files))
    else {
        return infer::lowering::lower_loaded_files(files);
    };
    infer::typed_act_bundle::with_cold_typed_act_template_cutover(profile, || {
        infer::lowering::lower_loaded_files(files)
    })
}

pub fn generate_typed_act_template_bundle_bytes() -> Result<Vec<u8>, String> {
    let (full, _) = generate_profile(TypedActTemplateProfileKind::FullStd)?;
    let (playground, _) = generate_profile(TypedActTemplateProfileKind::PlaygroundStd)?;
    TypedActTemplateBundle::from_profiles(vec![full, playground])
        .encode()
        .map_err(bundle_error)
}

pub fn decode_checked_in_typed_act_template_bundle() -> Result<TypedActTemplateBundle, String> {
    TypedActTemplateBundle::decode(CHECKED_IN_TYPED_ACT_TEMPLATE_BUNDLE).map_err(bundle_error)
}

fn generate_profile(
    kind: TypedActTemplateProfileKind,
) -> Result<
    (
        infer::typed_act_bundle::TypedActTemplateBundleProfile,
        infer::lowering::BodyLowering,
    ),
    String,
> {
    let entry = match kind {
        TypedActTemplateProfileKind::FullStd => "<typed-act-full-std-root>",
        TypedActTemplateProfileKind::PlaygroundStd => "<typed-act-playground-std-root>",
    };
    let collected = match kind {
        TypedActTemplateProfileKind::FullStd => {
            crate::collect_source_text_with_embedded_std(entry, String::new())
        }
        TypedActTemplateProfileKind::PlaygroundStd => {
            crate::collect_source_text_with_embedded_playground_std(entry, String::new())
        }
    }
    .map_err(|error| error.to_string())?;
    let loaded = match kind {
        TypedActTemplateProfileKind::FullStd => {
            crate::load_source_text_with_embedded_std(entry, String::new())
        }
        TypedActTemplateProfileKind::PlaygroundStd => {
            crate::load_source_text_with_embedded_playground_std(entry, String::new())
        }
    }
    .map_err(|error| error.to_string())?;
    let manifest = SemanticStdManifest::new(
        collected
            .iter()
            .filter(|file| !file.module_path.segments.is_empty())
            .map(|file| SemanticStdModule {
                module_path: file
                    .module_path
                    .segments
                    .iter()
                    .map(|segment| segment.0.clone())
                    .collect(),
                source_hash: stable_source_hash(file.source.as_bytes()),
            })
            .collect(),
    );
    let lowering = infer::lowering::lower_loaded_files_for_typed_act_template_bundle(&loaded)
        .map_err(|error| format!("legacy std lowering failed: {error:?}"))?;
    if !lowering.errors.is_empty() {
        return Err(format!(
            "legacy std lowering diagnostics: {:?}",
            lowering.errors
        ));
    }
    let profile =
        capture_profile_from_legacy_lowering(kind, manifest, &lowering).map_err(bundle_error)?;
    Ok((profile, lowering))
}

fn stable_source_hash(bytes: &[u8]) -> u64 {
    let mut hash = 0xcbf29ce484222325_u64;
    for byte in bytes {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(0x100000001b3);
    }
    hash
}

fn bundle_error(error: TypedActTemplateBundleError) -> String {
    format!("{error:?}")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn m1_6_checked_in_bundle_is_reproducible_and_external_anchors_resolve() {
        let checked = decode_checked_in_typed_act_template_bundle().expect("decode checked asset");
        let mut generated_profiles = Vec::new();
        for kind in [
            TypedActTemplateProfileKind::FullStd,
            TypedActTemplateProfileKind::PlaygroundStd,
        ] {
            let (profile, lowering) = generate_profile(kind).expect("legacy-only profile capture");
            let resolved = verify_profile_external_anchors(&profile, &lowering)
                .expect("all stable external anchors resolve");
            assert!(resolved > 0, "{kind:?} must retain external anchors");
            generated_profiles.push(profile);
        }
        let regenerated = TypedActTemplateBundle::from_profiles(generated_profiles)
            .encode()
            .expect("encode regenerated bundle");
        assert_eq!(regenerated, CHECKED_IN_TYPED_ACT_TEMPLATE_BUNDLE);
        assert_eq!(checked.profiles.len(), 2);
    }

    #[test]
    fn m1_8_playground_std_embedded_catalog_matches_cold_legacy_before_cutover() {
        let source = concat!(
            "my state =\n",
            "  my $value = 1\n",
            "  &value = $value\n",
            "  $value\n",
            "my escaped = sub 'done:\n",
            "  'done.return state\n",
            "escaped\n",
        );
        let files = crate::load_source_text_with_embedded_playground_std(
            "<m1-8-playground-shadow>",
            source.to_string(),
        )
        .expect("load playground std source set");
        let bundle = decode_checked_in_typed_act_template_bundle().expect("decode checked asset");
        let profile = infer::typed_act_bundle::profile_for_loaded_files(&bundle, &files)
            .expect("playground source set selects an embedded profile");
        assert_eq!(profile.kind, TypedActTemplateProfileKind::PlaygroundStd);

        let (lowering, report) =
            infer::typed_act_bundle::with_cold_typed_act_template_shadow_report(profile, || {
                infer::lowering::lower_loaded_files(&files).expect("cold playground lowering")
            });
        assert!(lowering.errors.is_empty(), "{:?}", lowering.errors);
        assert!(report.failures.is_empty(), "{:?}", report.failures);
        assert_eq!(report.var_passed, 1, "{report:?}");
        assert_eq!(report.label_sub_passed, 1, "{report:?}");
    }

    #[test]
    fn m1_8_playground_std_cold_cutover_is_eligible_and_skips_legacy_lowering() {
        let source = concat!(
            "my state =\n",
            "  my $value = 1\n",
            "  &value = $value\n",
            "  $value\n",
            "my escaped = sub 'done:\n",
            "  'done.return state\n",
            "escaped\n",
        );
        let files = crate::load_source_text_with_embedded_playground_std(
            "<m1-8-playground-cutover>",
            source.to_string(),
        )
        .expect("load playground std source set");
        let bundle = decode_checked_in_typed_act_template_bundle().expect("decode checked asset");
        let profile = infer::typed_act_bundle::profile_for_loaded_files(&bundle, &files)
            .expect("playground source set selects an embedded profile");
        assert_eq!(profile.kind, TypedActTemplateProfileKind::PlaygroundStd);

        let (lowering, report) =
            infer::typed_act_bundle::with_cold_typed_act_template_cutover_report(profile, || {
                infer::lowering::lower_loaded_files(&files).expect("cold playground lowering")
            });
        assert!(lowering.errors.is_empty(), "{:?}", lowering.errors);
        assert_eq!(report.var_eligible, 1, "{report:?}");
        assert_eq!(report.label_sub_eligible, 1, "{report:?}");
        assert_eq!(report.misses, 0, "{report:?}");
        assert_eq!(report.fallbacks, 0, "{report:?}");
        assert_eq!(report.legacy_lowerings, 0, "{report:?}");
    }

    #[test]
    fn m1_8_playground_std_cold_cutover_reaches_control_lowering() {
        for (case, source) in [
            (
                "var",
                "my state =\n  my $value = 1\n  &value = $value + 1\n  $value\nstate\n",
            ),
            (
                "label_sub",
                "my state = sub 'done:\n  'done.return 2\nstate\n",
            ),
            ("combined", m1_8_full_pipeline_source()),
        ] {
            let files = crate::load_source_text_with_embedded_playground_std(
                format!("<m1-8-playground-control-{case}>"),
                source.to_string(),
            )
            .expect("load playground std source set");
            let poly = crate::build_poly_from_loaded_files(files).expect("cold poly lowering");
            crate::build_control_from_poly_output(&poly).unwrap_or_else(|error| {
                let missing = match &error {
                    crate::RouteError::Specialize(specialize::SpecializeError::MissingScheme {
                        def,
                    }) => Some(poly::expr::DefId(def.0)),
                    _ => None,
                };
                let detail = missing.map(|def| {
                    let shape = match poly.arena.defs.get(def) {
                        Some(poly::expr::Def::Let {
                            scheme,
                            body,
                            children,
                            ..
                        }) => format!(
                            "Let(scheme={}, body={body:?}, children={children:?})",
                            scheme.is_some()
                        ),
                        Some(poly::expr::Def::Mod { children, .. }) => {
                            format!("Mod(children={children:?})")
                        }
                        Some(poly::expr::Def::Arg) => "Arg".to_string(),
                        None => "missing".to_string(),
                    };
                    (def, poly.labels.def_label(def), shape)
                });
                panic!("{case} cold control lowering: {error:?}; missing={detail:?}")
            });
        }
    }

    #[test]
    fn m1_8_invalid_stale_and_custom_std_bundles_fail_closed_to_legacy() {
        let source = "my $value = 1\n$value\n";
        let files = crate::load_source_text_with_embedded_playground_std(
            "<m1-8-fallback>",
            source.to_string(),
        )
        .expect("load playground std source set");
        let legacy = infer::lowering::lower_loaded_files(&files).expect("legacy lowering");

        let invalid = TypedActTemplateBundle::decode(b"not a typed-act bundle").ok();
        let invalid_output = lower_loaded_files_with_typed_act_bundle(invalid.as_ref(), &files)
            .expect("invalid bundle falls back");
        assert_eq!(invalid_output.errors, legacy.errors);

        let bundle = decode_checked_in_typed_act_template_bundle().expect("decode checked asset");
        let mut custom_std = files.clone();
        custom_std
            .iter_mut()
            .find(|file| !file.module_path.segments.is_empty())
            .expect("playground std module")
            .source
            .push_str("\n# custom std fingerprint\n");
        assert!(infer::typed_act_bundle::profile_for_loaded_files(&bundle, &custom_std).is_none());
        let custom_output = lower_loaded_files_with_typed_act_bundle(Some(&bundle), &custom_std)
            .expect("custom/stale std falls back");
        assert_eq!(custom_output.errors, legacy.errors);
    }

    fn m1_8_full_pipeline_source() -> &'static str {
        concat!(
            "my state =\n",
            "  my $value = 1\n",
            "  &value = $value + 1\n",
            "  sub 'done:\n",
            "    'done.return $value\n",
            "state\n",
        )
    }
}
