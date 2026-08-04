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

pub(crate) fn lower_loaded_files_with_embedded_typed_act_shadow(
    files: &[sources::LoadedFile],
) -> Result<infer::lowering::BodyLowering, infer::LoadedFilesError> {
    let bundle = DECODED_TYPED_ACT_TEMPLATE_BUNDLE
        .get_or_init(|| TypedActTemplateBundle::decode(CHECKED_IN_TYPED_ACT_TEMPLATE_BUNDLE).ok());
    let Some(profile) = bundle
        .as_ref()
        .and_then(|bundle| infer::typed_act_bundle::profile_for_loaded_files(bundle, files))
    else {
        return infer::lowering::lower_loaded_files(files);
    };
    infer::typed_act_bundle::with_cold_typed_act_template_shadow(profile, || {
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
}
