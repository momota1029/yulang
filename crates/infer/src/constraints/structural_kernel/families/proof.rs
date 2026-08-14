use super::super::gateway::ProofPublishPort;

pub(in crate::constraints::structural_kernel) fn publish_shadow(port: ProofPublishPort<'_>) {
    port.publish_shadow();
}

#[cfg(cpk_sv_d_ss2_p0_ui_legacy_sources_private)]
fn ui_family_cannot_name_legacy_read_sources(_: super::super::LegacyOnlyReadSources<'_>) {}
