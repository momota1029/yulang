use super::super::gateway::ProofPublishPort;

pub(in crate::constraints::structural_kernel) fn publish_shadow(port: ProofPublishPort<'_>) {
    port.publish_shadow();
}
