use super::super::gateway::IdentitiesPublishPort;

pub(in crate::constraints::structural_kernel) fn publish_shadow(port: IdentitiesPublishPort<'_>) {
    port.publish_shadow();
}
