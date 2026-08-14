use super::super::gateway::ConstraintsPublishPort;

pub(in crate::constraints::structural_kernel) fn publish_shadow(port: ConstraintsPublishPort<'_>) {
    port.publish_shadow();
}
