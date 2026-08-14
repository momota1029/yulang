use super::super::gateway::BoundsPublishPort;

pub(in crate::constraints::structural_kernel) fn publish_shadow(port: BoundsPublishPort<'_>) {
    port.publish_shadow();
}
