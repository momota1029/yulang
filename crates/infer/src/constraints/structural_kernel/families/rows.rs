use super::super::gateway::RowsPublishPort;

pub(in crate::constraints::structural_kernel) fn publish_shadow(port: RowsPublishPort<'_>) {
    port.publish_shadow();
}
