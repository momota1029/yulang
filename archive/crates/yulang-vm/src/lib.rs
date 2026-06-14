//! VM execution for Yulang runtime IR.
//!
//! This crate owns VM value containers, host request handling, and both the
//! tree-walking VM and compact control VM. It consumes monomorphized
//! `yulang-runtime` modules instead of participating in runtime lowering or
//! specialization.

pub mod host;
pub mod runtime;
pub mod vm;

pub use host::{HostRunOutput, eval_root_with_basic_host, eval_roots_with_basic_host};
pub use vm::{
    CONTROL_VM_ARTIFACT_VERSION, ControlVmModule, VmError, VmModule, VmProfile, VmRequest,
    VmResult, VmValue, compile_control_vm_module, compile_vm_module,
};
