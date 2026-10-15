//! Private provisional source evaluator. Production inference and backends do not
//! depend on this module. Missing typed-consumer evidence stops execution.
mod continuation;
mod literal;
mod machine;
mod program;
mod receiving;

pub use machine::{
    ContinuationHandle, Machine, RuntimeOutcome, RuntimeValue, RuntimeValueKind, ValueHandle,
};
pub use program::{
    NameConsumption, RuntimeEvidence, RuntimeProgram, RuntimeUnavailable, SourceSite,
};
