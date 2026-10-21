//! Private provisional source evaluator. Production inference and backends do not
//! depend on this module. Missing typed-consumer evidence stops execution.
mod continuation;
mod literal;
mod machine;
mod primitive;
mod program;
mod receiving;

pub use machine::{
    ContinuationHandle, Machine, RuntimeOutcome, RuntimeValue, RuntimeValueKind, TupleElement,
    ValueHandle,
};
pub use program::{
    ExecutionRoot, ExpressionExecutionRoot, NameConsumption, RuntimeEvidence, RuntimeProgram,
    RuntimeUnavailable, SourceSite,
};
