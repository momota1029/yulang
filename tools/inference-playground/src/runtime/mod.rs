//! Private provisional source evaluator. Production inference and backends do not
//! depend on this module. Missing typed-consumer evidence stops execution.
mod literal;
mod machine;
mod program;

pub use machine::{Machine, RuntimeOutcome, RuntimeValue, RuntimeValueKind, ValueHandle};
pub use program::{
    NameConsumption, RuntimeEvidence, RuntimeProgram, RuntimeUnavailable, SourceSite,
};
