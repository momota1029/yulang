//! Conditional Dir-Protect adapter, owned by the opt-in core proof lane.
//! Caller witnesses are unresolved assumptions, never source-derived identities.
//! No production consumer, solver, allocation, provider input or evidence mutation
//! is involved. Failure publishes nothing; removing this module and its wiring
//! rolls back the experiment without changing source obligations or F5.

use crate::shadow::{BinderId, ExprId};
use crate::shadow_derivation::PendingSourceCallRegistration;

/// One caller-assumed original dependency family. All fields remain unresolved.
/// `W` is caller-owned witness storage, not a semantic ID minted by this adapter.
pub struct AssumedOriginalContext<'a, W> {
    pub beta: &'a W,
    pub scope: &'a W,
    pub xi: &'a W,
    pub shared_variable: &'a W,
}

/// Caller assumption at one exact exposure; the binder's formal status is pending.
pub struct AssumedExposure<'a, W> {
    pub source: &'a ExprId,
    pub binder: &'a BinderId,
    pub context: &'a AssumedOriginalContext<'a, W>,
}

/// Caller-owned upper-view assumption packet. Its reference joins inputs;
/// the enclosed witness supplies no source or typed-view judgment.
pub struct AssumedUpperView<'a, W> {
    pub witness: &'a W,
}

/// Explicit unresolved input categories of the selected rule.
pub enum AssumedDirectionalInput<'a, W> {
    /// Assumes this seed protects the shared variable while still inferred at u.
    ProtectedVariableAtExposure {
        exposure: AssumedExposure<'a, W>,
        seed: &'a W,
    },
    /// Assumes an original source-generated upper Function demand v <: U.
    SourceUpperFunctionUse {
        exposure: AssumedExposure<'a, W>,
        upper_view: &'a AssumedUpperView<'a, W>,
    },
    /// Assumes the exact covariant output-effect occurrence of this same U.
    CovariantOutputOccurrence {
        exposure: AssumedExposure<'a, W>,
        upper_view: &'a AssumedUpperView<'a, W>,
        output: &'a W,
    },
}

/// Checked premise wiring only. Actual source applicability, joint-context
/// validity and typed output correspondence remain pending on the source.
pub struct DirectionalProtectionPremises<'a, W> {
    source: &'a ExprId,
    binder: &'a BinderId,
    context: &'a AssumedOriginalContext<'a, W>,
    seed: &'a W,
    upper_view: &'a AssumedUpperView<'a, W>,
    output: &'a W,
}

impl<'a, W> DirectionalProtectionPremises<'a, W> {
    /// Rejects category swaps and mixed source/binder/context/view witnesses.
    /// Reference identity checks wire assumptions; they establish no semantics.
    pub fn from_assumed_inputs(
        registration: &PendingSourceCallRegistration<'_, '_>,
        seed_input: AssumedDirectionalInput<'a, W>,
        upper_input: AssumedDirectionalInput<'a, W>,
        output_input: AssumedDirectionalInput<'a, W>,
    ) -> Option<Self> {
        let AssumedDirectionalInput::ProtectedVariableAtExposure { exposure, seed } = seed_input
        else {
            return None;
        };
        let AssumedDirectionalInput::SourceUpperFunctionUse {
            exposure: upper_exposure,
            upper_view,
        } = upper_input
        else {
            return None;
        };
        let AssumedDirectionalInput::CovariantOutputOccurrence {
            exposure: output_exposure,
            upper_view: output_view,
            output,
        } = output_input
        else {
            return None;
        };
        if exposure.source != registration.source
            || exposure.source != registration.source_use_input.application().expression()
            || exposure.binder != registration.source_use_input.binder()
            || !same_exposure(&exposure, &upper_exposure)
            || !same_exposure(&exposure, &output_exposure)
            || !std::ptr::eq(upper_view, output_view)
        {
            return None;
        }
        Some(Self {
            source: exposure.source,
            binder: exposure.binder,
            context: exposure.context,
            seed,
            upper_view,
            output,
        })
    }

    /// Applies only the selected one-step conditional rule; no lower input exists.
    pub fn derive_conditionally(self) -> ConditionalDirectionalProtection<'a, W> {
        ConditionalDirectionalProtection {
            status: ConditionalStatus::Assumed,
            source: self.source,
            binder: self.binder,
            context: self.context,
            seed: self.seed,
            upper_view: self.upper_view,
            covariant_output: self.output,
        }
    }
}

/// A logical conditional conclusion, never a protection grant or inference result.
pub struct ConditionalDirectionalProtection<'a, W> {
    pub status: ConditionalStatus,
    pub source: &'a ExprId,
    pub binder: &'a BinderId,
    pub context: &'a AssumedOriginalContext<'a, W>,
    pub seed: &'a W,
    pub upper_view: &'a AssumedUpperView<'a, W>,
    pub covariant_output: &'a W,
}

#[derive(Debug, PartialEq, Eq)]
pub enum ConditionalStatus {
    Assumed,
}

fn same_exposure<W>(left: &AssumedExposure<'_, W>, right: &AssumedExposure<'_, W>) -> bool {
    left.source == right.source
        && left.binder == right.binder
        && std::ptr::eq(left.context, right.context)
}
