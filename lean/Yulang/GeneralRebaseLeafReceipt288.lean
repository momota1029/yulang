import Yulang.GeneralRebaseRowRefreshDiagnostics288

/-! A source-local leaf receipt. Its head and local equations have separate
provenance from the ambient snapshot. No existing trust constructor or
transition consumes this new proof interface. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseLeafReceipt288
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedEvidence231 (Frame Evidence)
open GeneralNominalVersionedDiagnostic232 (boundary)
open GeneralNominalVersionedSupport233 (Readback)
open GeneralNominalVersionedPlans231 (Inputs Outputs)
open GeneralRebaseInertLeaf288 (Leaf SourceSlice)
open GeneralNominalSupport (Head)

variable {roles : Roles.RoleDecls}

structure Receipt (registry : Registry) (state : State roles) (root : Occurrence roles)
    (key : Nat) (plan : Plan roles) : Prop where
  frame : Frame registry state.core root key plan
  safe : B4TargetV8.SafeKnown (boundary roles) registry state root
  merged : ¬ GeneralNominalVersionedMergedConflict232.MergedOutputConflict state root
  unique : GeneralNominalVersionedCandidates231.Unique registry state.core.erased.current.context root key []
  noChildren : GeneralNominalVersionedFrame231.children plan.packet = []
  noRequests : GeneralNominalCenteredHeadOutputs.requests state.core root = []
  sourceExists : ∃ m, SourceSlice state m
  rootReadback : ∀ slot, ∃ test obs,
    Head state.core.erased.current.context.state (root.demand.arguments slot).1 test obs ∧
    ∀ m, SourceSlice state m → obs.Holds m
  nestedReadback : Readback state [] plan
  localChecks : ∀ m, SourceSlice state m → Inputs plan m ∧ Outputs plan m

variable {registry : Registry} {state : State roles} {root : Occurrence roles}
variable {key : Nat} {plan : Plan roles}

theorem strong_if_ambient (proof : Receipt registry state root key plan)
    (ambient : ∀ m, SourceSlice state m → GeneralNominalState.Models state.core.erased.current.context.state m) :
    Leaf registry state root key plan :=
  ⟨proof.frame,proof.safe,proof.merged,proof.unique,proof.noChildren,proof.noRequests,proof.sourceExists,
    fun m inSource => ⟨proof.frame.context_eq.symm ▸ ambient m inSource,proof.localChecks m inSource⟩⟩

theorem instantiate (proof : Receipt registry state root key plan) (m : Assignment)
    (valid : Models state m) : Evidence registry state.core m root (.node key []) := by
  have source := GeneralNominalVersionedSupport233.trusted_models .source valid
  have hold : GeneralNominalVersionedPlans231.Holds plan m :=
    ⟨proof.frame.context_eq.symm ▸ valid.1.1,proof.localChecks m source⟩
  have ready : GeneralNominalCenteredHeadMatEffects.Ready state.core root plan := by
    intro out included
    rw [proof.noRequests] at included
    cases included
  have effects : GeneralNominalVersionedEffects231.ClassEffects state.core root plan m := by
    constructor <;> intro out included <;> rw [proof.noRequests] at included <;> cases included
  exact GeneralNominalVersionedEvidence231.evidence_leaf
    ⟨plan,GeneralNominalVersionedEvidence231.certificate_of_semantics proof.frame proof.noChildren.symm hold ready effects⟩

end Yulang.GeneralRebaseLeafReceipt288
