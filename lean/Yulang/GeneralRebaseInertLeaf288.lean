import Yulang.GeneralNominalVersionedDiagnosticLaws232
import Yulang.GeneralNominalVersionedSupport233

/-! One source-certified leaf. This independent certificate is not an
operational step and does not change the recorded journal. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseInertLeaf288
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedSupport233 (SliceModels)
open GeneralNominalVersionedEvidence231 (Evidence)
open GeneralNominalVersionedDiagnostic232 (boundary Local)
variable {roles : Roles.RoleDecls}

abbrev SourceSlice (state : State roles) (model : Assignment) : Prop := SliceModels state [] model

structure Leaf (registry : Registry) (state : State roles) (root : Occurrence roles)
    (key : Nat) (plan : Plan roles) : Prop where
  frame : GeneralNominalVersionedEvidence231.Frame registry state.core root key plan
  safe : B4TargetV8.SafeKnown (boundary roles) registry state root
  merged : ¬ GeneralNominalVersionedMergedConflict232.MergedOutputConflict state root
  unique : GeneralNominalVersionedCandidates231.Unique registry state.core.erased.current.context root key []
  noChildren : GeneralNominalVersionedFrame231.children plan.packet = []
  noRequests : GeneralNominalCenteredHeadOutputs.requests state.core root = []
  sourceExists : ∃ model, SourceSlice state model
  sourcePacket : ∀ model, SourceSlice state model → GeneralNominalVersionedPlans231.Holds plan model

variable {registry : Registry} {state : State roles} {root : Occurrence roles} {key : Nat} {plan : Plan roles}

theorem ready (leaf : Leaf registry state root key plan) :
    GeneralNominalCenteredHeadMatEffects.Ready state.core root plan := by
  intro out member
  rw [leaf.noRequests] at member
  cases member

theorem class_effects (leaf : Leaf registry state root key plan) (model : Assignment) :
    GeneralNominalVersionedEffects231.ClassEffects state.core root plan model := by
  constructor <;> intro out present <;> rw [leaf.noRequests] at present <;> cases present

theorem source_evidence (leaf : Leaf registry state root key plan)
    (model : Assignment) (source : SourceSlice state model) :
    Evidence registry state.core model root (.node key []) :=
  GeneralNominalVersionedEvidence231.evidence_leaf
    ⟨plan,GeneralNominalVersionedEvidence231.certificate_of_semantics leaf.frame leaf.noChildren.symm
      (leaf.sourcePacket model source) (ready leaf) (class_effects leaf model)⟩

theorem source_evidence_exists (leaf : Leaf registry state root key plan) :
    ∃ model, SourceSlice state model ∧ Evidence registry state.core model root (.node key []) := by
  obtain ⟨model,source⟩ := leaf.sourceExists
  exact ⟨model,source,source_evidence leaf model source⟩

theorem existing_selection (leaf : Leaf registry state root key plan)
    (model : Assignment) (valid : Models state model) :
    Local registry state root (.selected key []) :=
  GeneralNominalVersionedDiagnosticLaws232.selected_of_model leaf.safe leaf.unique valid leaf.frame
    (ready leaf) (leaf.sourcePacket model (GeneralNominalVersionedSupport233.trusted_models .source valid))
    (class_effects leaf model) leaf.merged

end Yulang.GeneralRebaseInertLeaf288
