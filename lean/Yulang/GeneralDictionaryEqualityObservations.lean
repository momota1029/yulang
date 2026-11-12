import Yulang.GeneralDictionaryJointMerge

/-! Equality feedback is observationally reversible for prepared branches and
Joint, at the same assignment. Endpoint registration prevents fresh source
capture. Journal entailment is needed only in the forward direction.
These are not merge confluence results. -/
namespace Yulang.GeneralDictionaryEqualityObservations
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalFeedbackSteps GeneralNominalJointCandidates
open GeneralDictionaryJointEquality GeneralNominalRecursiveCandidates
variable {roles : Roles.RoleDecls}

theorem equate_as_extension (state : State roles) (first last : Nat) :
    equate state first last = {state with context := (GeneralDictionaryOrdinaryTransport.extend state.context []
        (GeneralNominalAllocation.equations first (.var last)) [])} := by
  simp [equate, GeneralNominalState.extend, GeneralDictionaryOrdinaryTransport.extend,
    GeneralDictionaryOrdinaryTransport.extendState]

/-- Reverse transport retains the exact assignment. No equality entailment is
needed for restriction. -/
theorem branch_equate_back (registry : Registry) (state : State roles)
    (root : Occurrence roles) (key first last : Nat)
    (one : first ∈ GeneralNominalState.sources state.context.state)
    (two : last ∈ GeneralNominalState.sources state.context.state)
    (model : GeneralNominalCommonBridge.Assignment)
    (given : BranchAt registry (equate state first last) root key model) :
    BranchAt registry state root key model := by
  rw [equate_as_extension] at given
  exact (GeneralDictionaryJointMerge.branch_extension_back registry state
    (GeneralNominalAllocation.equations first (.var last))
    (sources_equate state first last · one two) root key model given).1

/-- Exact per-assignment branch preservation for journal-entailed equality. -/
theorem branch_equate_iff (registry : Registry) (state : State roles)
    (root : Occurrence roles) (key first last : Nat)
    (one : first ∈ GeneralNominalState.sources state.context.state)
    (two : last ∈ GeneralNominalState.sources state.context.state)
    (equal : GeneralNominalFeedbackK2.Equal state first last)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    BranchAt registry (equate state first last) root key model ↔
      BranchAt registry state root key model :=
  ⟨branch_equate_back registry state root key first last one two model,
    branch_equate_forward registry state root key first last one two equal model valid⟩

/-- Restriction preserves the one model shared by every alias-related site. -/
theorem joint_equate_back (registry : Registry) (state : State roles)
    (root : Occurrence roles) (key first last : Nat)
    (one : first ∈ GeneralNominalState.sources state.context.state)
    (two : last ∈ GeneralNominalState.sources state.context.state)
    (given : Joint registry (equate state first last) root key) :
    Joint registry state root key := by
  obtain ⟨packets,model,valid,branch,related⟩ := given
  have oldValid : Models state model := by
    exact ⟨((GeneralNominalState.extend_models state.context.state []
      (GeneralNominalAllocation.equations first (.var last)) model).mp valid.1).1, valid.2⟩
  refine ⟨?_,model,oldValid,
    branch_equate_back registry state root key first last one two model branch,?_⟩
  · intro packet member alias
    exact packets packet member (alias_same (before := state)
      (after := equate state first last) rfl alias)
  · intro site rel
    apply branch_equate_back registry state site.occurrence key first last one two model
    exact related site ⟨rel.1,alias_same (before := state)
      (after := equate state first last) rfl rel.2⟩

/-- Equality feedback neither loses nor creates Joint candidates. In particular
it cannot repair a missing common assignment between aliases. -/
theorem joint_equate_iff (registry : Registry) (state : State roles)
    (root : Occurrence roles) (key first last : Nat)
    (one : first ∈ GeneralNominalState.sources state.context.state)
    (two : last ∈ GeneralNominalState.sources state.context.state)
    (equal : GeneralNominalFeedbackK2.Equal state first last) :
    Joint registry (equate state first last) root key ↔ Joint registry state root key :=
  ⟨joint_equate_back registry state root key first last one two,
    joint_equate registry state root key first last one two equal⟩
/-- Certificate restricting a finite sequence to journal-entailed equations
on existing sources. It does not replace or assert actual support reachability. -/
inductive Equates : State roles → State roles → Prop where
  | refl (state) : Equates state state
  | tail {before middle : State roles} (path : Equates before middle)
      (first last : Nat)
      (one : first ∈ GeneralNominalState.sources middle.context.state)
      (two : last ∈ GeneralNominalState.sources middle.context.state)
      (equal : GeneralNominalFeedbackK2.Equal middle first last) :
      Equates before (equate middle first last)

theorem Equates.trans {before middle after : State roles}
    (first : Equates before middle) (last : Equates middle after) : Equates before after := by
  induction last with
  | refl => exact first
  | tail _ a b one two equal ih => exact .tail ih a b one two equal

/-- A finite equality subphase retains exactly the journal assignments. -/
theorem Equates.models {before after : State roles} (path : Equates before after)
    (model : GeneralNominalCommonBridge.Assignment) : Models after model ↔ Models before model := by
  induction path with
  | refl => rfl
  | tail _ a b _ _ equal ih => exact (equate_models _ a b equal model).trans ih

/-- Full recursive evidence is preserved at the original journal assignment,
with precisely the same payload. -/
theorem Equates.evidence {before after : State roles} (path : Equates before after)
    (registry : Registry) (model : GeneralNominalCommonBridge.Assignment)
    (valid : Models before model) (root : Occurrence roles)
    (payload : GeneralDictionaryReadback.Payload) :
    GeneralDictionaryRecursiveEvidence.Evidence registry after.context model root payload ↔
      GeneralDictionaryRecursiveEvidence.Evidence registry before.context model root payload := by
  have growth : GeneralDictionaryOrdinaryTrace.Extension before.context after.context := by
    induction path with
    | refl => exact GeneralDictionaryOrdinaryTrace.extension_refl _
    | tail _ a b _ _ _ ih =>
      exact GeneralDictionaryOrdinaryTrace.extension_trans ih
        (GeneralDictionaryOrdinaryTrace.equate_extension _ a b)
  exact ⟨GeneralDictionaryOrdinaryTrace.evidence_extension_backward registry _ _ growth model root payload,
    GeneralDictionaryOrdinaryTrace.evidence_extension registry _ _ growth model
      ((path.models model).mpr valid).1 root payload⟩

/-- Complete Joint observation, including failure, is invariant under the
finite equality subphase. No separate existential models are amalgamated. -/
theorem Equates.joint {before after : State roles} (path : Equates before after)
    (registry : Registry) (root : Occurrence roles) (key : Nat) :
    Joint registry after root key ↔ Joint registry before root key := by
  induction path with
  | refl => rfl
  | tail _ a b one two equal ih =>
    exact (joint_equate_iff registry _ root key a b one two equal).trans ih

end Yulang.GeneralDictionaryEqualityObservations
