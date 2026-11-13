import Yulang.GeneralNominalSettledBoundary

/-! Positive source-only sanity for I26. When the tracked fact journal is empty,
the old guard already supplies a source entailment, so the new trusted ledger
can be empty. This includes every initial source and does not settle children. -/
namespace Yulang.GeneralDictionarySettledSourceGuard
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport
variable {roles : Roles.RoleDecls} {state : Tracked roles}

/-- No assumption about producer settlement is needed for a source entailment. -/
theorem head_of_empty_facts (empty : state.facts = [])
    (given : HeadSupported state support identity test) :
    GeneralNominalSettledSupport.HeadJustified state identity test := by
  obtain ⟨snapshot,observation,head,entails⟩ := given
  refine ⟨[],.source,snapshot,observation,head,?_⟩
  intro model valid
  apply entails model
  refine ⟨valid.1,?_⟩
  intro fact member _
  rw [empty] at member
  cases member

theorem ready_of_empty_facts (empty : state.facts = [])
    (given : ReadyAt state support identity) :
    GeneralNominalSettledSupport.ReadyAt state identity := by
  obtain ⟨test,observation,head,supported⟩ := given
  exact ⟨test,observation,head,head_of_empty_facts empty supported⟩

theorem base_decision_of_empty_facts (empty : state.facts = [])
    (given : GeneralNominalSupport.DecisionGuard state registry root support) :
    GeneralNominalSettledSupport.DecisionGuard registry state root :=
  ⟨fun index => ready_of_empty_facts empty (given.2.1 index),
   fun declaration member role bounds located slot inspected =>
     ready_of_empty_facts empty (given.2.2 declaration member role bounds located slot inspected)⟩

theorem decision_of_empty_facts (empty : state.facts = [])
    (given : GeneralNominalValueSupport.DecisionGuard registry state root support) :
    GeneralNominalSettledSupport.DecisionGuard registry state root :=
  base_decision_of_empty_facts empty given.1

theorem initial_decision (context : GeneralNominalCandidates.Context) (root : Occurrence roles)
    (given : GeneralNominalValueSupport.DecisionGuard registry (initial context root) focus support) :
    GeneralNominalSettledSupport.DecisionGuard registry (initial context root) focus :=
  decision_of_empty_facts rfl given

/-- Every source-only selected Value frontier remains selected by I26. -/
theorem selected_of_empty_facts (empty : state.facts = [])
    (selected : GeneralNominalValueBoundary.Local registry state root (.selected key children)) :
    GeneralNominalSettledBoundary.Local registry state root (.selected key children) := by
  classical
  cases selected with
  | selected safe unique =>
    have supported : ∃ support, GeneralNominalValueSupport.DecisionGuard registry state root support :=
      Classical.byContradiction (fun blocked => safe.2.2.2 (Or.inr blocked))
    obtain ⟨support,guard⟩ := supported
    refine .selected ⟨safe.1,safe.2.1,safe.2.2.1,?_⟩ unique
    rintro (old | blocked)
    · exact safe.2.2.2 old
    · exact blocked (decision_of_empty_facts empty guard)

theorem initial_selected (context : GeneralNominalCandidates.Context) (root : Occurrence roles)
    (selected : GeneralNominalValueBoundary.Local registry (initial context root) focus (.selected key children)) :
    GeneralNominalSettledBoundary.Local registry (initial context root) focus (.selected key children) :=
  selected_of_empty_facts rfl selected

/-- Empty-journal installation witnesses satisfy the new extra guard. -/
theorem packet_guard_of_empty_facts (empty : state.facts = [])
    (given : GeneralNominalValueSupport.PacketGuard state packet support) :
    GeneralNominalSettledSupport.PacketGuard state packet support :=
  ⟨given,base_decision_of_empty_facts empty given.1.2⟩

/-- The new relation loses no old step at a state with an empty fact journal. -/
theorem at_of_empty_facts (empty : state.facts = [])
    (step : GeneralNominalValueSteps.At registry state focus after) :
    GeneralNominalSettledSteps.At registry state focus after := by
  cases step with
  | administrative focus after action => exact .administrative focus after action
  | install packet support enabled novel guard =>
    exact .install packet support enabled novel (packet_guard_of_empty_facts empty guard)
  | merge first last support one two same novel guard =>
    exact .merge first last support one two same novel guard

theorem step_of_empty_facts (empty : state.facts = [])
    (step : GeneralNominalValueSteps.Step registry root state after) :
    GeneralNominalSettledSteps.Step registry root state after :=
  ⟨step.choose,step.choose_spec.1,at_of_empty_facts empty step.choose_spec.2⟩

/-- Source formation has no provisional outputs yet; one-step relations agree. -/
theorem initial_step_iff (context : GeneralNominalCandidates.Context) (root : Occurrence roles) :
    GeneralNominalSettledSteps.Step registry root (initial context root) after ↔
    GeneralNominalValueSteps.Step registry root (initial context root) after :=
  ⟨GeneralNominalSettledSteps.step_old,step_of_empty_facts rfl⟩
end Yulang.GeneralDictionarySettledSourceGuard
