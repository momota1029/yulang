import Yulang.GeneralDictionaryCenteredCandidate176

/-! Structural guard production from the current inspected candidate. No raw
installation, stability or joint model assumption is needed for this part.
Value support and a common centered branch model remain explicit residuals. -/
namespace Yulang.GeneralDictionaryCenteredGuard177
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralDictionaryCenteredCandidate176
open GeneralNominalCenteredBoundary (Local)

variable {roles : Roles.RoleDecls} {registry : Registry} {state : State roles}
  {focus : Occurrence roles} {key : Nat} {children : List (Occurrence roles)} {plan : Plan roles}

 theorem candidate_headReady (candidate : Candidate registry state focus key children plan) :
    GeneralNominalRecursiveCandidates.HeadReady registry plan.packet.context
      focus plan.packet.declaration := by
  rw [← candidate.registry_eq, ← candidate.occurrence_eq]
  obtain ⟨metadata,linked,fresh,bounds,found,finished,_,model,branch⟩ := candidate.prepared
  exact ⟨metadata,linked,fresh,bounds,found,finished,model,branch.1,branch.2.1⟩

 theorem candidate_structural_guards
    (candidate : Candidate registry state focus key children plan)
    (selected : Local registry state focus (.selected key children)) :
    DecisionGuard registry state focus ∧
    ¬ RootCycle state focus ∧ ¬ CandidateCycle registry state focus ∧
    Safe state plan ∧ AlternativesSafe registry state plan.input := by
  have input : plan.input.occurrence = focus := plan.input_exact.trans candidate.occurrence_eq
  have located := candidate.located
  rw [candidate.occurrence_eq] at located
  have guards := GeneralNominalCenteredInspection.selected_guards selected
  exact ⟨guards.1,guards.2.1,guards.2.2,
    GeneralNominalCenteredInspection.selected_safe selected plan candidate.centered_recorded
      input candidate.registry_eq candidate.context_eq candidate.visible candidate.role
      (candidate_headReady candidate) located,
    GeneralNominalCenteredInspection.selected_alternatives selected plan.input
      candidate.centered_recorded input⟩

/-- Exact residual guard characterization, without assuming raw Installable.
This does not construct value support or a common model of the journal and plan. -/
theorem candidate_guard_iff
    (candidate : Candidate registry state focus key children plan)
    (selected : Local registry state focus (.selected key children))
    (support : List (Occurrence roles)) :
    PacketGuard state plan support ↔
      GeneralNominalValueSupport.PacketGuard state.erased plan.packet support ∧
      ∃ model, Models state model ∧ plan.Holds model := by
  constructor
  · intro guard
    exact ⟨guard.2.1,guard.2.2.2.2.2.2⟩
  · rintro ⟨values,model⟩
    obtain ⟨decision,noRoot,noCandidate,safe,alternatives⟩ :=
      candidate_structural_guards candidate selected
    refine ⟨candidate.centered_recorded,values,?_,safe,?_,?_,model⟩
    · simpa only [DecisionGuard,candidate.registry_eq,candidate.context_eq,
        candidate.occurrence_eq] using decision
    · simpa only [candidate.registry_eq] using alternatives
    · simpa only [candidate.registry_eq,candidate.occurrence_eq] using And.intro noRoot noCandidate

end Yulang.GeneralDictionaryCenteredGuard177
