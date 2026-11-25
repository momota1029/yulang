import Yulang.GeneralDeclarativeI65I74OpenTailModels414

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.OpenTail414
open GeneralDeclarativeI65
open CommonNominalFullCarrier (Ty Subtype Equivalent record observeTy)
open CommonNominalFullDemand (AcceptAt Environment Demand Observation ProbeAt ProbeStep MaskedProbeStep)

private def fieldEnvironment : Environment CommonNominalFullCarrier.Row :=
  ⟨fun _ => .top,fun _ => []⟩

theorem a_filled_tail_is_not_semantically_an_empty_tail414 (label : Nat) :
    ¬ Equivalent (.emptyRecord : Ty) (record label (.base .int) .emptyRecord) := by
  intro same
  let d : Demand CommonNominalFullCarrier.Row := .atom (.field label .trivial)
  have field : AcceptAt Common.rowLe 0 fieldEnvironment
      (observeTy 1 (record label (.base .int) .emptyRecord)) d := by
    intro ob see
    have h : ob = .field label .trivial := see
    cases h
    change (if label = label ∧ label ∉ ([] : List Nat) then True else False)
    simp
  have impossible := same.1 1 0 fieldEnvironment d field (.field label .trivial) rfl
  exact impossible

theorem one_accepted_X4_report_preserves_semantically_distinct_models414
    (p : Checker408.Problem) (w : OpenWire)
    (yes : check p pendingReport (.openTail w) = true)
    (read : ∀ v : OpenVerified p, replayOpen414 p w = some v →
      p.state.core.origins = [v.pending.input.origin])
    (fresh : Nat) :
    ∃ a : OpenInput p.state p.root, ∃ m n : I72.Model,
      Fits p.state m ∧ Fits p.state n ∧
      ¬ Equivalent (m.assignment a.tail).1 (n.assignment a.tail).1 ∧
      ReportEvidence p.state m p.root pendingReport ∧ ReportEvidence p.state n p.root pendingReport := by
  obtain ⟨a,m,n,ma,na,me,ne,_,mr,nr⟩ := one_checked_state_has_two_tail_models414 p w yes read fresh
  refine ⟨a,m,n,ma,na,?_,mr,nr⟩
  rw [me,ne]
  exact a_filled_tail_is_not_semantically_an_empty_tail414 fresh

end Yulang.GeneralDeclarativeI65.I72.OpenTail414
