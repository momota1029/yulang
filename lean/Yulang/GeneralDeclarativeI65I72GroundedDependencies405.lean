import Yulang.GeneralDeclarativeI65I72GroundedNative405

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (Dictionary Tree Summarizes)

mutual
/-- Indexed across the actual derivation, including strictly smaller
producer selections which are deliberately not dictionary children.
No assumption that every non-selected branch has a full visit list. -/
def TracePriority405 {R s q t ev} (trace : SourceTrace R s q t ev) : Prop :=
  match trace with
  | .rootK2 _ => True
  | .other _ _ _ support => ProducerPriority405 support
  | .selected e _ _ support children =>
    PriorityAt405 (e := e) support ∧ ProducerPriority405 support ∧ WherePriority405 children

def WherePriority405 {R s qs ts} (forest : WhereForest R s qs ts) : Prop :=
  match forest with
  | .nil => True
  | .cons node tail => TracePriority405 node ∧ WherePriority405 tail

def ProducerPriority405 {R s needs} (forest : SupportForest R s needs) : Prop :=
  match forest with
  | .nil => True
  | .cons node _ _ tail => TracePriority405 node ∧ ProducerPriority405 tail
end

theorem every_entered_selected_proof_keeps_grounded_priority405 {R}
    (invert : GroundedInversion405 R) {s q t e} (trace : SourceTrace R s q t e) :
    TracePriority405 trace := by
  exact SourceTrace.rec (R := R) (s := s)
    (motive_1 := fun _ _ _ trace => TracePriority405 trace)
    (motive_2 := fun _ _ deps => WherePriority405 deps)
    (motive_3 := fun _ deps => ProducerPriority405 deps)
    (fun _ => True.intro)
    (fun _ _ _ _ below => below)
    (fun event safe primitive support kids before after =>
      ⟨priority_at_actual_support405 invert event _ support safe primitive,before,after⟩)
    True.intro
    (fun _ _ a b => ⟨a,b⟩)
    True.intro
    (fun _ _ _ _ a b => ⟨a,b⟩)
    trace

/-- Recover priority at the literal producer receipt ordinal in the
same support list, not a different selection with equal outputs. -/
theorem actual_output_support_uses_grounded_producer405 {R s needs}
    (support : SupportForest R s needs) (grounded : ProducerPriority405 support)
    (i : Nat) {need : OutputNeed s} (atI : needs[i]? = some need) :
    TracePriority405 (support.atOriginal i atI).source := by
  cases support with
  | nil => simp at atI
  | cons chosen done typed tail =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at atI
      subst need
      exact grounded.1
    | succ i =>
      have later : ProducerPriority405 tail := grounded.2
      exact actual_output_support_uses_grounded_producer405 tail later i (by simpa using atI)

theorem actual_selected_event_and_literal_producer_both_grounded405
    {s q t e} (trace : SourceTrace completedChoiceSource404 s q t (some e)) :
    ∃ (needs : List (OutputNeed s)) (support : SupportForest completedChoiceSource404 s needs),
      PriorityAt405 (e := e) support ∧
      (∀ i need (seen : needs[i]? = some need),
        TracePriority405 (support.atOriginal i seen).source ∧
        ¬ RootCycle s need.producer) := by
  have all := every_entered_selected_proof_keeps_grounded_priority405
    actual_completed_choice_grounds_visits405 trace
  cases trace with
  | selected e raw chosen support kids =>
    exact ⟨_,support,all.1,fun i need found =>
      ⟨actual_output_support_uses_grounded_producer405 support all.2.1 i found,
        exact_output_support_cannot_use_root_k2 (support.atOriginal i found)⟩⟩

end Yulang.GeneralDeclarativeI65.I72
