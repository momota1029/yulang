import Yulang.GeneralDeclarativeI65I74ExplicitPickMeaning419

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ExplicitPick419
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Pattern normalize)
open Checker408 (Problem Result)

private theorem pick_not_variable_family419 {p} (a : PickPacket p)
    (scope : (d : Declaration) → d ∈ visible p.state.core p.root → RepeatedRow403 p.root d) : False := by
  let d := a.declaration.decl
  have seen : d ∈ visible p.state.core p.root := by simp [d,a.declaration.theOnlyOne]
  have stated : pickSyntax a.rows.x a.declaration.fieldBinder a.declaration.tailBinder ∈ d.head :=
    by simp [d,a.declaration.literal]
  rw [(scope d seen).literal] at stated
  obtain ⟨_,_,bad⟩ := List.mem_map.mp stated
  cases bad

private theorem pick_not_nominal419 {p} (a : PickPacket p)
    {d : Declaration} (seen : d ∈ visible p.state.core p.root) {literal : Pattern}
    (src : d.head = [literal]) {head args} (shape : normalize literal = .app head args) :
    False := by
  have ident : d = a.declaration.decl := by simpa [a.declaration.theOnlyOne] using seen
  have same := (List.cons.inj (src.symm.trans
    ((congrArg Declaration.head ident).trans a.declaration.literal))).1
  rw [same] at shape
  cases shape

private theorem pick_not_repeated_diagnostic419 {p v} (a : PickPacket p)
    (old : RepeatedOther403 p.state p.root v) : False := by
  cases old with
  | ambiguous scope _ =>
    obtain ⟨scope⟩ := scope
    exact pick_not_variable_family419 a scope.allVisible

private theorem pick_not_native_diagnostic419 {p v needs} (a : PickPacket p)
    (old : variableWithNativeK2403.other p.state p.root v needs) : False := by
  rcases old.2 with repeats|⟨_,_,view,_⟩
  · exact pick_not_repeated_diagnostic419 a repeats
  · exact pick_not_nominal419 a view.visibleRow view.exactHead view.dispatch

private theorem pick_not_completed_native_diagnostic419 {p v needs} (a : PickPacket p)
    (old : completedNativePrioritySource404.other p.state p.root v needs) : False := by
  rcases old with earlier|⟨_,⟨caller⟩⟩
  · exact pick_not_native_diagnostic419 a earlier
  · exact pick_not_nominal419 a caller.entry.visibleRow caller.entry.exactHead caller.entry.dispatch

private theorem pick_not_completed_choice_diagnostic419 {p v needs} (a : PickPacket p)
    (old : completedChoiceSource404.other p.state p.root v needs) : False := by
  rcases old with earlier|⟨_,⟨scope⟩⟩
  · exact pick_not_completed_native_diagnostic419 a earlier
  · exact pick_not_variable_family419 a scope.allVisible

private theorem pick_has_output419 {p} (a : PickPacket p) (empty : p.root.demand.outputs = []) : False := by
  have h := a.single
  rw [empty] at h
  cases h

theorem no_older_diagnostic_claims_this_actual_Pick419 {p verdict needs} (a : PickPacket p) :
    ¬ RigidRival418.R10.other p.state p.root verdict needs := by
  rintro ((((⟨_,family,old⟩|⟨_,_,⟨closed⟩⟩)|mixed)|opened)|⟨_,_,⟨ambiguity⟩⟩)
  · cases family with
    | variableOnly =>
      cases old.2 with
      | ambiguous scope _ =>
        obtain ⟨scope⟩ := scope
        let d := a.declaration.decl
        have seen : d ∈ visible p.state.core p.root := by simp [d,a.declaration.theOnlyOne]
        have stated : pickSyntax a.rows.x a.declaration.fieldBinder a.declaration.tailBinder ∈ d.head :=
          by simp [d,a.declaration.literal]
        rw [(scope.allVisible d seen).literal] at stated
        obtain ⟨_,_,bad⟩ := List.mem_map.mp stated
        cases bad
    | repeated | whereTree => exact pick_not_repeated_diagnostic419 a old.2
    | nativeK2 | supported => exact pick_not_native_diagnostic419 a old
    | supportedK2 => exact pick_not_completed_native_diagnostic419 a old
    | supportedAmbiguity | authoredNative => exact pick_not_completed_choice_diagnostic419 a old
  · exact pick_has_output419 a closed.field.noOutputs
  · obtain ⟨_,_,⟨mixed⟩⟩ := mixed
    have count := mixed.rivalsExist
    simp [a.declaration.theOnlyOne] at count
  · obtain ⟨_,_,⟨view⟩⟩ := opened
    exact pick_has_output419 a view.input.noOutputs
  · have count := congrArg List.length a.declaration.theOnlyOne
    rcases ambiguity.ordered with h|h <;> simp [h] at count

/-- No pre-existing interpretation can claim a different result for this
actual explicitly written record request. The previous checker still runs
unchanged everywhere; this is a disjointness theorem, not a new filter. -/
theorem previous_checker_is_disjoint_for_actual_Pick419 (p : Problem) (r : Result)
    (a : PickPacket p) (w : RigidRival418.Witness) : RigidRival418.check p r w = false := by
  cases verdict : RigidRival418.check p r w with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨e,t,_,_⟩ := (RigidRival418.check_sound p r w verdict).1
    generalize r.tree = tree at t
    cases t with
    | rootK2 cycle => exact a.rawSafe cycle
    | other _ _ rule _ => exact no_older_diagnostic_claims_this_actual_Pick419 a rule
    | selected event _ rule _ _ => exact no_older_selected_rule_can_claim_actual_Pick419 a event rule

end Yulang.GeneralDeclarativeI65.I72.ExplicitPick419
