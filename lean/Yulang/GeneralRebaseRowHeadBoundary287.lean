import Yulang.GeneralRebaseDepthSemanticTransitions286

/-! The current bounded inspector leaves row-parameter destructuring pending.
Known opaque nominal input is not the same as support for that pattern. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseRowHeadBoundary287
open GeneralDeclarationPatterns (Constructors Pattern)
open GeneralNominalInspection (Interpretation Query translate)
open GeneralNominalState (State Descriptor Parameter)
open GeneralNominalRecursiveInspection (Origin Report inspect typeArguments Finished)

theorem translates_deferred {catalogue : Constructors} {interp : Interpretation}
    {key : Nat} {layout : GeneralDeclarationPatterns.Constructor} {args : List Pattern}
    (resolved : catalogue key = some layout) (rowParameter : .row ∈ layout.parameters)
    (nonprimitive : interp.primitives key = none) :
    translate catalogue interp (.app key args) = .deferred (.app key args) := by
  have notAll : (layout.parameters.all (· == .type)) = false := by
    cases check : layout.parameters.all (· == .type) with
    | false => rfl
    | true =>
      have bad := List.all_eq_true.mp check _ rowParameter
      cases bad
  rw [translate,resolved]
  simp only [notAll,Bool.and_false,Bool.false_and,Bool.false_eq_true,ite_false]
  all_goals simp [nonprimitive]

theorem recursive_no_type_arguments {slots : Nat} {args : List (Parameter slots)}
    {ends : Fin slots × Fin slots} (found : .row ends ∈ args) : typeArguments args = none := by
  induction args with
  | nil => cases found
  | cons head tail ih =>
    rcases List.mem_cons.mp found with rfl|found
    · rfl
    · unfold typeArguments at *
      simp only [List.mapM_cons]
      rw [ih found]
      cases head <;> simp


theorem recursive_row_block {s : State} {bounds : GeneralNominalInspection.Bounds s}
    {d : Descriptor s.base.slots} {kids : List Query} {origin : Option Origin}
    {ends : Fin s.base.slots × Fin s.base.slots}
    (existsHead : s.nominals bounds.1 = some d) (row : .row ends ∈ d.arguments) :
    (inspect s (.nominal d.declaration.name kids) bounds origin).blocked = [bounds] := by
  rw [inspect,existsHead]
  simp only [recursive_no_type_arguments row]
  rfl

theorem recursive_row_not_finished {s : State} {bounds : GeneralNominalInspection.Bounds s}
    {d : Descriptor s.base.slots} {kids : List Query} {origin : Option Origin}
    {ends : Fin s.base.slots × Fin s.base.slots}
    (seen : s.nominals bounds.1 = some d) (row : .row ends ∈ d.arguments) :
    ¬ Finished (inspect s (.nominal d.declaration.name kids) bounds origin) := by
  intro done
  have clash := done.1
  rw [recursive_row_block seen row] at clash
  cases clash

theorem whole_capture {s : State} (name : Nat) (bounds : GeneralNominalInspection.Bounds s) (origin : Option Origin) :
    Finished (inspect s (.variables [name]) bounds origin) ∧
      (inspect s (.variables [name]) bounds origin).captures = [⟨name,bounds,origin⟩] :=
  by simp [inspect, Finished]

end Yulang.GeneralRebaseRowHeadBoundary287
