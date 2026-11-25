import Yulang.GeneralDeclarativeI65I74ExplicitPickEntry419
import Yulang.GeneralDeclarativeI65I74RigidRivalPriority418

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ExplicitPick419
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Pattern normalize normalizeArgs variablesArgs)
open GeneralDeclarativeWitnessDeclaredState357 (point)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeWhere319 (Capture)
open Checker408 (Problem)
open CommonNominalFullCarrier (Equivalent)
open GeneralDeclarativeInspect321 (PatternK2)

/-- The original out expression can reference this exact logical field,
not a newly chosen value or the record's residual tail. -/
theorem original_literal_body_slot_is_the_actual_field419 {p r} (d : PickDeclaration p r) :
    d.frame.slots (.explicit d.explicit) d.fieldBinder = some (point r.intSlot) := by
  have inputs : d.frame.decl.inputNames = [d.fieldBinder,d.tailBinder] := by
    change variablesArgs (normalizeArgs d.decl.head) = _
    rw [d.literal]
    rfl
  have outputs : d.frame.decl.outputNames = [] := by
    change d.decl.outputBinders.map _ = _
    rw [d.noOutputBinders]
    rfl
  simp [AuthoredBodyFrame393.slots,AuthoredBodyFrame393.captures,inputs,outputs,
    frame_keeps_original_pick_capture419,d.field]

theorem original_binder_tree_carries_exact_three_names419
    {s slots c pat n} (tree : NamedMixedTree401 s slots c pat)
    (shape : pat = .var n) {cap} (slot : slots n = some cap) :
    Check408.encodeRhs tree = .node 0 (Check408.nameTriple n cap) [] := by
  cases tree with
  | binder name stored =>
    have same := Pattern.var.inj shape
    subst n
    have ident := Option.some.inj (stored.property.symm.trans slot)
    simp [Check408.encodeRhs,ident]
  | record _ _ _ => cases shape
  | variant _ _ => cases shape
  | join _ _ => cases shape
  | declaredApp _ _ _ _ _ => cases shape
  | scalar _ _ _ _ => cases shape
  | emptyRecord _ _ _ => cases shape
  | exactEmpty _ _ _ => cases shape
  | pair _ _ _ _ _ => cases shape

theorem typed_ledger_uses_original_binder_and_all_actual_point_names419
    {p : Problem} (a : PickPacket p) :
    a.retained.write.typedRhs =
      .node 0 [a.declaration.fieldBinder,a.rows.intSlot,a.rows.intSlot,a.rows.intSlot] [] := by
  have shape : normalize (GeneralDeclarativeOutputs320.bodyPattern a.retained.output.body) =
      .var a.declaration.fieldBinder := by
    rw [a.actualBody]
    change normalize a.declaration.explicit.rhs = _
    rw [a.declaration.explicitRhs]
    rfl
  have slot : a.declaration.frame.slots a.retained.output.body a.declaration.fieldBinder =
      some (point a.rows.intSlot) := by
    rw [a.actualBody]
    exact original_literal_body_slot_is_the_actual_field419 a.declaration
  exact original_binder_tree_carries_exact_three_names419 a.retained.output.rhs shape slot

theorem retained_output_is_same_field_in_every_fitting_model419
    {p : Problem} (a : PickPacket p) (m : I72.Model) (fit : Fits p.state m) :
    a.retained.output.receipt.actualEquation m =
      some (p.root.demand.outputs[exactlyOneOutput p a.single].target,(m.assignment a.rows.intSlot).1) ∧
    Equivalent (m.assignment p.root.demand.outputs[exactlyOneOutput p a.single].target).1
      (m.assignment a.rows.intSlot).1 := by
  have expr := a.retained.code
  rw [a.fieldCode] at expr
  have reads := fixed_value_code_same_model403 a.retained.output.rhs m (.variable a.rows.intSlot) expr
  constructor
  · simp only [NamedMixedReceipt401.actualEquation, reads, NamedMixedOutput401.receipt]
    rfl
  · have retained := a.retained.atRow
    rw [a.fieldCode] at retained
    exact fit.1.1.2 _ retained

theorem both_real_binders_and_retained_residual_are_preserved419
    {p : Problem} (a : PickPacket p) (m : I72.Model) (fit : Fits p.state m) :
    a.event.frame.names.input a.declaration.fieldBinder = point a.rows.intSlot ∧
    a.event.frame.names.input a.declaration.tailBinder = point a.rows.residual ∧
    Equivalent (m.assignment a.rows.residual).1
      (CommonNominalFullCarrier.record a.rows.y (m.assignment a.rows.strSlot).1 .emptyRecord) := by
  refine ⟨?_,?_,fit.1.1.2 _ a.rows.retainedResidual⟩
  · exact (frame_keeps_original_pick_capture419 _ _).trans a.declaration.field
  · exact (frame_keeps_original_pick_capture419 _ _).trans a.declaration.tail

theorem checked_pattern_cannot_hide_a_reached_cycle419 {p : Problem} (a : PickPacket p) :
    ¬ PatternK2 p.state.core.current.ordinary a.rows.root
      (pickCode a.rows.x a.declaration.fieldBinder a.declaration.tailBinder) := by
  rintro ⟨site,path,cyclic⟩
  have atRoot := pick_binder_fields_do_not_look_inside_the_original_value419 path
  have args : p.root.demand.arguments = [point a.rows.root] := a.rows.requested
  exact a.rawSafe ⟨point a.rows.root,by simp [args],atRoot ▸ cyclic⟩

private theorem actual_pick_decl_is_unique419 {p} (a : PickPacket p)
    {decl : Declaration} (seen : decl ∈ visible p.state.core p.root) :
    decl = a.declaration.decl := by
  simpa [a.declaration.theOnlyOne] using seen

private theorem older_residual_has_no_outputs419 {s q e}
    (old : ClosedResidual415.ResidualElection s q e) : q.demand.outputs = [] := by
  cases old with
  | parent rows _ => exact rows.noOutputs
  | leaf _ _ _ => rfl

theorem no_older_selected_rule_can_claim_actual_Pick419 {p needs}
    (a : PickPacket p) (event : Event p.state p.root) :
    ¬ RigidRival418.R10.elected p.state p.root event needs := by
  rcases p with ⟨s,q⟩
  have same := actual_pick_decl_is_unique419 a event.frame.inScope
  have shape : event.frame.decl.head =
      [pickSyntax a.rows.x a.declaration.fieldBinder a.declaration.tailBinder] :=
    (congrArg Declaration.head same).trans a.declaration.literal
  have wrote : pickSyntax a.rows.x a.declaration.fieldBinder a.declaration.tailBinder ∈
      event.frame.decl.head := by simp [shape]
  rintro ((((((legacy|named)|list)|whereList)|record)|plain)|rival)
  · rcases R0_selection_uses_independent_original_rule407 event legacy with allVariables|native
    · obtain ⟨_,bad,_⟩ := allVariables.2 event.frame.decl event.frame.inScope _ wrote
      cases bad
    · obtain ⟨fromSyntax⟩ := native
      have clash := (List.cons.inj (shape.symm.trans fromSyntax.test.writtenHead)).1
      cases clash
  · obtain ⟨_,⟨candidate⟩⟩ := named
    have clash := (List.cons.inj (shape.symm.trans candidate.test.named)).1
    cases clash
  · obtain ⟨_,⟨candidate⟩⟩ := list
    have clash := (List.cons.inj (shape.symm.trans candidate.test.named)).1
    cases clash
  · obtain ⟨_,⟨candidate⟩⟩ := whereList
    have clash := (List.cons.inj (shape.symm.trans candidate.test.named)).1
    cases clash
  · obtain ⟨_,⟨r⟩⟩ := record
    have h := a.single
    rw [older_residual_has_no_outputs419 r] at h
    cases h
  · obtain ⟨_,⟨r⟩⟩ := plain
    cases r with
    | actual rows old =>
      have clash := (List.cons.inj (shape.symm.trans old.head)).1
      cases clash
  · obtain ⟨_,⟨r⟩⟩ := rival
    cases r with
    | actual winner =>
      have impossible := congrArg List.length a.declaration.theOnlyOne
      rcases winner.ordered with h|h <;> simp [h] at impossible

end Yulang.GeneralDeclarativeI65.I72.ExplicitPick419
