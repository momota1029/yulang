import Yulang.GeneralDeclarativeI65I74ExplicitPickPriority419

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ExplicitPick419
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessDeclaredState357 (point authoredRegistry)
open GeneralDeclarationPatterns (Pattern)
open Checker408 (Problem Result)

/-- The original occupied input, not a witness row locator, determines
the logical names used by the record head. -/
private theorem one_member_when_length_one419 {α : Type} {xs : List α}
    (single : xs.length = 1) {a b : α} (left : a ∈ xs) (right : b ∈ xs) :
    a = b := by
  cases xs with
  | nil => cases left
  | cons head tail =>
    cases tail with
    | nil => exact (List.mem_singleton.mp left).trans (List.mem_singleton.mp right).symm
    | cons _ _ => simp at single

theorem actual_sources_agree_on_input_and_residual419 {p} (a b : Rows p) :
    a.root = b.root ∧ a.x = b.x ∧ a.intSlot = b.intSlot ∧ a.y = b.y ∧
    a.strSlot = b.strSlot ∧ a.residual = b.residual := by
  have root := congrArg GeneralDeclarativeWhere319.Capture.center
    (List.cons.inj (a.requested.symm.trans b.requested)).1
  change a.root = b.root at root
  have left : a.original ∈ p.state.core.origins.filter (fun src => src.slot == a.root) := by
    simp [a.actualOriginal,a.originalRoot]
  have right : b.original ∈ p.state.core.origins.filter (fun src => src.slot == a.root) := by
    simp [b.actualOriginal,b.originalRoot,root]
  have original := one_member_when_length_one419 a.originalCount left right
  have sameLiteral := a.source.symm.trans ((congrArg Origin.endpoint original).trans b.source)
  have EqNames : a.x = b.x ∧ a.intSlot = b.intSlot ∧ a.y = b.y ∧ a.strSlot = b.strSlot := by
    simpa [ClosedResidual415.wholeOriginal] using sameLiteral
  obtain ⟨x,field,y,rest⟩ := EqNames
  have k := b.uniqueSplit
  rw [← root,← x,← field] at k
  have residual := (List.cons.inj (a.uniqueSplit.symm.trans k)).1
  have tails : a.residual = b.residual := by simpa [OpenTail414.openRow] using residual
  exact ⟨root,x,field,y,rest,tails⟩

theorem actual_packets_agree_on_the_literal_ledger419 {p} (a b : PickPacket p) :
    a.retained.write = b.retained.write := by
  have decl := (List.cons.inj (a.declaration.theOnlyOne.symm.trans b.declaration.theOnlyOne)).1
  have rows := actual_sources_agree_on_input_and_residual419 a.rows b.rows
  have head := (List.cons.inj (a.declaration.literal.symm.trans
    ((congrArg Declaration.head decl).trans b.declaration.literal))).1
  have binder := (Pattern.var.inj ((Pattern.record.inj head).2.1))
  have output := (List.cons.inj (a.declaration.exactlyWritten.symm.trans
    ((congrArg Declaration.associated decl).trans b.declaration.exactlyWritten))).1
  let table := (authoredRegistry p.state.core.current).declarations.map Declaration.id
  have left : table[a.declaration.ordinal]? = some a.declaration.decl.id := by
    simp [table,a.declaration.authored]
  have right : table[b.declaration.ordinal]? = some a.declaration.decl.id := by
    simp [table,b.declaration.authored,decl]
  obtain ⟨bound,_⟩ := List.getElem?_eq_some_iff.mp left
  have ordinal := (List.Nodup.getElem?_inj bound a.declaration.checked.1).mp (left.trans right.symm)
  apply (eq_write419 _ _).mp
  simp only [eqWrite, RetainedOutput.write, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨True.intro,ordinal,True.intro,True.intro,True.intro,?_⟩,?_⟩
  · rw [a.actualBody,b.actualBody,output]
  · change eqWire a.retained.write.typedRhs b.retained.write.typedRhs = true
    rw [typed_ledger_uses_original_binder_and_all_actual_point_names419,
      typed_ledger_uses_original_binder_and_all_actual_point_names419,binder,rows.2.2.1]
    exact (eq_wire419 _ _).mpr rfl

/-- All successful constructors of the new checker agree on both the real
selected declaration and the exact ordered typed ledger, in this scope. -/
theorem check_cannot_change_report_at_actual_Pick419 (p : Problem) (a : PickPacket p)
    (r : Result) (w : Witness) (yes : check p r w = true) :
    r = pickReport a := by
  cases w with
  | previous old =>
    change RigidRival418.check p r old = true at yes
    rw [previous_checker_is_disjoint_for_actual_Pick419 p r a old] at yes
    cases yes
  | explicitPick wire =>
    obtain ⟨b,_,report⟩ := checked_report_uses_original_pick419 yes
    rw [report]
    have decl := (List.cons.inj (a.declaration.theOnlyOne.symm.trans b.declaration.theOnlyOne)).1
    simp only [pickReport,decl,actual_packets_agree_on_the_literal_ledger419 a b]
  | unsupported => simp [check] at yes

end Yulang.GeneralDeclarativeI65.I72.ExplicitPick419
