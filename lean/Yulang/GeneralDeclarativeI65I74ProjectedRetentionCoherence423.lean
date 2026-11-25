import Yulang.GeneralDeclarativeI65I74ProjectedRetentionRead423

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423
open GeneralDeclarativeI65
open GeneralDeclarativeI65.I72.RecordEndpoints422
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Pattern)
open Checker408 (Problem)

private theorem authored_point_same423 {p : Problem} (a b : Read p) :
    a.ordinal = b.ordinal ∧ a.low.label = b.low.label ∧ a.arg = b.arg := by
  have sameDecl := (List.cons.inj (a.only.symm.trans b.only)).1
  have sameHead := (List.cons.inj (a.literal.symm.trans
    ((congrArg Declaration.head sameDecl).trans b.literal))).1
  have sameKey := (Pattern.record.inj sameHead).1
  have sameInput := (List.cons.inj (a.request.symm.trans b.request)).1
  let registry := (authoredRegistry p.state.core.current).declarations.map Declaration.id
  have A : registry[a.ordinal]? = some a.decl.id := by
    simp [registry,a.actualDecl]
  have B : registry[b.ordinal]? = some a.decl.id := by
    simp [registry,b.actualDecl,sameDecl]
  obtain ⟨bound,_⟩ := List.getElem?_eq_some_iff.mp A
  have sameOrd := (List.Nodup.getElem?_inj bound a.checked.1).mp (A.trans B.symm)
  exact ⟨sameOrd,sameKey,sameInput⟩

/-- Different valid retention wires can cite different existing rows,
but cannot choose a different actual associated value or a different
occurrence, declaration ordinal, output ordinal, or target. This is
semantic determinacy of value-side preparation in one unchanged
fitting model, not uniqueness of a classification. -/
theorem different_prepared_evidence_keeps_the_same_actual_write423
    {p : Problem} (a b : PreparedWrite p) (m : I72.Model) (fit : I72.Fits p.state m) :
    a.typed.actualRightValue m = b.typed.actualRightValue m := by
  obtain ⟨written,key,arg⟩ := authored_point_same423 a.original b.original
  obtain ⟨left,litA,_⟩ := prepared_write_preserves_full_projected_capture_and_actual_value423 a m fit
  obtain ⟨right,litB,_⟩ := prepared_write_preserves_full_projected_capture_and_actual_value423 b m fit
  have authored := left.atRequired
  rw [key,arg] at authored
  have actualType : left.required = right.required := Option.some.inj (authored.symm.trans right.atRequired)
  have sameOut : a.original.outIndex = b.original.outIndex := Fin.ext rfl
  have targetEq := congrArg (fun i : Fin p.root.demand.outputs.length => p.root.demand.outputs[i].target) sameOut
  simp only [litA,litB,written,targetEq,actualType]
  rfl

end Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423
