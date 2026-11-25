import Yulang.GeneralDeclarativeI65I75ProjectedReceipt425
import Yulang.GeneralDeclarativeI65I74ProjectedRetentionCoherence423

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423
open GeneralDeclarativeI65
open Checker408 (Problem)
open GeneralDictionaryAssociatedProvenance (Body)
open GeneralDeclarationPatterns (normalize)
open GeneralDeclarativeOutputs320 (bodyPattern)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)

private theorem exact_source_atlas_is_functional425
    {p : Problem} {j k : Nat} {i a : Fin p.root.demand.outputs.length} {b c : Body}
    {l : B6MixedRhs401 p.state.core false (normalize (bodyPattern b))}
    {r : B6MixedRhs401 p.state.core false (normalize (bodyPattern c))}
    (left : p.state.b6.read p.root j i b = some l)
    (right : p.state.b6.read p.root k a c = some r)
    (atDecl : j = k) (atOut : i = a) (atBody : b = c) : HEq l r := by
  cases atDecl
  cases atOut
  cases atBody
  exact heq_of_eq (Option.some.inj (left.symm.trans right))

/-- Two genuine reads of the same symbolic receipt in one exact State
may cite different retained ordinary rows. They cannot substitute a
different original authored body or B6 term. This is dependent
equality of the actual typed terms, not equivalence of their values. -/
theorem one_exact_receipt_replays_one_original_B6_term425
    {p : Problem} {a b : PrepareWire} {key d e}
    (left : readProjectedReceipt425 p a key = some d)
    (right : readProjectedReceipt425 p b key = some e) :
    d.original.decl = e.original.decl ∧ d.original.assoc = e.original.assoc ∧
    d.original.ordinal = e.original.ordinal ∧ d.original.outIndex = e.original.outIndex ∧
    HEq d.typed.plan e.typed.plan := by
  have L := (read_projected_receipt_is_exact425.mp left).2
  have R := (read_projected_receipt_is_exact425.mp right).2
  have sameKey := L.trans R.symm
  have ordinal : d.original.ordinal = e.original.ordinal :=
    congrArg ProjectedReceiptKey425.declarationOrdinal sameKey
  have output : d.original.outIndex = e.original.outIndex :=
    Fin.ext (congrArg ProjectedReceiptKey425.outputOrdinal sameKey)
  have declaredFirst := d.original.actualDecl
  rw [ordinal] at declaredFirst
  have decl := Option.some.inj (declaredFirst.symm.trans e.original.actualDecl)
  have authored : [d.original.assoc] = [e.original.assoc] := by
    rw [←d.original.actualAssoc,decl,e.original.actualAssoc]
  have body := (List.cons.inj authored).1
  exact ⟨decl,body,ordinal,output,exact_source_atlas_is_functional425
    d.typed.originalCompiled e.typed.originalCompiled ordinal output
    (congrArg Body.explicit body)⟩

/-- Preserve the exact original syntax and actual output simultaneously,
without making receipt identity depend on the selected fitting model. -/
theorem same_receipt_key_preserves_source_and_model_write425
    {p : Problem} {a b : PrepareWire} {key d e}
    (left : readProjectedReceipt425 p a key = some d)
    (right : readProjectedReceipt425 p b key = some e)
    (m : I72.Model) (fit : I72.Fits p.state m) :
    d.original.assoc = e.original.assoc ∧ HEq d.typed.plan e.typed.plan ∧
    d.typed.actualRightValue m = e.typed.actualRightValue m := by
  have src := one_exact_receipt_replays_one_original_B6_term425 left right
  exact ⟨src.2.1,src.2.2.2.2,different_prepared_evidence_keeps_the_same_actual_write423 d e m fit⟩

/-- The new read does not filter or substitute the earlier genuine raw
root-cycle check. Absence for any other reason is not a diagnosis. -/
theorem root_K2_blocks_projected_receipt_in_same_problem425 {p : Problem}
    (priority : RootCycle p.state p.root) (wire : PrepareWire) (key : ProjectedReceiptKey425) :
    readProjectedReceipt425 p wire key = none := by
  cases h : readProjectedReceipt425 p wire key with
  | none => rfl
  | some actual => exact (actual.original.rawSafe priority).elim

end Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423
