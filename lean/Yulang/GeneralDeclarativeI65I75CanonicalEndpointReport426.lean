import Yulang.GeneralDeclarativeI65I75ProjectedLeafEntry426

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423

open Checker408 (Problem Result)
open ProjectedCore425

/-- Internal evidence wiring at the exact projected-offer leaf. The
public R13 checker still does not call this branch. -/
theorem checked_projected_report_has_canonical_dictionary_evidence426
    {p : Problem} {tag : Nat} {r : Result} {w : ProjectedRowsWire426}
    (h : checkProjectedLeafReport426 p tag r w = true) :
    ∃ a : ProjectedLeafPacket426 p, checkableProjectedLeaf426 p w = some a ∧
      r = a.exactReport tag ∧
      ∀ m : I72.Model, Fits p.state m → DictionaryEvidence p.state m p.root a.original.dictionary := by
  obtain ⟨a,observed,_,exactReport,_⟩ :=
    checked_projected_leaf_original_report_and_fixed_target426 h
  exact ⟨a,observed,exactReport,fun m fit =>
    original_projected_leaf_with_retention_has_dictionary_evidence426 a.original a.retained m fit⟩

end Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423
