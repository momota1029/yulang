import Yulang.GeneralDeclarativeI65I74ProjectionBatchInput464

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.NamedProjection464
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeK2Graph321.AddAtOneSource
private abbrev RawState := GeneralDeclarativeHead320.State

def exact_single_suffix_owner (pre post : RawState) (site : Nat) : Bool :=
  match suppliedRows pre post with
  | [row] => decide (row.left = site)
  | _ => false

private theorem anchored_append_really_has_exactly_one_row
    (pre : RawState) (e : Equation) :
    suppliedRows pre (extendedRows pre e) = [e] := by
  simp [suppliedRows,extendedRows]

theorem same_wire_single_row_is_exact_specialization_of_batch_guard
    (pre post : RawState) (site : Nat) (w : ProjectionWire) :
    checkProjection pre post site w =
        (checkSuppliedBatch pre post [w] && exact_single_suffix_owner pre post site) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro accepted
    cases seen : post.equations[pre.equations.length]? with
    | none => simp [checkProjection,seen] at accepted
    | some row =>
      have parsed : exactOrderedAppend pre post row = true ∧
          (row.left = site ∧ Derivation.checkEq pre (.variable site) row.right w.equality = true) ∧
          checksNamedProjectionCut pre site row.right w.cut = true := by
        simpa [checkProjection,seen,Bool.and_eq_true,and_assoc] using accepted
      obtain ⟨exact,literal,cut⟩ := parsed
      have appended := (checks_single_ordered_extension_exactly ..).mp exact
      subst post
      have ok : readDerivedAppends pre [⟨⟨row,w.cut⟩,w.equality⟩] = some (extendedRows pre row) := by
        simp [readDerivedAppends,literal.1,literal.2,cut]
      simp [checkSuppliedBatch,exact_single_suffix_owner,anchored_append_really_has_exactly_one_row,
        attachCertificate,Option.bind,ok,(exact_ordinary_snapshot_iff ..).mpr rfl,literal.1]
  · intro accepted
    obtain ⟨proof,signed⟩ := Bool.and_eq_true_iff.mp accepted
    cases suffix : suppliedRows pre post with
    | nil => simp [exact_single_suffix_owner,suffix] at signed
    | cons row rest =>
      cases rest with
      | cons more tail => simp [exact_single_suffix_owner,suffix] at signed
      | nil =>
        have owner : row.left = site := by simpa [exact_single_suffix_owner,suffix] using signed
        have lookup : post.equations[pre.equations.length]? = some row := by
          have ix := congrArg (fun xs : List Equation => xs[0]?) suffix
          simpa [suppliedRows,List.getElem?_drop] using ix
        by_cases step : Derivation.checkEq pre (.variable row.left) row.right w.equality = true ∧
            checksNamedProjectionCut pre row.left row.right w.cut = true
        · have full : post = extendedRows pre row := by
            apply (exact_ordinary_snapshot_iff ..).mp
            simpa [checkSuppliedBatch,suffix,attachCertificate,Option.bind,
              readDerivedAppends,step.1,step.2] using proof
          rw [checkProjection,lookup]
          simp [(checks_single_ordered_extension_exactly ..).mpr full,←owner,step.1,step.2]
        · simp [checkSuppliedBatch,suffix,attachCertificate,Option.bind,readDerivedAppends,
             Bool.and_eq_true,step] at proof

end Yulang.GeneralDeclarativeI65.I72.NamedProjection464
