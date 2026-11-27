import Yulang.GeneralDeclarativeI65I74ProjectedField464
import Yulang.GeneralDeclarativeI65I74OrderedProjectionDerivation464

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.NamedProjection464
open GeneralDeclarativeHead320 (Equation Models)
private abbrev RawState := GeneralDeclarativeHead320.State
open GeneralDeclarativeK2Graph321.AddAtOneSource
open GeneralDeclarativeWitnessLiteral349 (sameRows rows_exact)

def exactOrdinaryState (a b : RawState) : Bool :=
  (decide (a.normal.ordinary = b.normal.ordinary) &&
   decide (a.normal.intervals = b.normal.intervals)) && sameRows a.equations b.equations

theorem exact_ordinary_snapshot_iff (a b : RawState) : exactOrdinaryState a b = true ↔ a = b := by
  rcases a with ⟨⟨aa,ab⟩,ar⟩
  rcases b with ⟨⟨ba,bb⟩,br⟩
  simp only [exactOrdinaryState,Bool.and_eq_true,decide_eq_true_eq,rows_exact]
  constructor
  · rintro ⟨⟨rfl,rfl⟩,rfl⟩
    rfl
  · intro equal
    cases equal
    exact ⟨⟨rfl,rfl⟩,rfl⟩

/-- The new equations are read from the exact suffix of the separately
supplied target state. The certificate carries only proofs and cuts,
never a second copy of the equation data. -/
def attachCertificate : List Equation → List ProjectionWire → Option (List DerivedAppendData)
  | [],[] => some []
  | row::rows,w::rest =>
    (attachCertificate rows rest).map fun parsed => ⟨⟨row,w.cut⟩,w.equality⟩ :: parsed
  | _,_ => none

private theorem attached_to_actual_rows {rows : List Equation} {w : List ProjectionWire}
    {bound : List DerivedAppendData} (found : attachCertificate rows w = some bound) :
    bound.map (fun d => d.checked.row) = rows := by
  induction rows generalizing w bound with
  | nil =>
    cases w <;> simp [attachCertificate] at found
    subst bound
    rfl
  | cons r rst ih =>
    cases w with
    | nil => simp [attachCertificate] at found
    | cons x tail =>
      cases attached : attachCertificate rst tail with
      | none => simp [attachCertificate,attached] at found
      | some doneProofs =>
        have action : ⟨⟨r,x.cut⟩,x.equality⟩ :: doneProofs = bound := by
          simpa [attachCertificate,attached] using found
        subst bound
        simp [ih attached]

private theorem attach_recovers_any_derived_batch (bound : List DerivedAppendData) :
    attachCertificate (bound.map fun d => d.checked.row)
      (bound.map fun d => ⟨d.derivation,d.checked.cut⟩) = some bound := by
  induction bound with
  | nil => rfl
  | cons d ds ih =>
    rcases d with ⟨⟨row,cut⟩,proof⟩
    simp [attachCertificate,ih]

def suppliedRows (pre post : RawState) : List Equation :=
  post.equations.drop pre.equations.length

def checkSuppliedBatch (pre post : RawState) (w : List ProjectionWire) : Bool :=
  ((attachCertificate (suppliedRows pre post) w).bind (readDerivedAppends pre)).any
    (exactOrdinaryState post)

def ActualSuppliedBatch (pre post : RawState) : Prop :=
  OrderedSafeAppends pre (suppliedRows pre post) post ∧
    AllDeriveInActualPrefix pre (suppliedRows pre post)

theorem checked_batch_has_exact_independent_supplied_prefix_evidence
    {pre post : RawState} {w : List ProjectionWire}
    (checked : checkSuppliedBatch pre post w = true) : ActualSuppliedBatch pre post := by
  cases bound : attachCertificate (suppliedRows pre post) w with
  | none => simp [checkSuppliedBatch,bound,Option.bind] at checked
  | some actual =>
    cases ran : readDerivedAppends pre actual with
    | none => simp [checkSuppliedBatch,bound,ran,Option.bind] at checked
    | some target =>
      have eq : post = target := (exact_ordinary_snapshot_iff ..).mp
        (by simpa [checkSuppliedBatch,bound,ran,Option.bind] using checked)
      subst target
      have u := read_derived_batch_validates_exact_supplied_source_proofs_and_cut ran
      simpa only [ActualSuppliedBatch,attached_to_actual_rows bound] using u

theorem exact_supplied_phase_iff_finite_prefix_proof_data (pre post : RawState) :
    ActualSuppliedBatch pre post ↔ ∃ w, checkSuppliedBatch pre post w = true := by
  constructor
  · intro proof
    obtain ⟨records,same,ran⟩ := independent_source_and_structural_batch_has_finite_derived_wire proof.1 proof.2
    refine ⟨records.map fun d => ⟨d.derivation,d.checked.cut⟩,?_⟩
    have attach := attach_recovers_any_derived_batch records
    rw [same] at attach
    simp [checkSuppliedBatch,attach,ran,Option.bind,(exact_ordinary_snapshot_iff post post).mpr rfl]
  · rintro ⟨_,checks⟩
    exact checked_batch_has_exact_independent_supplied_prefix_evidence checks

theorem checked_batch_compares_to_the_exact_actual_suffix (pre post : RawState) (h : ActualSuppliedBatch pre post) :
    post.normal = pre.normal ∧ post.equations = pre.equations ++ suppliedRows pre post :=
  literal_row_order_and_ordinary_constraints_are_exact h.1

theorem actual_supplied_batch_preserves_all_ordinary_models
    {pre post : RawState} (h : ActualSuppliedBatch pre post) (m) :
    Models post m ↔ Models pre m := by
  obtain ⟨_,_,ran⟩ := independent_source_and_structural_batch_has_finite_derived_wire h.1 h.2
  exact (checked_derived_batch_preserves_all_exact_ordinary_models_and_raw_cycles ran m 0).1

end Yulang.GeneralDeclarativeI65.I72.NamedProjection464
