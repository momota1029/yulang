import Yulang.CommonPatternLookup
import Yulang.CommonCanonicalShapes
import Yulang.CaseDataTerms

/-! Exact Common producer types for concrete record insertion. Runtime
insertion removes hidden duplicate payloads; these lemmas connect that real
operation to ordinary producer record constructors, without a set-of-values
reinterpretation of Common subtyping. -/

namespace Yulang.CommonPatternConcreteRecordTypes

open Common (Ty Row Equivalent)

theorem finite_record_swap (first last : Nat) (different : first ≠ last)
    (a b tail : CommonFinite.Ty Row) :
    CommonFinite.ProducerEq Common.rowLe (.record first a (.record last b tail))
      (.record last b (.record first a tail)) := by
  have observed (rank : Nat) (environment : CommonFinite.Environment Row) (observation : CommonFinite.Observation Row) :
      CommonFinite.ProbeAt Common.rowLe rank environment (.record first a (.record last b tail)) observation ↔
        CommonFinite.ProbeAt Common.rowLe rank environment (.record last b (.record first a tail)) observation := by
    cases rank <;> cases observation <;>
      simp only [CommonFinite.ProbeAt, CommonFinite.ProbeStep, CommonFinite.MaskedProbeStep]
    all_goals try rfl
    all_goals rename_i query payload
    all_goals by_cases left : query = first <;> by_cases right : query = last <;>
      simp_all [CommonFinite.maskedProbeStep_or_trivial]
  exact ⟨(CommonFinite.producerLe_iff_probe _ _).mpr (fun rank environment observation => (observed rank environment observation).mpr),
    (CommonFinite.producerLe_iff_probe _ _).mpr (fun rank environment observation => (observed rank environment observation).mp)⟩

theorem record_swap (first last : Nat) (different : first ≠ last) (a b tail : Ty) :
    Equivalent (Common.record first a (Common.record last b tail))
      (Common.record last b (Common.record first a tail)) := by
  constructor <;> intro depth
  · exact (finite_record_swap first last different _ _ _).1
  · exact (finite_record_swap first last different _ _ _).2

def recordTypeOf (type : A → Ty) : List (Nat × A) → Ty
  | [] => Common.exactEmpty
  | (name, value) :: rest => Common.record name (type value) (recordTypeOf type rest)

theorem recordTypeOf_width (type : A → Ty) (fields : List (Nat × A)) :
    Common.Subtype (recordTypeOf type fields) Common.emptyRecord := by
  cases fields with
  | nil => exact Common.exactEmpty_below_width
  | cons field rest =>
      intro depth
      apply (CommonFinite.producerLe_iff_probe _ _).mpr
      intro rank environment observation accepted
      cases rank <;> cases observation <;>
        simp_all [recordTypeOf, Common.observeTy, Common.record, Common.emptyRecord, CommonSyntax.Layer.evalAt,
          CommonFinite.ProbeAt, CommonFinite.ProbeStep,
          CommonFinite.MaskedProbeStep]

theorem record_congr (label : Nat) {a b tail rest : Ty} (head : Equivalent a b) (remaining : Equivalent tail rest) :
    Equivalent (Common.record label a tail) (Common.record label b rest) :=
  ⟨Common.common_record_mono label head.1 remaining.1, Common.common_record_mono label head.2 remaining.2⟩

theorem insert_filter_exact (type : A → Ty) (name : Nat) (value : A) (fields : List (Nat × A)) :
    Equivalent (Common.record name (type value) (recordTypeOf type (fields.filter (fun field => field.1 != name))))
      (Common.record name (type value) (recordTypeOf type fields)) := by
  induction fields with
  | nil => exact Common.equivalent_refl _
  | cons field rest ih =>
      rcases field with ⟨current, item⟩
      by_cases same : current = name
      · subst current
        simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, recordTypeOf]
        exact Common.equivalent_trans ih (Common.equivalent_symm (Common.common_shadowed_head_equivalent name _ _ _))
      · simp only [List.filter_cons, bne_iff_ne.mpr same, ↓reduceIte, recordTypeOf]
        exact Common.equivalent_trans (record_swap name current (Ne.symm same) _ _ _)
          (Common.equivalent_trans (record_congr current (Common.equivalent_refl _) ih)
            (Common.equivalent_symm (record_swap name current (Ne.symm same) _ _ _)))

/-- Actual duplicate-removing insertion, all payload Common types and all
finite source record fields. No presence/success/inhabitation premise. -/
theorem insert_exact (type : CaseValues.Value F → Ty) (name : Nat) (value : CaseValues.Value F)
    (fields : CaseValues.Bindings F) :
    Equivalent (recordTypeOf type (CaseDataTerms.insert name value fields))
      (Common.record name (type value) (recordTypeOf type fields)) :=
  insert_filter_exact type name value fields

theorem optional_absorb_trivial (environment : CommonFinite.Environment Row)
    (order : CommonFinite.Ty Row → CommonFinite.Ty Row → Prop) (tail : CommonFinite.Ty Row)
    (records : CommonFinite.MaskedProbeStep Common.rowLe environment order [] tail .records)
    (label : Nat) (observation : CommonFinite.Observation Row) :
    (CommonFinite.MaskedProbeStep Common.rowLe environment order [] tail (.optional label observation) ∨ observation = .trivial) ↔
      CommonFinite.MaskedProbeStep Common.rowLe environment order [] tail (.optional label observation) := by
  by_cases trivial : observation = .trivial
  · subst observation
    simp only [CommonFinite.maskedProbeStep_optional_trivial, records, true_or]
  · simp [trivial]

theorem finite_default_record_other (label current : Nat) (different : label ≠ current)
    (head tail fallback : CommonFinite.Ty Row) (width : CommonFinite.ProducerLe Common.rowLe tail .emptyRecord) :
    CommonFinite.ProducerEq Common.rowLe (.recordDefault label (.record current head tail) fallback)
      (.record current head (.recordDefault label tail fallback)) := by
  have observed (rank : Nat) (environment : CommonFinite.Environment Row) (observation : CommonFinite.Observation Row) :
      CommonFinite.ProbeAt Common.rowLe rank environment (.recordDefault label (.record current head tail) fallback) observation ↔
        CommonFinite.ProbeAt Common.rowLe rank environment (.record current head (.recordDefault label tail fallback)) observation := by
    have records : CommonFinite.ProbeAt Common.rowLe rank environment tail .records :=
      (CommonFinite.producerLe_iff_probe _ _).mp width rank environment .records (by cases rank <;> trivial)
    cases rank <;> cases observation <;>
      simp only [CommonFinite.ProbeAt, CommonFinite.ProbeStep, CommonFinite.MaskedProbeStep] at records ⊢
    all_goals try rfl
    all_goals rename_i query payload
    all_goals by_cases selected : query = label <;> by_cases existing : query = current <;>
      simp_all [optional_absorb_trivial _ _ _ records, CommonFinite.maskedProbeStep_or_trivial]
  exact ⟨(CommonFinite.producerLe_iff_probe _ _).mpr (fun rank environment observation => (observed rank environment observation).mpr),
    (CommonFinite.producerLe_iff_probe _ _).mpr (fun rank environment observation => (observed rank environment observation).mp)⟩

theorem default_record_other (label current : Nat) (different : label ≠ current) (head tail fallback : Ty)
    (width : Common.Subtype tail Common.emptyRecord) :
    Equivalent (Common.recordDefault label (Common.record current head tail) fallback)
      (Common.record current head (Common.recordDefault label tail fallback)) := by
  constructor <;> intro depth
  · cases depth with
    | zero => exact (finite_record_swap label current different _ _ _).1
    | succ depth => exact (finite_default_record_other label current different _ _ _ (width _)).1
  · cases depth with
    | zero => exact (finite_record_swap label current different _ _ _).2
    | succ depth => exact (finite_default_record_other label current different _ _ _ (width _)).2

/-- Actual strict default insertion retains a present field and appends an
absent one. Its full finite record type equals the Common default image. -/
theorem insertDefault_exact (type : CaseValues.Value F → Ty) (name : Nat) (value : CaseValues.Value F)
    (fields : CaseValues.Bindings F) :
    Equivalent (recordTypeOf type (CaseDataTerms.insertDefault name value fields))
      (Common.recordDefault name (recordTypeOf type fields) (type value)) := by
  induction fields with
  | nil =>
      exact Common.equivalent_symm (Common.default_exactEmpty name (type value))
  | cons field rest ih =>
      rcases field with ⟨current, item⟩
      by_cases same : name = current
      · subst current
        simp only [CaseDataTerms.insertDefault, CaseValues.lookup, ↓reduceIte, Option.isSome_some, recordTypeOf]
        exact Common.equivalent_symm (Common.default_present_record name _ _ _)
      · have unchanged : CaseDataTerms.insertDefault name value ((current, item) :: rest) =
            (current, item) :: CaseDataTerms.insertDefault name value rest := by
          simp only [CaseDataTerms.insertDefault, CaseValues.lookup, same, ↓reduceIte]
          split <;> rfl
        rw [unchanged]
        exact Common.equivalent_trans (record_congr current (Common.equivalent_refl _) ih)
          (Common.equivalent_symm (default_record_other name current same _ _ _ (recordTypeOf_width type rest)))

end Yulang.CommonPatternConcreteRecordTypes
