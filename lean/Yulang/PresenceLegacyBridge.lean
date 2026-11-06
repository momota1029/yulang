import Yulang.PresenceDataCompatibility

/-!
# Compositional legacy data demands inside the presence model

The translation uses the presence model's base/product/variant predicates and
required-field demands. It translates the old width type `{}` to `records`,
never to exact emptiness or absence. A finite list of shadowed labels removes
older requirements, including below unions and intersections in an opaque tail.
`translate_exact` proves agreement with the independently defined legacy
`DataTypeSemantics.Holds` for every type, mask list and runtime value.

This is a first-order data interpretation. Legacy arrows translate to `never`
because the old data runtime has no closures; the operational transfer theorem
retains its explicit data-support premise. No function interpretation, regular
recursive-type interpretation, equality of the two principal-type notions, or
new whole-core solver is asserted.
-/

namespace Yulang.PresenceLegacyBridge

open SourceDataRuntime (Value)
open StructuralBase (Ty)

universe u
variable {Row : Type u}

/-- A finite required-field demand, with first-field-wins shadowing. The record
case uses logical demand intersection, not the presence constructor image. -/
def translate : Ty Row → List Nat → PresenceDataTypes.Ty
  | .bottom, _ => PresenceDataTypes.never
  | .top, _ => PresenceDataTypes.any
  | .base name, _ => PresenceDataTypes.base name
  | .union left right, hidden =>
      PresenceDataTypes.union (translate left hidden) (translate right hidden)
  | .inter left right, hidden =>
      PresenceDataTypes.inter (translate left hidden) (translate right hidden)
  | .pair left right, _ => PresenceDataTypes.pair (translate left []) (translate right [])
  | .emptyRecord, _ => PresenceDataTypes.records
  | .record label head tail, hidden =>
      PresenceDataTypes.inter
        (if label ∈ hidden then PresenceDataTypes.records
          else PresenceDataTypes.required label (translate head []))
        (translate tail (label :: hidden))
  | .variant label payload, _ => PresenceDataTypes.variant label (translate payload [])
  | .arrow _ _ _ _, _ => PresenceDataTypes.never

/-- The translation is exact for the existing, separately defined data meaning.
No subtype or inference hypothesis is needed. -/
theorem translate_exact (type : Ty Row) (hidden : List Nat) (value : Value) :
    translate type hidden value ↔
      DataTypeSemantics.Holds type (fun label => label ∈ hidden) value := by
  have emptyMask : (fun label => label ∈ ([] : List Nat)) = DataTypeSemantics.visible := by
    funext label
    simp [DataTypeSemantics.visible]
  induction type generalizing hidden value with
  | bottom | top => rfl
  | base name =>
      cases value <;>
        simp [translate, PresenceDataTypes.base, PresenceDataTypes.exact, DataTypeSemantics.Holds]
  | union left right ihl ihr => exact or_congr (ihl hidden value) (ihr hidden value)
  | inter left right ihl ihr => exact and_congr (ihl hidden value) (ihr hidden value)
  | pair left right ihl ihr =>
      cases value with
      | base | record | variant => rfl
      | pair first last =>
          change (translate left [] first ∧ translate right [] last) ↔ _
          have firstExact := ihl [] first
          have lastExact := ihr [] last
          rw [emptyMask] at firstExact lastExact
          exact and_congr firstExact lastExact
  | emptyRecord => cases value <;> rfl
  | record label head tail ihh iht =>
      cases value with
      | base | pair | variant =>
          by_cases masked : label ∈ hidden <;>
            simp [translate, PresenceDataTypes.inter, PresenceDataTypes.records,
              PresenceDataTypes.required, masked, DataTypeSemantics.Holds]
      | record fields =>
          have headExact (item : Value) : translate head [] item ↔
              DataTypeSemantics.Holds head DataTypeSemantics.visible item := by
            have exactHead := ihh [] item
            rwa [emptyMask] at exactHead
          have tailExact : translate tail (label :: hidden) (.record fields) ↔
              DataTypeSemantics.Holds tail
                (DataTypeSemantics.hide label (fun query => query ∈ hidden)) (.record fields) := by
            have consMask : (fun query => query ∈ label :: hidden) =
                DataTypeSemantics.hide label (fun query => query ∈ hidden) := by
              funext query
              simp [DataTypeSemantics.hide]
            have exactTail := iht (label :: hidden) (.record fields)
            rwa [consMask] at exactTail
          by_cases masked : label ∈ hidden <;>
            simp [translate, PresenceDataTypes.inter, PresenceDataTypes.records,
              PresenceDataTypes.required, PresenceDataTypes.lookup, masked,
              DataTypeSemantics.Holds, headExact, tailExact]
  | variant label payload ih =>
      cases value with
      | base | pair | record => rfl
      | variant actual item =>
          change (actual = label ∧ translate payload [] item) ↔ _
          have exactPayload := ih [] item
          rw [emptyMask] at exactPayload
          exact and_congr (Iff.rfl (a := actual = label)) exactPayload
  | arrow => rfl

theorem translate_visible (type : Ty Row) (value : Value) :
    translate type [] value ↔ DataTypeSemantics.Holds type DataTypeSemantics.visible value := by
  have emptyMask : (fun label => label ∈ ([] : List Nat)) = DataTypeSemantics.visible := by
    funext label
    simp [DataTypeSemantics.visible]
  rw [← emptyMask]
  exact translate_exact type [] value

/-- Legacy `{l : A, ..{}}` becomes precisely a required-field demand. -/
theorem translate_required (label : Nat) (payload : Ty Row) (value : Value) :
    translate (.record label payload .emptyRecord) [] value ↔
      PresenceDataTypes.required label (translate payload []) value := by
  cases value <;>
    simp [translate, PresenceDataTypes.inter, PresenceDataTypes.required,
      PresenceDataTypes.records, PresenceDataTypes.lookup]

/-- Hidden-field elimination is retained for arbitrary, possibly nonrigid tails. -/
theorem translate_shadow (label : Nat) (head hiddenPayload tail : Ty Row)
    (hidden : List Nat) (value : Value) :
    translate (.record label head (.record label hiddenPayload tail)) hidden value ↔
      translate (.record label head tail) hidden value := by
  rw [translate_exact, translate_exact]
  exact DataTypeSemantics.record_shadow label head hiddenPayload tail _ value

/-- Subtyping transfers to predicate inclusion; no converse is claimed. -/
theorem shadow_subtype_preserved {leRow : Row → Row → Prop}
    {source target : Ty Row} (below : ShadowSemanticRecords.Subtype leRow source target)
    (hidden : List Nat) :
    PresenceDataTypes.Le (translate source hidden) (translate target hidden) := by
  intro value valid
  exact (translate_exact target hidden value).mpr
    (ShadowDataSafety.subtype_preserves below _ value
      ((translate_exact source hidden value).mp valid))

/-- Any closed supported source derivation in the raw Shadow model yields a
presence-data derivation of the translated target, with the same actual source. -/
theorem closed_typing_translates (algebra : RowFlowSchemes.Algebra Row)
    (expression : Inference.Expr) (supported : SourceDataRuntime.Supported expression)
    (target : Inference.Comp (ShadowRecordValueInference.model algebra))
    (typed : Inference.Typing (ShadowRecordValueInference.model algebra) [] expression target) :
    PresenceDataInference.Typing [] expression (translate target.1 []) := by
  apply (PresenceDataCompatibility.exact_typing_iff_evaluates [] expression
    (translate target.1 [])).mpr
  obtain ⟨value, evaluated, valid⟩ :=
    ShadowDataSafety.typing_evaluates algebra expression supported target typed
  exact ⟨value, evaluated, (translate_visible target.1 value).mpr valid⟩

/-- Every free parameter of an accepted legacy finite-data plan describes the
same new exact descriptor. This validates all instances without identifying the
old free-parameter scheme with the new closed exact descriptor. -/
theorem legacy_data_plan_translates (algebra : RowFlowSchemes.Algebra Row)
    (expression : Inference.Expr) (plan : RigidRecordValueInference.Plan)
    (inferred : RigidRecordValueInference.infer expression = .inferred plan) :
    ∃ shape, PresenceDataInference.infer expression = .solved shape ∧
      ∀ parameter : plan.Parameters (Ty Row),
        PresenceDataTypes.Le shape.denote (translate (plan.evaluate parameter) []) := by
  obtain ⟨value, evaluated, allInstances⟩ :=
    SourceDataSafety.inferred_evaluates algebra expression plan inferred
  obtain ⟨shape, solved, same⟩ :=
    (PresenceDataCompatibility.eval_success_iff_infer expression value).mp evaluated
  refine ⟨shape, solved, ?_⟩
  intro parameter
  have valid : translate (plan.evaluate parameter) [] shape.value := by
    apply (translate_visible _ _).mpr
    simpa [same] using allInstances parameter
  exact (shape.denote_le_iff (translate (plan.evaluate parameter) [])).mpr valid

/-- Optionality is a union of absence and a present required payload, not a
union with the old width-supertype `{}`. This law uses the existing semantics. -/
theorem optional_iff_absent_or_required (label : Nat) (payload : PresenceDataTypes.Ty)
    (value : Value) :
    PresenceDataTypes.optional label payload value ↔
      PresenceDataTypes.lacks label value ∨ PresenceDataTypes.required label payload value := by
  constructor
  · intro valid
    cases found : PresenceDataTypes.lookup label value with
    | none => exact Or.inl ⟨valid.1, found⟩
    | some item => exact Or.inr ⟨valid.1, item, found, valid.2 item found⟩
  · intro valid
    exact valid.elim (PresenceDataTypes.lacks_optional label payload value)
      (PresenceDataTypes.required_optional label payload value)

theorem optional_never_iff_absent (label : Nat) (value : Value) :
    PresenceDataTypes.optional label PresenceDataTypes.never value ↔
      PresenceDataTypes.lacks label value := by
  rw [optional_iff_absent_or_required]
  constructor
  · intro valid
    rcases valid with absent | ⟨_, item, _, impossible⟩
    · exact absent
    · exact False.elim impossible
  · exact Or.inl

/-- Width information carries no absence information for any field. -/
theorem legacy_emptyRecord_not_absence (label : Nat) :
    ¬ PresenceDataTypes.Le (translate (.emptyRecord : Ty Row) [])
      (PresenceDataTypes.lacks label) := PresenceDataTypes.records_not_le_lacks label

theorem legacy_emptyRecord_not_exactEmpty :
    ¬ PresenceDataTypes.Le (translate (.emptyRecord : Ty Row) [])
      PresenceDataTypes.exactEmpty := PresenceDataTypes.records_not_le_exactEmpty

end Yulang.PresenceLegacyBridge
