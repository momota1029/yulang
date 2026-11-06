import Yulang.CasePatternSafety

/-!
# Declared presence validation and the concrete-value/marker bridge

A default pattern on a resolved optional field is permitted; one on a
resolved required field is rejected (spec §3b.3). `unknown` is an unresolved
metadata result, not an acceptance or rejection policy for source inference.
The declaration/elaboration pass that supplies this metadata is not proved.

The executable projection below erases literal contents from the base,
pair, record and variant fragment into `SourceDataRuntime` values. A float,
list or nominal value has no projection in this legacy marker universe.
Projection preserves field lookup. This connects the existing presence types
to actual concrete pattern binding, including the union with a lazy default.
-/

namespace Yulang.CasePresenceValidation

open CaseValues LiteralValues EvaluationTrace

inductive Presence where
  | required | optional | unknown
  deriving DecidableEq, Repr

inductive DefaultVerdict where
  | allowed | rejectedRequired | unresolved
  deriving DecidableEq, Repr

def validateDefault : Presence → DefaultVerdict
  | .required => .rejectedRequired
  | .optional => .allowed
  | .unknown => .unresolved

inductive DefaultAllowed : Presence → Prop where
  | optional : DefaultAllowed .optional

@[simp] theorem validateDefault_exact (presence : Presence) :
    validateDefault presence = .allowed ↔ DefaultAllowed presence := by
  cases presence with
  | required => constructor <;> intro impossible <;> cases impossible
  | optional => exact ⟨fun _ => .optional, fun _ => rfl⟩
  | unknown => constructor <;> intro impossible <;> cases impossible

/-- The required-field rule is a metadata check, not semantic subtyping:
a required input is also a subtype of an optional payload demand. -/
theorem required_default_rejected : validateDefault .required = .rejectedRequired := rfl

theorem unknown_not_accepted : validateDefault .unknown ≠ .allowed := by decide

mutual
  def erase : Value F → Option SourceDataRuntime.Value
    | .literal value => value.legacyBase.map SourceDataRuntime.Value.base
    | .pair first last => do
        let left ← erase first
        let right ← erase last
        return .pair left right
    | .record fields => (eraseFields fields).map SourceDataRuntime.Value.record
    | .variant tag payload => (erase payload).map (SourceDataRuntime.Value.variant tag)
    | .nominal _ _ _ | .list _ => none

  def eraseFields : Bindings F → Option (List (Nat × SourceDataRuntime.Value))
    | [] => some []
    | (name, value) :: fields => do
        let erased ← erase value
        let rest ← eraseFields fields
        return (name, erased) :: rest
end

def pullback (type : PresenceDataTypes.Ty) : Ty F :=
  fun value => ∃ erased, erase value = some erased ∧ type erased

theorem erase_record_iff (value : Value F) (erasedFields : List (Nat × SourceDataRuntime.Value)) :
    erase value = some (.record erasedFields) ↔
      ∃ fields, value = .record fields ∧ eraseFields fields = some erasedFields := by
  cases value <;> simp [erase, Option.bind_eq_some_iff, Option.map_eq_some_iff]

/-- Every successfully projected record retains the first matching field,
and no present concrete field is erased into a missing marker. -/
theorem projected_lookup (fields : Bindings F) (erasedFields : List (Nat × SourceDataRuntime.Value))
    (projected : eraseFields fields = some erasedFields) (name : Nat) :
    match lookup name fields with
    | none => SourceDataRuntime.Fields.lookup name erasedFields = none
    | some value => ∃ erased, erase value = some erased ∧
        SourceDataRuntime.Fields.lookup name erasedFields = some erased := by
  induction fields generalizing erasedFields with
  | nil =>
      have same : erasedFields = [] := (Option.some.inj projected).symm
      subst erasedFields
      rfl
  | cons field fields ih =>
      obtain ⟨label, value⟩ := field
      cases hv : erase value with
      | none => simp [eraseFields, hv] at projected
      | some erased =>
          cases hf : eraseFields fields with
          | none => simp [eraseFields, hv, hf] at projected
          | some rest =>
              have same : (label, erased) :: rest = erasedFields := by
                simpa [eraseFields, hv, hf] using projected
              subst erasedFields
              by_cases isName : name = label
              · simp [lookup, SourceDataRuntime.Fields.lookup, isName, hv]
              · simpa [lookup, SourceDataRuntime.Fields.lookup, isName] using ih rest hf

theorem lookup_projection (fields : Bindings F) (erasedFields : List (Nat × SourceDataRuntime.Value))
    (projected : eraseFields fields = some erasedFields) (name : Nat) :
    (lookup name fields).bind erase = SourceDataRuntime.Fields.lookup name erasedFields := by
  have corresponding := projected_lookup fields erasedFields projected name
  cases found : lookup name fields with
  | none =>
      rw [found] at corresponding
      exact corresponding.symm
  | some value =>
      rw [found] at corresponding
      obtain ⟨erased, successful, same⟩ := corresponding
      simp [successful, same]

theorem optional_projected_iff (fields : Bindings F)
    (erasedFields : List (Nat × SourceDataRuntime.Value))
    (projected : eraseFields fields = some erasedFields) (name : Nat) (payload : PresenceDataTypes.Ty) :
    PresenceDataTypes.optional name payload (.record erasedFields) ↔
      Ty.optional name (pullback payload) (.record fields) := by
  constructor
  · intro optional value present
    have corresponding := projected_lookup fields erasedFields projected name
    rw [present] at corresponding
    obtain ⟨erased, successful, found⟩ := corresponding
    exact ⟨erased, successful, optional.2 erased found⟩
  · intro optional
    refine ⟨trivial, ?_⟩
    intro erased present
    have corresponding := projected_lookup fields erasedFields projected name
    cases found : lookup name fields with
    | none =>
        rw [found] at corresponding
        have impossible := present.symm.trans corresponding
        cases impossible
    | some value =>
        rw [found] at corresponding
        obtain ⟨actual, successful, markerFound⟩ := corresponding
        obtain ⟨other, otherSuccess, valid⟩ := optional value found
        have same : other = actual := Option.some.inj (otherSuccess.symm.trans successful)
        have sameMarker : actual = erased := Option.some.inj (markerFound.symm.trans present)
        simpa [same, sameMarker] using valid

theorem required_projected_iff (fields : Bindings F)
    (erasedFields : List (Nat × SourceDataRuntime.Value))
    (projected : eraseFields fields = some erasedFields) (name : Nat) (payload : PresenceDataTypes.Ty) :
    PresenceDataTypes.required name payload (.record erasedFields) ↔
      Ty.required name (pullback payload) (.record fields) := by
  constructor
  · rintro ⟨_, erased, present, valid⟩
    have corresponding := projected_lookup fields erasedFields projected name
    cases found : lookup name fields with
    | none =>
        rw [found] at corresponding
        have impossible := present.symm.trans corresponding
        cases impossible
    | some value =>
        rw [found] at corresponding
        obtain ⟨actual, successful, markerFound⟩ := corresponding
        have same : actual = erased := Option.some.inj (markerFound.symm.trans present)
        exact ⟨value, found, actual, successful, by simpa [same] using valid⟩
  · rintro ⟨value, present, erased, successful, valid⟩
    have corresponding := projected_lookup fields erasedFields projected name
    rw [present] at corresponding
    obtain ⟨actual, actualSuccess, markerFound⟩ := corresponding
    have same : actual = erased := Option.some.inj (actualSuccess.symm.trans successful)
    exact ⟨trivial, erased, by simpa [same, PresenceDataTypes.lookup] using markerFound, valid⟩

/-- Pulling an optional marker type back to concrete values yields the same
optional lookup demand on each present concrete payload. -/
theorem pullback_optional {F : Type} (name : Nat) (payload : PresenceDataTypes.Ty) :
    Ty.Le (F := F) (pullback (PresenceDataTypes.optional name payload))
      (Ty.optional name (pullback payload)) := by
  rintro value ⟨erased, projected, optional⟩
  cases erased with
  | record erasedFields =>
      obtain ⟨fields, rfl, projectFields⟩ := (erase_record_iff value erasedFields).mp projected
      exact (optional_projected_iff fields erasedFields projectFields name payload).mp optional
  | base | pair | variant => cases optional.1

/-- `none` records missing elaboration metadata; it is not a chosen source
rejection or acceptance for an unknown field. -/
def resolvedFieldType (presence : Presence) (name : Nat) (payload : PresenceDataTypes.Ty) :
    Option PresenceDataTypes.Ty :=
  match presence with
  | .required => some (PresenceDataTypes.required name payload)
  | .optional => some (PresenceDataTypes.optional name payload)
  | .unknown => none

/-- A concrete pattern receives the union of the optional marker payload
and the fallback result. Required metadata cannot inhabit these premises. -/
theorem validated_binding_typing {F D : Type} (DefaultTyped : D → Ty F → Prop)
    (presence : Presence) (name binder : Nat) (payload input : PresenceDataTypes.Ty)
    (resolved : resolvedFieldType presence name payload = some input)
    (accepted : validateDefault presence = .allowed) (fallback : D) (fallbackType : Ty F)
    (fallbackTyped : DefaultTyped fallback fallbackType) :
    CasePatterns.Typing DefaultTyped
      (.defaultField name fallback (.bind binder) .recordEnd)
      (pullback input) [(binder, Ty.union (pullback payload) fallbackType)] := by
  have permitted := (validateDefault_exact presence).mp accepted
  cases permitted
  have same : PresenceDataTypes.optional name payload = input := Option.some.inj resolved
  subst input
  have recordInput : Ty.Le (F := F) (pullback (PresenceDataTypes.optional name payload)) Ty.records :=
    fun value valid => Ty.optional_records name (pullback payload) value
      (pullback_optional name payload value valid)
  exact .defaultField (pullback_optional name payload) fallbackTyped .bind
    (.narrow recordInput .recordEnd)

/-- A present concrete field is bound verbatim and produces no fallback
observation. No marker-to-value reconstruction is used. -/
theorem binding_present (floatCheck : F → F → Bool)
    (defaultEval : D → Logged E R (Value F)) (name binder : Nat) (fallback : D)
    (fields : Bindings F) (value : Value F) (present : lookup name fields = some value) :
    CasePatterns.run floatCheck defaultEval
      (.defaultField name fallback (.bind binder) .recordEnd) (.record fields) =
        CasePatterns.success [(binder, value)] := by
  rw [CasePatterns.default_present _ _ _ _ _ _ _ _ present]
  simp [CasePatterns.run, CasePatterns.andThen, CasePatterns.success, Logged.ofResult, Logged.bind]

/-- For an absent field the exact fallback observation is retained, and only
its resulting value is repackaged as the binding. -/
theorem binding_absent (floatCheck : F → F → Bool)
    (defaultEval : D → Logged E R (Value F)) (name binder : Nat) (fallback : D)
    (fields : Bindings F) (absent : lookup name fields = none) :
    CasePatterns.run floatCheck defaultEval
      (.defaultField name fallback (.bind binder) .recordEnd) (.record fields) =
        (defaultEval fallback).bind (fun value => CasePatterns.success [(binder, value)]) := by
  rw [CasePatterns.default_absent _ _ _ _ _ _ _ absent]
  simp [CasePatterns.run, CasePatterns.andThen, CasePatterns.success, Logged.ofResult, Logged.bind]

/-- For every implementation of the fallback satisfying its ordinary typing
contract, a validated default binder matches every projected input value and
binds a concrete payload in the promised union. Evaluation is not a premise. -/
theorem validated_binding_evaluates {F D E R : Type}
    (floatCheck : F → F → Bool) (DefaultTyped : D → Ty F → Prop)
    (defaultEval : D → Logged E R (Value F))
    (defaultSound : CasePatterns.DefaultSound DefaultTyped defaultEval)
    (presence : Presence) (name binder : Nat) (payload input : PresenceDataTypes.Ty)
    (resolved : resolvedFieldType presence name payload = some input)
    (accepted : validateDefault presence = .allowed) (fallback : D) (fallbackType : Ty F)
    (fallbackTyped : DefaultTyped fallback fallbackType)
    (value : Value F) (erased : SourceDataRuntime.Value)
    (projected : erase value = some erased) (valid : input erased) :
    ∃ selected, (CasePatterns.run floatCheck defaultEval
        (.defaultField name fallback (.bind binder) .recordEnd) value).result =
          .ok (some [(binder, selected)]) ∧
        Ty.union (pullback payload) fallbackType selected := by
  have permitted := (validateDefault_exact presence).mp accepted
  cases permitted
  have same : PresenceDataTypes.optional name payload = input := Option.some.inj resolved
  subst input
  have sourceOptional : Ty.optional name (pullback payload) value :=
    pullback_optional name payload value ⟨erased, projected, valid⟩
  cases value with
  | record fields =>
      cases found : lookup name fields with
      | some selected =>
          refine ⟨selected, ?_, Or.inl (sourceOptional selected found)⟩
          rw [binding_present floatCheck defaultEval name binder fallback fields selected found]
          rfl
      | none =>
          obtain ⟨selected, evaluated, selectedValid⟩ := defaultSound fallback fallbackType fallbackTyped
          refine ⟨selected, ?_, Or.inr selectedValid⟩
          rw [binding_absent floatCheck defaultEval name binder fallback fields found,
            Logged.bind_result, evaluated]
          rfl
  | literal | pair | variant | nominal | list => cases sourceOptional

end Yulang.CasePresenceValidation
