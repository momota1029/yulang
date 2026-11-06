import Yulang.PresenceDataShapes

/-!
# Principal inference for presence-aware first-order source data

The input is the actual `Inference.Expr`, including `recordDefault`.
`Typing` is an independent constructor/subsumption judgment over semantic data
types. The algorithm computes finite exact `Shape` descriptors, using only
source recursion and type-level field operations; it does not call `eval`.

The supported language comprises variables, literals, evaluated lets, pairs,
projections, records, spread-first defaults, field access, and variants.
Functions, applications, branches and effects are outside this entry. This
module neither changes legacy typing nor claims full-core principal inference.
-/

namespace Yulang.PresenceDataInference

open Inference (Expr Base)
open SourceDataRuntime (Value)
open PresenceDataTypes
open PresenceDataShapes (Shape ShapeFields)

/-- Every rule is stated without mentioning the inference algorithm or the
runtime evaluator. In particular both operands of `recordDefault` are typed. -/
inductive Typing : List Ty → Expr → Ty → Prop where
  | var : context[index]? = some type → Typing context (.var index) type
  | lit (name : Base) : Typing context (.lit name) (base name)
  | emptyRecord : Typing context .emptyRecord exactEmpty
  | letE : Typing context value valueType → Typing (valueType :: context) body resultType →
      Typing context (.letE value body) resultType
  | pair : Typing context left leftType → Typing context right rightType →
      Typing context (.pair left right) (pair leftType rightType)
  | fst : Typing context expression (pair left right) → Typing context (.fst expression) left
  | snd : Typing context expression (pair left right) → Typing context (.snd expression) right
  | record : Typing context head headType → Typing context tail tailType → Le tailType records →
      Typing context (.record label head tail) (record label headType tailType)
  | recordDefault : Typing context source sourceType → Typing context fallback fallbackType →
      Le sourceType records →
      Typing context (.recordDefault label source fallback)
        (recordDefault label sourceType fallbackType)
  | field : Typing context expression (required label payload) →
      Typing context (.field label expression) payload
  | variant : Typing context expression payload →
      Typing context (.variant label expression) (variant label payload)
  | subsume : Typing context expression source → Le source target →
      Typing context expression target

/-- Syntax support is separate from typability, including malformed data
operations such as reading a missing field or spreading a scalar. -/
def supported : Expr → Bool
  | .var _ | .lit _ | .emptyRecord => true
  | .letE left right | .pair left right | .record _ left right | .recordDefault _ left right =>
      supported left && supported right
  | .fst expression | .snd expression | .field _ expression | .variant _ expression =>
      supported expression
  | _ => false

def Data (expression : Expr) : Prop := supported expression = true

/-- Structural type synthesis. `ShapeFields` are type descriptors, not
runtime fields. Both default operands are synthesized before field selection. -/
def synth (environment : List Shape) : Expr → Option Shape
  | .var index => environment[index]?
  | .lit name => some (.base name)
  | .emptyRecord => some (.record .nil)
  | .letE value body => do
      let initial ← synth environment value
      synth (initial :: environment) body
  | .pair left right => do
      let first ← synth environment left
      let last ← synth environment right
      pure (.pair first last)
  | .fst expression => do
      let shape ← synth environment expression
      match shape with
      | .pair first _ => some first
      | _ => none
  | .snd expression => do
      let shape ← synth environment expression
      match shape with
      | .pair _ last => some last
      | _ => none
  | .record label head tail => do
      let first ← synth environment head
      let last ← synth environment tail
      match last with
      | .record fields => some (.record (fields.insert label first))
      | _ => none
  | .recordDefault label source fallback => do
      let first ← synth environment source
      let last ← synth environment fallback
      match first with
      | .record fields => some (.record (fields.insertDefault label last))
      | _ => none
  | .field label expression => do
      let shape ← synth environment expression
      match shape with
      | .record fields => fields.lookup label
      | _ => none
  | .variant label expression => do
      let payload ← synth environment expression
      pure (.variant label payload)
  | _ => none

inductive Result where
  | solved : Shape → Result
  | rejected : Result
  | unsupported : Result
  deriving Repr

/-- A total entry on the original source AST, with separate unsupported and
ill-typed outcomes. It requires no type assignment, solver witness or fuel. -/
def infer (expression : Expr) : Result :=
  if supported expression then
    match synth [] expression with
    | some shape => .solved shape
    | none => .rejected
  else .unsupported

def exactContext (environment : List Shape) : List Ty := environment.map Shape.denote

/-- An arbitrary declared environment may describe any of these exact
values; no equality between its types and the inferred shapes is assumed. -/
def EnvHolds (context : List Ty) (environment : List Shape) : Prop :=
  ∀ (index : Nat) (type : Ty), context[index]? = some type →
    ∃ shape, environment[index]? = some shape ∧ type shape.value

theorem EnvHolds.nil : EnvHolds [] [] := by
  intro index type found
  simp at found

theorem EnvHolds.cons {context : List Ty} {environment : List Shape}
    {type : Ty} {shape : Shape} (valid : type shape.value) (rest : EnvHolds context environment) :
    EnvHolds (type :: context) (shape :: environment) := by
  intro index target found
  cases index with
  | zero =>
      have same : type = target := by simpa using found
      subst target
      exact ⟨shape, rfl, valid⟩
  | succ index =>
      exact rest index target found

theorem exactContext_holds (environment : List Shape) : EnvHolds (exactContext environment) environment := by
  intro index type found
  simp only [exactContext, List.getElem?_map, Option.map_eq_some_iff] at found
  obtain ⟨shape, present, rfl⟩ := found
  exact ⟨shape, present, rfl⟩

theorem Typing.supported {context : List Ty} {expression : Expr} {type : Ty}
    (typed : Typing context expression type) : Data expression := by
  induction typed <;> simp_all [Data, PresenceDataInference.supported]

/-- Completeness derives successful synthesis from the independent typing
judgment, retaining the semantic bound for every target type. -/
theorem Typing.synth_complete {context : List Ty} {expression : Expr} {type : Ty}
    (typed : Typing context expression type) (environment : List Shape)
    (valid : EnvHolds context environment) :
    ∃ shape, synth environment expression = some shape ∧ type shape.value := by
  induction typed generalizing environment with
  | var found =>
      obtain ⟨shape, present, valid⟩ := valid _ _ found
      exact ⟨shape, present, valid⟩
  | lit name => exact ⟨.base name, rfl, rfl⟩
  | emptyRecord => exact ⟨.record .nil, rfl, rfl⟩
  | letE _ _ first last =>
      obtain ⟨initial, firstFound, initialValid⟩ := first environment valid
      obtain ⟨result, lastFound, resultValid⟩ := last (initial :: environment) (EnvHolds.cons initialValid valid)
      exact ⟨result, by simp [synth, firstFound, lastFound], resultValid⟩
  | pair _ _ first last =>
      obtain ⟨left, leftFound, leftValid⟩ := first environment valid
      obtain ⟨right, rightFound, rightValid⟩ := last environment valid
      exact ⟨.pair left right, by simp [synth, leftFound, rightFound], leftValid, rightValid⟩
  | fst _ child =>
      obtain ⟨shape, found, shapeValid⟩ := child environment valid
      cases shape with
      | pair left right => exact ⟨left, by simp [synth, found], shapeValid.1⟩
      | base | record | variant => cases shapeValid
  | snd _ child =>
      obtain ⟨shape, found, shapeValid⟩ := child environment valid
      cases shape with
      | pair left right => exact ⟨right, by simp [synth, found], shapeValid.2⟩
      | base | record | variant => cases shapeValid
  | @record context headExpr headType tailExpr tailType label _ _ admissible head tail =>
      obtain ⟨first, firstFound, firstValid⟩ := head environment valid
      obtain ⟨last, lastFound, lastValid⟩ := tail environment valid
      have recordShape := admissible _ lastValid
      cases last with
      | record fields =>
          refine ⟨.record (fields.insert label first), by simp [synth, firstFound, lastFound], ?_⟩
          exact ⟨first.value, fields.values, firstValid, lastValid, by simp [Shape.value]⟩
      | base | pair | variant => cases recordShape
  | @recordDefault context sourceExpr sourceType fallbackExpr fallbackType label _ _ admissible source fallback =>
      obtain ⟨first, firstFound, firstValid⟩ := source environment valid
      obtain ⟨last, lastFound, lastValid⟩ := fallback environment valid
      have recordShape := admissible _ firstValid
      cases first with
      | record fields =>
          refine ⟨.record (fields.insertDefault label last), by simp [synth, firstFound, lastFound], ?_⟩
          exact ⟨fields.values, last.value, firstValid, lastValid, by simp [Shape.value]⟩
      | base | pair | variant => cases recordShape
  | @field context expression label payload _ child =>
      obtain ⟨shape, found, shapeValid⟩ := child environment valid
      cases shape with
      | record fields =>
          obtain ⟨_, item, itemFound, itemValid⟩ := shapeValid
          change SourceDataRuntime.Fields.lookup label fields.values = some item at itemFound
          rw [ShapeFields.lookup_values, Option.map_eq_some_iff] at itemFound
          obtain ⟨result, resultFound, same⟩ := itemFound
          exact ⟨result, by simp [synth, found, resultFound], by simpa [same] using itemValid⟩
      | base | pair | variant => cases shapeValid.1
  | variant _ child =>
      obtain ⟨shape, found, shapeValid⟩ := child environment valid
      exact ⟨.variant _ shape, by simp [synth, found], rfl, shapeValid⟩
  | subsume _ below child =>
      obtain ⟨shape, found, shapeValid⟩ := child environment valid
      exact ⟨shape, found, below _ shapeValid⟩

/-! ## Exact descriptor derivations and algorithm soundness -/

theorem Typing.exact_pair {context : List Ty} {left right : Expr} {first last : Shape}
    (before : Typing context left first.denote) (after : Typing context right last.denote) :
    Typing context (.pair left right) (Shape.pair first last).denote :=
  .subsume (.pair before after) (PresenceDataTypes.pair_exact _ _)

theorem Typing.exact_fst {context : List Ty} {expression : Expr} {first last : Shape}
    (typed : Typing context expression (Shape.pair first last).denote) :
    Typing context (.fst expression) first.denote := by
  have viewed : Typing context expression (PresenceDataTypes.pair first.denote last.denote) :=
    .subsume typed (by rintro value rfl; exact ⟨rfl, rfl⟩)
  exact .fst viewed

theorem Typing.exact_snd {context : List Ty} {expression : Expr} {first last : Shape}
    (typed : Typing context expression (Shape.pair first last).denote) :
    Typing context (.snd expression) last.denote := by
  have viewed : Typing context expression (PresenceDataTypes.pair first.denote last.denote) :=
    .subsume typed (by rintro value rfl; exact ⟨rfl, rfl⟩)
  exact .snd viewed

theorem Typing.exact_record {context : List Ty} {head tail : Expr}
    (label : Nat) {first : Shape} {fields : ShapeFields}
    (before : Typing context head first.denote)
    (after : Typing context tail (Shape.record fields).denote) :
    Typing context (.record label head tail) (Shape.record (fields.insert label first)).denote := by
  have typed := Typing.record before after (exact_record_le_records fields.values) (label := label)
  have bounded := Typing.subsume typed (PresenceDataTypes.record_exact label first.value fields.values)
  simpa only [Shape.denote, Shape.value, ShapeFields.insert_values] using bounded

theorem Typing.exact_recordDefault {context : List Ty} {source fallback : Expr}
    (label : Nat) {fields : ShapeFields} {last : Shape}
    (before : Typing context source (Shape.record fields).denote)
    (after : Typing context fallback last.denote) :
    Typing context (.recordDefault label source fallback)
      (Shape.record (fields.insertDefault label last)).denote := by
  have typed := Typing.recordDefault before after (exact_record_le_records fields.values) (label := label)
  have bounded := Typing.subsume typed
    (PresenceDataTypes.recordDefault_exact label fields.values last.value)
  simpa only [Shape.denote, Shape.value, ShapeFields.insertDefault_values] using bounded

theorem Typing.exact_field {context : List Ty} {expression : Expr}
    (label : Nat) {fields : ShapeFields} {shape : Shape}
    (typed : Typing context expression (Shape.record fields).denote)
    (found : fields.lookup label = some shape) :
    Typing context (.field label expression) shape.denote :=
  .field (.subsume typed (fields.required_of_lookup label shape found))

theorem Typing.exact_variant {context : List Ty} {expression : Expr}
    (label : Nat) {shape : Shape} (typed : Typing context expression shape.denote) :
    Typing context (.variant label expression) (Shape.variant label shape).denote :=
  .subsume (.variant typed) (PresenceDataTypes.variant_exact label shape.value)

/-- A successful structural computation produces a derivation in the
independent typing system, with no residual type or graph constraints. -/
theorem synth_sound (environment : List Shape) (expression : Expr) (shape : Shape)
    (found : synth environment expression = some shape) :
    Typing (exactContext environment) expression shape.denote := by
  induction expression generalizing environment shape with
  | var index =>
      apply Typing.var
      simp only [synth] at found
      simp [exactContext, List.getElem?_map, found]
  | lit name =>
      have same : Shape.base name = shape := Option.some.inj found
      subst shape
      exact .lit name
  | emptyRecord =>
      have same : Shape.record .nil = shape := Option.some.inj found
      subst shape
      exact .emptyRecord
  | letE value body first last =>
      simp only [synth, Option.bind_eq_bind, Option.bind_eq_some_iff] at found
      obtain ⟨initial, firstFound, lastFound⟩ := found
      exact .letE (first environment initial firstFound) (last (initial :: environment) shape lastFound)
  | pair left right first last =>
      simp only [synth, Option.bind_eq_bind, Option.bind_eq_some_iff] at found
      obtain ⟨initial, firstFound, final, lastFound, returned⟩ := found
      cases Option.some.inj returned
      exact .exact_pair (first environment initial firstFound) (last environment final lastFound)
  | fst expression child =>
      simp only [synth, Option.bind_eq_bind, Option.bind_eq_some_iff] at found
      obtain ⟨parent, parentFound, selected⟩ := found
      cases parent with
      | pair first last =>
          have same : first = shape := Option.some.inj selected
          subst shape
          exact .exact_fst (child environment (.pair first last) parentFound)
      | base | record | variant => cases selected
  | snd expression child =>
      simp only [synth, Option.bind_eq_bind, Option.bind_eq_some_iff] at found
      obtain ⟨parent, parentFound, selected⟩ := found
      cases parent with
      | pair first last =>
          have same : last = shape := Option.some.inj selected
          subst shape
          exact .exact_snd (child environment (.pair first last) parentFound)
      | base | record | variant => cases selected
  | record label head tail first last =>
      simp only [synth, Option.bind_eq_bind, Option.bind_eq_some_iff] at found
      obtain ⟨initial, firstFound, final, lastFound, selected⟩ := found
      cases final with
      | record fields =>
          have same : Shape.record (fields.insert label initial) = shape := Option.some.inj selected
          subst shape
          exact .exact_record label (first environment initial firstFound)
            (last environment (.record fields) lastFound)
      | base | pair | variant => cases selected
  | recordDefault label source fallback first last =>
      simp only [synth, Option.bind_eq_bind, Option.bind_eq_some_iff] at found
      obtain ⟨initial, firstFound, final, lastFound, selected⟩ := found
      cases initial with
      | record fields =>
          have same : Shape.record (fields.insertDefault label final) = shape := Option.some.inj selected
          subst shape
          exact .exact_recordDefault label (first environment (.record fields) firstFound)
            (last environment final lastFound)
      | base | pair | variant => cases selected
  | field label expression child =>
      simp only [synth, Option.bind_eq_bind, Option.bind_eq_some_iff] at found
      obtain ⟨parent, parentFound, selected⟩ := found
      cases parent with
      | record fields => exact .exact_field label (child environment (.record fields) parentFound) selected
      | base | pair | variant => cases selected
  | variant label expression child =>
      simp only [synth, Option.bind_eq_bind, Option.bind_eq_some_iff] at found
      obtain ⟨payload, payloadFound, returned⟩ := found
      cases Option.some.inj returned
      exact .exact_variant label (child environment payload payloadFound)
  | lam | app | branch => cases found

/-- Principal types hold for every target predicate in this data model, not
only for the constructor shape selected by the algorithm. -/
theorem synth_instances_exact (environment : List Shape) (expression : Expr) (target : Ty) :
    Typing (exactContext environment) expression target ↔
      ∃ shape, synth environment expression = some shape ∧ Le shape.denote target := by
  constructor
  · intro typed
    obtain ⟨shape, found, valid⟩ := typed.synth_complete environment (exactContext_holds environment)
    exact ⟨shape, found, (shape.denote_le_iff target).mpr valid⟩
  · rintro ⟨shape, found, below⟩
    exact .subsume (synth_sound environment expression shape found) below

theorem infer_solved_iff (expression : Expr) (shape : Shape) :
    infer expression = .solved shape ↔ synth [] expression = some shape := by
  constructor
  · intro result
    unfold infer at result
    split at result
    · split at result
      · rename_i found
        cases result
        exact found
      · cases result
    · cases result
  · intro found
    have data : supported expression = true := (synth_sound [] expression shape found).supported
    simp [infer, data, found]

theorem infer_unsupported_iff (expression : Expr) :
    infer expression = .unsupported ↔ ¬ Data expression := by
  unfold infer Data
  cases supported expression <;> simp
  cases synth [] expression <;> simp

/-- The exact all-instance contract has no caller-supplied success premise. -/
theorem infer_instances_exact (expression : Expr) (target : Ty) :
    Typing [] expression target ↔
      ∃ shape, infer expression = .solved shape ∧ Le shape.denote target := by
  simpa only [exactContext, List.map_nil, infer_solved_iff] using
    synth_instances_exact [] expression target

theorem infer_success_iff (expression : Expr) :
    (∃ shape, infer expression = .solved shape) ↔ ∃ target, Typing [] expression target := by
  constructor
  · rintro ⟨shape, found⟩
    exact ⟨shape.denote, (infer_instances_exact expression shape.denote).mpr
      ⟨shape, found, le_refl _⟩⟩
  · rintro ⟨target, typed⟩
    obtain ⟨shape, found, _⟩ := (infer_instances_exact expression target).mp typed
    exact ⟨shape, found⟩

/-- Rejection is exact on supported data syntax. Unsupported syntax remains
a separate outcome, including otherwise valid function terms. -/
theorem infer_rejected_iff (expression : Expr) :
    infer expression = .rejected ↔ Data expression ∧ ¬ ∃ target, Typing [] expression target := by
  constructor
  · intro rejected
    have data : Data expression := by
      unfold infer at rejected
      split at rejected
      · assumption
      · cases rejected
    refine ⟨data, ?_⟩
    intro typed
    obtain ⟨shape, solved⟩ := (infer_success_iff expression).mpr typed
    rw [rejected] at solved
    cases solved
  · rintro ⟨data, untyped⟩
    cases result : infer expression with
    | rejected => rfl
    | solved shape => exact False.elim (untyped ((infer_success_iff expression).mp ⟨shape, result⟩))
    | unsupported => exact False.elim (((infer_unsupported_iff expression).mp result) data)

/-! ## Unknown, present and absent field contracts -/

theorem Typing.default_optional {context : List Ty} {source fallback : Expr}
    (label : Nat) {sourceType payload fallbackType : Ty}
    (before : Typing context source sourceType) (after : Typing context fallback fallbackType)
    (bounded : Le sourceType (optional label payload)) :
    Typing context (.recordDefault label source fallback) (required label (union payload fallbackType)) :=
  .subsume (.recordDefault before after (le_trans bounded (optional_records label payload)))
    (PresenceDataTypes.recordDefault_optional label sourceType payload fallbackType bounded)

theorem Typing.default_present {context : List Ty} {source fallback : Expr}
    (label : Nat) {sourceType payload fallbackType : Ty}
    (before : Typing context source sourceType) (after : Typing context fallback fallbackType)
    (bounded : Le sourceType (required label payload)) :
    Typing context (.recordDefault label source fallback) (required label payload) :=
  .subsume (.recordDefault before after (fun value valid => (bounded value valid).1))
    (PresenceDataTypes.recordDefault_present label sourceType fallbackType payload bounded)

theorem Typing.default_absent {context : List Ty} {source fallback : Expr}
    (label : Nat) {sourceType fallbackType : Ty}
    (before : Typing context source sourceType) (after : Typing context fallback fallbackType)
    (bounded : Le sourceType (lacks label)) :
    Typing context (.recordDefault label source fallback) (required label fallbackType) :=
  .subsume (.recordDefault before after (fun value valid => (bounded value valid).1))
    (PresenceDataTypes.recordDefault_absent label sourceType fallbackType bounded)

/-- Static knowledge of presence keeps the complete original record shape. -/
theorem synth_default_present (environment : List Shape) (label : Nat)
    (source fallback : Expr) (fields : ShapeFields) (existing last : Shape)
    (before : synth environment source = some (.record fields))
    (after : synth environment fallback = some last)
    (present : fields.lookup label = some existing) :
    synth environment (.recordDefault label source fallback) = some (.record fields) := by
  simp [synth, before, after, ShapeFields.insertDefault, present]

theorem synth_default_absent (environment : List Shape) (label : Nat)
    (source fallback : Expr) (fields : ShapeFields) (last : Shape)
    (before : synth environment source = some (.record fields))
    (after : synth environment fallback = some last)
    (absent : fields.lookup label = none) :
    synth environment (.recordDefault label source fallback) =
      some (.record (fields.append (.cons label last .nil))) := by
  simp [synth, before, after, ShapeFields.insertDefault, absent]

end Yulang.PresenceDataInference
