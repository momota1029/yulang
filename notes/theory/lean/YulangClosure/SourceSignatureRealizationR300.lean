import YulangClosure.AuthenticSourceGraphR299
import YulangClosure.OriginalUnionOwnerR292

/-!
R300: complete HIR annotation retention and source-directed field readback.

The carrier is the existing PrimitiveOperation.Annotation, with concrete row
payloads matching source_annotation.rs:135--163. It retains arbitrary recursive
Function/tuple/variable/hole syntax, complete row positions, ordered concrete
identities and symbolic row variables. No semantic interface is replaced by
this syntax. The constructors below model source field access and the pure
branch policy of candidate_signature_effect; they do NOT establish an actual
Rust execution, allocation/cache invariant, original primitive license or IF
whole-map action. Operation preflight excludes holes and tuples, although the
HIR and annotation path include both. See the frozen assignment handoff.
-/
namespace YulangClosure.SourceSignatureRealizationR300

open PrimitiveOperation

/-- Exact SourceEffectRow fields; Key and Position stand for complete native
identities, not spelling, hashes or source-range approximations. -/
structure EffectRow (Key Position : Type) where
  position : Position
  concrete : List Key
  variables : List String

abbrev Signature (Key Position : Type) := Annotation (EffectRow Key Position) Position

def effects {E H : Type} : Annotation E H → Option E
  | .primitive row _ | .variable row _ | .hole row _
  | .function row _ _ | .tuple row _ => row

/-- Exactly FormalPortStep's three source child constructors. -/
inductive Step where
  | argument | result | element (index : Nat)
  deriving DecidableEq, Repr

def child {E H : Type} : Annotation E H → Step → Option (Annotation E H)
  | .function _ argument _, .argument => some argument
  | .function _ _ result, .result => some result
  | .tuple _ elements, .element i => elements[i]?
  | _, _ => none

/-- Complete subtree readback, not a base/Function-shape decoder. -/
def lookup {E H : Type} (root : Annotation E H) : List Step → Option (Annotation E H)
  | [] => some root
  | step :: rest => (child root step).bind (fun next => lookup next rest)

/-- A typed field action contains the genuine constructor edge. Tuple fields
retain their ordered index; two occurrences of the same subtree stay distinct. -/
inductive Field {E H : Type} : Annotation E H → List Step → Annotation E H → Type where
  | root (a) : Field a [] a
  | argument {row argument result path leaf} (inner : Field argument path leaf) :
      Field (.function row argument result) (.argument :: path) leaf
  | result {row argument result path leaf} (inner : Field result path leaf) :
      Field (.function row argument result) (.result :: path) leaf
  | element {row elements i next path leaf} (found : elements[i]? = some next)
      (inner : Field next path leaf) : Field (.tuple row elements) (.element i :: path) leaf

theorem field_readback {E H : Type} {a b : Annotation E H} {path : List Step}
    (field : Field a path b) : lookup a path = some b := by
  induction field with
  | root => rfl
  | argument inner ih => exact ih
  | result inner ih => exact ih
  | element found inner ih => simp only [lookup, child, found, Option.bind_some]; exact ih

/-- Both directions for every recursive source constructor. No success or
semantic typing hypothesis is hidden in the reverse construction. -/
theorem lookup_iff_field {E H : Type} (a b : Annotation E H) (path : List Step) :
    lookup a path = some b ↔ Nonempty (Field a path b) := by
  constructor
  · intro found
    induction path generalizing a with
    | nil => cases Option.some.inj found; exact ⟨.root _⟩
    | cons step rest ih =>
        cases a with
        | primitive row base => cases step <;> simp [lookup, child] at found
        | «variable» row name => cases step <;> simp [lookup, child] at found
        | hole row position => cases step <;> simp [lookup, child] at found
        | function row argument result =>
            cases step with
            | argument => obtain ⟨inner⟩ := ih argument found; exact ⟨.argument inner⟩
            | result => obtain ⟨inner⟩ := ih result found; exact ⟨.result inner⟩
            | element i => simp [lookup, child] at found
        | tuple row elements =>
            cases step with
            | argument => simp [lookup, child] at found
            | result => simp [lookup, child] at found
            | element i =>
                cases h : elements[i]? with
                | none => simp [lookup, child, h] at found
                | some next =>
                    obtain ⟨inner⟩ := ih next (by simpa [lookup, child, h] using found)
                    exact ⟨.element h inner⟩
  · rintro ⟨field⟩; exact field_readback field

theorem field_unique {E H : Type} {a b c : Annotation E H} {path : List Step}
    (first : Field a path b) (second : Field a path c) : b = c :=
  Option.some.inj ((field_readback first).symm.trans (field_readback second))

/-- Source child actions compose at the exact intermediate subtree. -/
def Field.append {E H : Type} {a b c : Annotation E H} {p q : List Step}
    (outer : Field a p b) (inner : Field b q c) : Field a (p ++ q) c :=
  match outer with
  | .root _ => inner
  | .argument outer => .argument (outer.append inner)
  | .result outer => .result (outer.append inner)
  | .element found outer => .element found (outer.append inner)

/-- Rust independently carries polarity and variance. Both reverse only at
Function arguments; tuple elements and Function results preserve each one. -/
def polarityAt (positive : Bool) : List Step → Bool
  | [] => positive
  | .argument :: path => polarityAt (!positive) path
  | .result :: path | .element _ :: path => polarityAt positive path

theorem polarityAt_composition (positive : Bool) (p q : List Step) :
    polarityAt positive (p ++ q) = polarityAt (polarityAt positive p) q := by
  induction p generalizing positive with
  | nil => rfl
  | cons step p ih => cases step <;> simp only [List.cons_append, polarityAt] <;> apply ih

/-- A readback retains the actual subtree and its COMPLETE optional row. -/
def fieldRead {E H : Type} (a : Annotation E H) (p v : Bool) (path : List Step) :=
  (lookup a path).map (fun b => (b, effects b, polarityAt p path, polarityAt v path))

theorem fieldRead_exact {E H : Type} {a b : Annotation E H} {path : List Step}
    (field : Field a path b) (p v : Bool) :
    fieldRead a p v path = some (b, effects b, polarityAt p path, polarityAt v path) := by
  simp only [fieldRead, field_readback field, Option.map_some]

/-- The callable-result case excluded by the old ground decoder now has an
unconditional full readback, with arbitrary nested effects, variables/tuples
and both independent signs. It is not an OperationInstance typing theorem. -/
theorem callable_result_retained {E H : Type} (row nestedRow : Option E)
    (argument parameter result : Annotation E H) (p v : Bool) :
    fieldRead (.function row argument (.function nestedRow parameter result)) p v [.result] =
      some (.function nestedRow parameter result, nestedRow, p, v) := rfl

theorem nested_argument_retained {E H : Type} (row nestedRow : Option E)
    (argument parameter result : Annotation E H) (p v : Bool) :
    fieldRead (.function row argument (.function nestedRow parameter result)) p v
      [.result, .argument] = some (parameter, effects parameter, !p, !v) := rfl

/-- Direct operation-signature value preflight at candidate_source.rs:989.
Annotation retention is deliberately wider than operation acceptance. -/
def operationValues {E H : Type} : Annotation E H → Bool
  | .hole .. | .tuple .. => false
  | .function _ argument result => operationValues argument && operationValues result
  | _ => true

theorem operation_callable_result {E H : Type} (row nestedRow : Option E)
    (argument parameter result : Annotation E H) :
    operationValues (.function row argument (.function nestedRow parameter result)) =
      (operationValues argument && (operationValues parameter && operationValues result)) := rfl

/-- Identity of the outer operation signature is supplied by its owning call,
not inferred from structural equality. Descending clears the Self marker. -/
def selfFamily {Key : Type} (family : Key) (path : List Step) : Option Key :=
  if path.isEmpty then some family else none

theorem self_only_outer {Key : Type} (family : Key) (step : Step) (path : List Step) :
    selfFamily family (step :: path) = none := rfl

/-- Pure branch policy BEFORE mutable view-cache lookup and fresh allocation.
`view` preserves the whole row provenance, ordered members and symbolic tail.
These are construction instructions, NOT semantic permissions or native terms. -/
inductive EffectPlan (Key Position : Type) where
  | empty (positive : Bool)
  | tail (positive : Bool) (name : String)
  | view (support : Bool) (position : Position) (allowed : List Key) (tail : Option String)

/-- Operation context only. Primitive positive Functions have an extra shared
entry-row override; annotations have lexical scopes and omitted-row policy.
Neither is silently identified with this operation policy. -/
def operationEffectPlan {Key Position : Type} (position : Position)
    (row : Option (EffectRow Key Position)) (family : Option Key)
    (positive variance : Bool) : Option (EffectPlan Key Position) :=
  match row with
  | none => match family with
    | some key => some (.view true position [key] none)
    | none => some (.empty positive)
  | some row =>
    if (!variance && !row.concrete.isEmpty) || row.variables.length > 1 then none
    else if !variance then
      some (match row.variables.head? with
        | some name => .tail positive name
        | none => .empty positive)
    else some (.view positive row.position (family.toList ++ row.concrete) row.variables.head?)

theorem operation_omitted_self {Key Position : Type} (position : Position) (family : Key)
    (positive variance : Bool) :
    operationEffectPlan position none (some family) positive variance =
      some (.view true position [family] none) := rfl

theorem operation_written_positive {Key Position : Type} (position rowPosition : Position)
    (members : List Key) (variables : List String) (family : Option Key) (positive : Bool)
    (bounded : variables.length ≤ 1) :
    operationEffectPlan position (some ⟨rowPosition, members, variables⟩) family positive true =
      some (.view positive rowPosition (family.toList ++ members) variables.head?) := by
  simp [operationEffectPlan, Nat.not_lt.mpr bounded]

theorem operation_written_negative_concrete {Key Position : Type}
    (position rowPosition : Position) (head : Key) (members : List Key)
    (variables : List String) (family : Option Key) (positive : Bool) :
    operationEffectPlan position (some ⟨rowPosition, head :: members, variables⟩)
      family positive false = none := by simp [operationEffectPlan]

theorem operation_written_negative_tail {Key Position : Type}
    (position rowPosition : Position) (name : String) (family : Option Key) (positive : Bool) :
    operationEffectPlan position (some ⟨rowPosition, [], [name]⟩) family positive false =
      some (.tail positive name) := by simp [operationEffectPlan]

/-- Source value preflight propagates down every genuine retained field.
In particular no operation tuple/hole is reclassified as supported merely
because the complete HIR representation retains it. -/
theorem operationValues_field {E H : Type} {a b : Annotation E H} {path : List Step}
    (field : Field a path b) (accepted : operationValues a = true) :
    operationValues b = true := by
  induction field with
  | root => exact accepted
  | argument inner ih => exact ih (Bool.and_eq_true_iff.mp accepted).1
  | result inner ih => exact ih (Bool.and_eq_true_iff.mp accepted).2
  | element found inner ih => cases accepted

/-- A concrete successful erasure occurs already before mutable allocation:
omission and an explicitly empty negative row have the same operation plan.
The original row and position must therefore be retained separately. -/
theorem omitted_and_empty_same_plan {Key Position : Type}
    (position rowPosition : Position) (positive : Bool) :
    operationEffectPlan (Key := Key) position none none positive false =
      operationEffectPlan position (some ⟨rowPosition, [], []⟩) none positive false := by
  simp [operationEffectPlan]

/-- This failure is on TWO SUCCESSFUL branches, not on rejected signatures.
It refutes exact row reconstruction from this pure plan, not semantic IF. -/
theorem no_exact_row_recovery_from_plan {Key Position : Type}
    (position rowPosition : Position) (positive : Bool) :
    ¬ ∃ recover : EffectPlan Key Position → Option (EffectRow Key Position),
      ∀ row plan, operationEffectPlan position row none positive false = some plan →
        recover plan = row := by
  rintro ⟨recover, correct⟩
  have omitted := correct none (.empty positive) rfl
  have empty := correct (some ⟨rowPosition, [], []⟩) (.empty positive)
    (by simp [operationEffectPlan])
  have impossible := omitted.symm.trans empty
  cases impossible

/-- The actual next Union consumer is the original computation comparison,
not value Union. Full retained source syntax does not change this endpoint. -/
theorem actual_union_consumer (context : OriginalSource.Context) (mark : OriginalSource.Mark)
    (callee argument : OriginalSource.Source .expression) :
    OriginalSource.Premise.checking ⟨.computation, mark.site, context,
      ⟨mark.site, .callableImage⟩, ⟨mark.site, .synthesis⟩⟩ ∈
        SourceAppAdmissionR159.appPremises context mark callee argument :=
  OriginalUnionOwnerR292.app_computation_premise context mark callee argument

end YulangClosure.SourceSignatureRealizationR300
