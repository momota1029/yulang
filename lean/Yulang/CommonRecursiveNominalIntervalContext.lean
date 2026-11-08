import Yulang.CommonRecursiveNominalIntervalAdmission

/-!
# Inherited invariance in nested endpoint decomposition

Spec 6.5 (2026-11-08, dd6abf0b9) permits a used covariant position inside an
invariant argument to be held as an invariant interval too. The inherited
context is therefore part of an obligation. It is not recomputed solely from
the innermost declaration. Truly unused positions stay unused; their syntax
is checked separately by admission.

The old context-free reference functions and theorems remain unchanged.
These new functions implement the updated rule with no depth bound.
-/

namespace Yulang.CommonRecursiveNominalIntervals

open Core.PresenceGeneration (Comp)
open CommonDeclaredNominalInspection (Kind Parameter Declaration Registry)
open CommonDeclaredNominalVariance (Variance)
open PresenceNormalForm (Atom)

def effectiveVariance (inherited : Bool) : Variance → Variance
  | .unused => .unused
  | .invariant => .invariant
  | .covariant => if inherited then .invariant else .covariant
  | .contravariant => if inherited then .invariant else .contravariant

def effectiveParameter (inherited : Bool) (parameter : Parameter) : Parameter :=
  ⟨parameter.kind, effectiveVariance inherited parameter.variance⟩

def childContext (inherited : Bool) (parameter : Parameter) : Bool :=
  inherited || decide (parameter.variance = .invariant)

@[simp] theorem effective_false (parameter : Parameter) :
    effectiveParameter false parameter = parameter := by
  cases parameter with
  | mk kind mode => cases mode <;> rfl

@[simp] theorem effective_true_used (parameter : Parameter) (used : parameter.variance ≠ .unused) :
    effectiveParameter true parameter = ⟨parameter.kind, .invariant⟩ := by
  cases parameter with
  | mk kind mode => cases mode <;> simp_all [effectiveParameter, effectiveVariance]

abbrev ContextObligation (α : Type) := Bool × Obligation α

def decomposeContextArgument (inherited : Bool) (parameter : Parameter) (first last : Argument α) :
    Option (List (ContextObligation α)) :=
  (decomposeArgument (effectiveParameter inherited parameter) first last).map fun obligations =>
    obligations.map fun obligation => (childContext inherited parameter, obligation)

def decomposeContextArguments (inherited : Bool) :
    Declaration → List (Argument α) → List (Argument α) → Option (List (ContextObligation α))
  | [], [], [] => some []
  | parameter :: rest, first :: tail, last :: suffix =>
      append (decomposeContextArgument inherited parameter first last)
        (decomposeContextArguments inherited rest tail suffix)
  | _, _, _ => none

def ContextObligation.Holds (le : Bool → Endpoint α → Endpoint α → Prop)
    (assignment : α → Comp Common.model) (obligation : ContextObligation α) : Prop :=
  obligation.2.Holds (le obligation.1) assignment

theorem result_map_exact (meaning : γ → Prop) (map : β → γ) (result : Option (List β)) :
    ResultHolds meaning (result.map (List.map map)) ↔
      ResultHolds (fun item => meaning (map item)) result := by
  cases result <;> simp

theorem decompose_context_argument_exact (le : Bool → Endpoint α → Endpoint α → Prop)
    (assignment : α → Comp Common.model) (inherited : Bool) (parameter : Parameter)
    (first last : Argument α) :
    ResultHolds (ContextObligation.Holds le assignment)
      (decomposeContextArgument inherited parameter first last) ↔
        ArgumentRel (le (childContext inherited parameter)) assignment
          (effectiveParameter inherited parameter) first last := by
  rw [decomposeContextArgument, result_map_exact]
  simpa only [ContextObligation.Holds] using
    decompose_argument_exact (le (childContext inherited parameter)) assignment
      (effectiveParameter inherited parameter) first last

def ContextArgumentsRel (le : Bool → Endpoint α → Endpoint α → Prop)
    (assignment : α → Comp Common.model) (inherited : Bool) :
    Declaration → List (Argument α) → List (Argument α) → Prop
  | [], [], [] => True
  | parameter :: rest, first :: tail, last :: suffix =>
      ArgumentRel (le (childContext inherited parameter)) assignment
        (effectiveParameter inherited parameter) first last ∧
        ContextArgumentsRel le assignment inherited rest tail suffix
  | _, _, _ => False

theorem decompose_context_arguments_exact (le : Bool → Endpoint α → Endpoint α → Prop)
    (assignment : α → Comp Common.model) (inherited : Bool) (declaration : Declaration)
    (first last : List (Argument α)) :
    ResultHolds (ContextObligation.Holds le assignment)
      (decomposeContextArguments inherited declaration first last) ↔
        ContextArgumentsRel le assignment inherited declaration first last := by
  induction declaration generalizing first last with
  | nil => cases first <;> cases last <;> simp [decomposeContextArguments, ContextArgumentsRel]
  | cons parameter rest ih =>
      cases first with
      | nil => cases last <;> simp [decomposeContextArguments, ContextArgumentsRel]
      | cons first tail =>
          cases last with
          | nil => simp [decomposeContextArguments, ContextArgumentsRel]
          | cons last suffix =>
              simp only [decomposeContextArguments, append_exact, decompose_context_argument_exact,
                ih, ContextArgumentsRel]

theorem decompose_context_argument_size_lt (inherited : Bool) (parameter : Parameter)
    (first last : Argument α) (obligations : List (ContextObligation α))
    (returned : decomposeContextArgument inherited parameter first last = some obligations)
    (context : Bool) (a b : Endpoint α) (member : (context, .value a b) ∈ obligations) :
    max (sizeOf a) (sizeOf b) < max (sizeOf first) (sizeOf last) := by
  obtain ⟨original, generated, rfl⟩ := Option.map_eq_some_iff.mp returned
  obtain ⟨obligation, present, same⟩ := List.mem_map.mp member
  have shape : obligation = .value a b := congrArg Prod.snd same
  subst obligation
  exact decompose_argument_size_lt _ first last original generated a b present

theorem decompose_context_arguments_size_lt (inherited : Bool) (declaration : Declaration)
    (first last : List (Argument α)) (obligations : List (ContextObligation α))
    (returned : decomposeContextArguments inherited declaration first last = some obligations)
    (context : Bool) (a b : Endpoint α) (member : (context, .value a b) ∈ obligations) :
    max (sizeOf a) (sizeOf b) < max (sizeOf first) (sizeOf last) := by
  induction declaration generalizing first last obligations with
  | nil => cases first <;> cases last <;> simp [decomposeContextArguments] at returned
           subst obligations; cases member
  | cons parameter rest ih =>
      cases first with
      | nil => cases last <;> cases returned
      | cons first tail =>
          cases last with
          | nil => cases returned
          | cons last suffix =>
              rcases mem_append_result returned (context, .value a b) member with before | after
              · obtain ⟨before, generated, present⟩ := before
                have small := decompose_context_argument_size_lt inherited parameter first last before
                  generated context a b present
                simp only [List.cons.sizeOf_spec]
                omega
              · obtain ⟨after, generated, present⟩ := after
                have small := ih tail suffix after generated present
                simp only [List.cons.sizeOf_spec]
                omega

/-- The context is retained as part of every actual emitted obligation. -/
def inspectContext (registry : Registry) (inherited : Bool)
    (first last : Endpoint α) : Option (List (Atom α)) :=
  match first, last with
  | .ordinary a, .ordinary b => some [.tyLe a b]
  | .nominal name before, .nominal other after =>
      if name = other then
        match registry[name]? with
        | none => none
        | some declaration =>
            match returned : decomposeContextArguments inherited declaration before after with
            | none => none
            | some obligations =>
                concatenate (obligations.attach.map fun obligation =>
                  match shape : obligation.val.2 with
                  | .row a b => some [.rowLe a b]
                  | .value a b =>
                      have present : (obligation.val.1, .value a b) ∈ obligations := by
                        simpa only [← shape] using obligation.property
                      have _smaller := decompose_context_arguments_size_lt inherited declaration
                        before after obligations returned obligation.val.1 a b present
                      inspectContext registry obligation.val.1 a b)
      else none
  | _, _ => none
termination_by max (sizeOf first) (sizeOf last)
decreasing_by
  simp only [Endpoint.nominal.sizeOf_spec]
  omega

def inspectContextObligation (registry : Registry) (obligation : ContextObligation α) :
    Option (List (Atom α)) :=
  match obligation.2 with
  | .value first last => inspectContext registry obligation.1 first last
  | .row first last => some [.rowLe first last]

theorem inspect_context_nominal (registry : Registry) (inherited : Bool) (name : Nat)
    (first last : List (Argument α)) (declaration : Declaration)
    (obligations : List (ContextObligation α)) (declared : registry[name]? = some declaration)
    (generated : decomposeContextArguments inherited declaration first last = some obligations) :
    inspectContext registry inherited (.nominal name first) (.nominal name last) =
      concatenate (obligations.map (inspectContextObligation registry)) := by
  rw [inspectContext]
  simp only [↓reduceIte, declared]
  split
  · rename_i absent
    simp [absent] at generated
  · rename_i parts returned
    have same : parts = obligations := Option.some.inj (returned.symm.trans generated)
    subst parts
    congr 1
    calc
      _ = obligations.attach.map (fun obligation => inspectContextObligation registry obligation.val) := by
        apply List.map_congr_left
        intro obligation _
        rcases obligation with ⟨⟨context, obligation⟩, present⟩
        cases obligation <;> rfl
      _ = _ := List.attach_map_val

end Yulang.CommonRecursiveNominalIntervals
