import Yulang.CommonRecursiveNominalIntervals

/-!
# Recursive compilation of open nominal endpoint obligations

The recursion follows finite endpoint descriptions. Every invariant step
returns both old consistency checks and both cross checks through this same
ordinary-subtyping decomposition, including nondegenerate bounds inside the
endpoints. Its measure is the maximum endpoint size: using a sum would be
incorrect because an old consistency check can reuse the larger side twice.

No fuel, bound on nesting, endpoint oracle or representative argument occurs
in the compiler. A failed decomposition marks the exact finite structural
grammar boundary; this is not the full source subtype decision procedure.
-/

namespace Yulang.CommonRecursiveNominalIntervals

open Core.PresenceGeneration (TyTerm RowTerm Comp)
open CommonDeclaredNominalInspection (Kind Parameter Declaration Registry)
open CommonDeclaredNominalVariance (Variance)
open PresenceNormalForm (Atom All)

theorem Bounds.lower_size_lt [SizeOf Term] (bounds : Bounds Term) :
    sizeOf bounds.lower < sizeOf bounds := by
  cases bounds <;> simp only [Bounds.lower, Bounds.point.sizeOf_spec, Bounds.interval.sizeOf_spec] <;> omega

theorem Bounds.upper_size_lt [SizeOf Term] (bounds : Bounds Term) :
    sizeOf bounds.upper < sizeOf bounds := by
  cases bounds <;> simp only [Bounds.upper, Bounds.point.sizeOf_spec, Bounds.interval.sizeOf_spec] <;> omega

theorem Bounds.check_size_lt [SizeOf Term] (first last : Bounds Term)
    (a b : Term) (member : (a, b) ∈ first.checks last) :
    max (sizeOf a) (sizeOf b) < max (sizeOf first) (sizeOf last) := by
  have firstLower := first.lower_size_lt
  have firstUpper := first.upper_size_lt
  have lastLower := last.lower_size_lt
  have lastUpper := last.upper_size_lt
  simp only [Bounds.checks, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with equal | equal | equal | equal <;> cases equal <;> omega

theorem value_check_size_lt (first last : Bounds (Endpoint α))
    (a b : Endpoint α) (member : Obligation.value a b ∈ valueChecks first last) :
    max (sizeOf a) (sizeOf b) < max (sizeOf first) (sizeOf last) := by
  obtain ⟨pair, present, same⟩ := List.mem_map.mp member
  have components : pair = (a, b) := by cases pair; cases same; rfl
  subst pair
  exact Bounds.check_size_lt first last a b present

theorem decompose_argument_size_lt (parameter : Parameter) (first last : Argument α)
    (obligations : List (Obligation α))
    (returned : decomposeArgument parameter first last = some obligations)
    (a b : Endpoint α) (member : Obligation.value a b ∈ obligations) :
    max (sizeOf a) (sizeOf b) < max (sizeOf first) (sizeOf last) := by
  rcases parameter with ⟨kind, mode⟩
  cases first with
  | inl first =>
      cases last with
      | inr last => cases first <;> cases last <;> cases kind <;> cases mode <;> cases returned
      | inl last =>
          cases kind with
          | row => cases mode <;> cases returned
          | value =>
              cases mode with
              | unused => simp [decomposeArgument] at returned; subst obligations; cases member
              | invariant =>
                  simp only [decomposeArgument, Option.some.injEq] at returned
                  subst obligations
                  have small := value_check_size_lt first last a b member
                  simp only [Sum.inl.sizeOf_spec]
                  omega
              | covariant | contravariant =>
                  cases first <;> cases last <;> simp [decomposeArgument] at returned
                  all_goals subst obligations
                  all_goals simp only [List.mem_singleton, Obligation.value.injEq] at member
                  all_goals obtain ⟨rfl, rfl⟩ := member
                  all_goals simp only [Sum.inl.sizeOf_spec, Bounds.point.sizeOf_spec]; omega
  | inr first =>
      cases last with
      | inl last => cases first <;> cases last <;> cases kind <;> cases mode <;> cases returned
      | inr last =>
          cases kind <;> cases mode <;> cases first <;> cases last <;>
            simp [decomposeArgument] at returned
          all_goals subst obligations
          all_goals simp [rowChecks, List.mem_map] at member

theorem mem_append_result {first last : Option (List β)} {items : List β}
    (returned : append first last = some items) (item : β) (member : item ∈ items) :
    (∃ before, first = some before ∧ item ∈ before) ∨
      ∃ after, last = some after ∧ item ∈ after := by
  cases first with
  | none => cases returned
  | some before =>
      cases last with
      | none => cases returned
      | some after =>
          have same : before ++ after = items := Option.some.inj returned
          subst items
          exact (List.mem_append.mp member).elim
            (fun present => Or.inl ⟨before, rfl, present⟩)
            (fun present => Or.inr ⟨after, rfl, present⟩)

theorem decompose_arguments_size_lt (declaration : Declaration)
    (first last : List (Argument α)) (obligations : List (Obligation α))
    (returned : decomposeArguments declaration first last = some obligations)
    (a b : Endpoint α) (member : Obligation.value a b ∈ obligations) :
    max (sizeOf a) (sizeOf b) < max (sizeOf first) (sizeOf last) := by
  induction declaration generalizing first last obligations with
  | nil => cases first <;> cases last <;> simp [decomposeArguments] at returned
           subst obligations; cases member
  | cons parameter rest ih =>
      cases first with
      | nil => cases last <;> cases returned
      | cons first tail =>
          cases last with
          | nil => cases returned
          | cons last suffix =>
              rcases mem_append_result returned (.value a b) member with before | after
              · obtain ⟨before, generated, present⟩ := before
                have small := decompose_argument_size_lt parameter first last before generated a b present
                simp only [List.cons.sizeOf_spec]
                omega
              · obtain ⟨after, generated, present⟩ := after
                have small := ih tail suffix after generated present
                simp only [List.cons.sizeOf_spec]
                omega

def concatenate : List (Option (List β)) → Option (List β)
  | [] => some []
  | first :: rest => append first (concatenate rest)

theorem concatenate_exact (meaning : β → Prop) (parts : List (Option (List β))) :
    ResultHolds meaning (concatenate parts) ↔ ∀ part ∈ parts, ResultHolds meaning part := by
  induction parts with
  | nil => simp [concatenate]
  | cons first rest ih => simp only [concatenate, append_exact, ih, List.forall_mem_cons]

/-- Each recursive call is an actual emitted value obligation. The metadata
lookup and argument-kind/arity checks are performed at every nominal layer. -/
def inspect (registry : Registry) (first last : Endpoint α) : Option (List (Atom α)) :=
  match first, last with
  | .ordinary a, .ordinary b => some [.tyLe a b]
  | .nominal name before, .nominal other after =>
      if name = other then
        match registry[name]? with
        | none => none
        | some declaration =>
            match returned : decomposeArguments declaration before after with
            | none => none
            | some obligations =>
                concatenate (obligations.attach.map fun obligation =>
                  match shape : obligation.val with
                  | .row a b => some [.rowLe a b]
                  | .value a b =>
                      have _smaller := decompose_arguments_size_lt declaration before after obligations
                        returned a b (shape ▸ obligation.property)
                      inspect registry a b)
      else none
  | _, _ => none
termination_by max (sizeOf first) (sizeOf last)
decreasing_by
  simp only [Endpoint.nominal.sizeOf_spec]
  omega

end Yulang.CommonRecursiveNominalIntervals
