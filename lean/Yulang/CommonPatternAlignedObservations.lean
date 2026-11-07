import Yulang.CommonPatternMatchPaths

/-! Relational observations retain literal event traces and error identities,
while successful binding lists may differ by name-preserving alignment. -/

namespace Yulang.CommonPatternAlignedObservations

open CaseValues CasePatterns EvaluationTrace
open CommonPatternBindingAlignment (LookupEq reorder lookup)

inductive ResultRel (relation : A → B → Prop) : Except R A → Except R B → Prop where
  | error : ResultRel relation (.error error) (.error error)
  | ok : relation first last → ResultRel relation (.ok first) (.ok last)

def LoggedRel (relation : A → B → Prop) (first : Logged E R A) (last : Logged E R B) : Prop :=
  first.trace = last.trace ∧ ResultRel relation first.result last.result

theorem logged_bind {first : Logged E R A} {last : Logged E R B}
    (same : LoggedRel relation first last)
    (firstNext : A → Logged E R C) (lastNext : B → Logged E R D)
    (next : ∀ a b, relation a b → LoggedRel after (firstNext a) (lastNext b)) :
    LoggedRel after (first.bind firstNext) (last.bind lastNext) := by
  rcases first with ⟨firstTrace, firstResult⟩
  rcases last with ⟨lastTrace, lastResult⟩
  rcases same with ⟨traceSame, results⟩
  change firstTrace = lastTrace at traceSame
  cases results with
  | error => exact ⟨traceSame, .error⟩
  | ok related =>
      have continuations := next _ _ related
      exact ⟨by simp only [Logged.bind, traceSame, continuations.1],
        continuations.2⟩

theorem logged_equal (value : Logged E R A) : LoggedRel Eq value value := by
  refine ⟨rfl, ?_⟩
  cases value.result with
  | error => exact .error
  | ok => exact .ok rfl

theorem logged_prepend {first : Logged E R A} {last : Logged E R B}
    (same : LoggedRel relation first last) (events : List E) :
    LoggedRel relation (Logged.prepend events first) (Logged.prepend events last) :=
  ⟨by simp only [Logged.prepend, same.1], same.2⟩

theorem logged_eq_of_rel {first last : Logged E R A} (same : LoggedRel Eq first last) : first = last := by
  rcases first with ⟨firstTrace, firstResult⟩
  rcases last with ⟨lastTrace, lastResult⟩
  rcases same with ⟨traceSame, results⟩
  change firstTrace = lastTrace at traceSame
  cases traceSame
  cases results with
  | error => rfl
  | ok equal => cases equal; rfl

inductive MatchRel : Option (Bindings F) → Option (Bindings F) → Prop where
  | miss : MatchRel none none
  | hit : LookupEq first last → MatchRel (some first) (some last)

abbrev Equivalent (first last : Observation F E R) := LoggedRel MatchRel first last

theorem equivalent_success {first last : Bindings F} (same : LookupEq first last) :
    Equivalent (success (E := E) (R := R) first) (success last) := ⟨rfl, .ok (.hit same)⟩

theorem equivalent_miss : Equivalent (miss : Observation F E R) miss := ⟨rfl, .ok .miss⟩

theorem lookup_eq_append {first first' last last' : Bindings F}
    (before : LookupEq first first') (after : LookupEq last last') :
    LookupEq (first ++ last) (first' ++ last') := by
  intro name
  simp only [CommonPatternBindingAlignment.lookup_append, before name, after name]

theorem andThen_equivalent {first last : Observation F E R} (same : Equivalent first last)
    (firstNext lastNext : Bindings F → Observation F E R)
    (next : ∀ a b, LookupEq a b → Equivalent (firstNext a) (lastNext b)) :
    Equivalent (ScopedCasePatterns.andThen first firstNext) (ScopedCasePatterns.andThen last lastNext) := by
  apply logged_bind same
  intro a b related
  cases related with
  | miss => exact equivalent_miss
  | hit before =>
      apply logged_bind (next _ _ before)
      intro a b related
      cases related with
      | miss => exact equivalent_miss
      | hit after => exact equivalent_success (lookup_eq_append before after)

def alignResult (names : List Nat) (observed : Observation F E R) : Observation F E R :=
  ⟨observed.trace, observed.result.map (fun option => option.map (reorder names))⟩

theorem lookup_eq_names {first last : List (Nat × A)} (same : LookupEq first last) (name : Nat) :
    name ∈ first.map Prod.fst ↔ name ∈ last.map Prod.fst := by
  rw [← CommonPatternBindingAlignment.lookup_isSome, ← CommonPatternBindingAlignment.lookup_isSome, same name]

theorem alignResult_equivalent {first last : Observation F E R} (same : Equivalent first last)
    (names : List Nat)
    (retained : ∀ output, last.result = .ok (some output) → ∀ name ∈ output.map Prod.fst, name ∈ names) :
    Equivalent (alignResult names first) last := by
  rcases first with ⟨firstTrace, firstResult⟩
  rcases last with ⟨lastTrace, lastResult⟩
  rcases same with ⟨traceSame, results⟩
  refine ⟨traceSame, ?_⟩
  cases results with
  | error => exact .error
  | ok matched =>
      cases matched with
      | miss => exact .ok .miss
      | @hit first last same =>
          apply ResultRel.ok
          apply MatchRel.hit
          have ordered := CommonPatternBindingAlignment.reorder_lookup_eq names first
            (fun name member => retained last rfl name ((lookup_eq_names same name).mp member))
          intro name
          exact (ordered name).trans (same name)

end Yulang.CommonPatternAlignedObservations
