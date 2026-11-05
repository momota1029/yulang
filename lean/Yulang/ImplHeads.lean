import Yulang.CheckedRoles
import Yulang.Methods

/-!
# Anonymous impl-head variables and nominal receiver matching

Spec §6.2: every `_` in an impl head introduces a separate unnamed variable;
named variables may repeat, and `where` cannot refer to anonymous variables.
The lowering reserves even identifiers for resolved named variables and assigns
successive odd identifiers to hole occurrences. Its counting theorems establish
both freshness and preservation of named sharing for arbitrary finite heads.

Spec §6.4: a ref receiver is an ordinary nominal application. The existing
one-way head matcher checks that whole application and never tries its content.
The examples connect the lowered heads to the actual role matcher and generic
union-method selector. Method visibility, lookup priority and source row/type
kind checking remain upstream; no new priority or ref-specific fallback is added.
-/

namespace Yulang.ImplHeads

open Roles

inductive Head where
  | named : Nat → Head
  | hole
  | app : Nat → List Head → Head
  deriving Repr

mutual
  def holes : Head → Nat
    | .named _ => 0
    | .hole => 1
    | .app _ args => argsHoles args
  def argsHoles : List Head → Nat
    | [] => 0
    | head :: tail => holes head + argsHoles tail
end

private theorem interval_counts_add (start countFirst countRest index : Nat) :
    (if start ≤ index ∧ index < start + countFirst then 1 else 0) +
      (if start + countFirst ≤ index ∧ index < start + countFirst + countRest then 1 else 0) =
        (if start ≤ index ∧ index < start + (countFirst + countRest) then 1 else 0) := by
  by_cases first : start ≤ index ∧ index < start + countFirst
  · have outsideRest : ¬ (start + countFirst ≤ index ∧
        index < start + countFirst + countRest) := by omega
    have total : start ≤ index ∧ index < start + (countFirst + countRest) := by omega
    rw [ite_eq_left first, ite_eq_right outsideRest, ite_eq_left total]
  · by_cases rest : start + countFirst ≤ index ∧ index < start + countFirst + countRest
    · have total : start ≤ index ∧ index < start + (countFirst + countRest) := by omega
      rw [ite_eq_right first, ite_eq_left rest, ite_eq_left total]
    · have outside : ¬ (start ≤ index ∧ index < start + (countFirst + countRest)) := by omega
      rw [ite_eq_right first, ite_eq_right rest, ite_eq_right outside]

mutual
  def lower (start : Nat) : Head → Term
    | .named name => .var (2 * name)
    | .hole => .var (2 * start + 1)
    | .app name args => .app name (lowerArgs start args)
  def lowerArgs (start : Nat) : List Head → List Term
    | [] => []
    | head :: tail => lower start head :: lowerArgs (start + holes head) tail
end

mutual
  def namedOccurrences (name : Nat) : Head → Nat
    | .named current => if name = current then 1 else 0
    | .hole => 0
    | .app _ args => argsNamedOccurrences name args
  def argsNamedOccurrences (name : Nat) : List Head → Nat
    | [] => 0
    | head :: tail => namedOccurrences name head + argsNamedOccurrences name tail
end

mutual
  /-- Every allocated anonymous identifier occurs once, and no others occur. -/
  theorem anonymous_occurrences (head : Head) (start index : Nat) :
      (lower start head).occurrences (2 * index + 1) =
        if start ≤ index ∧ index < start + holes head then 1 else 0 := by
    cases head with
    | named name =>
        have different : 2 * index + 1 ≠ 2 * name := by omega
        have outside : ¬ (start ≤ index ∧ index < start + holes (.named name)) := by
          change ¬ (start ≤ index ∧ index < start + 0)
          omega
        rw [ite_eq_right outside]
        simp [lower, Term.occurrences, different]
    | hole =>
        by_cases same : index = start
        · subst index
          have inside : start ≤ start ∧ start < start + holes .hole := by
            change start ≤ start ∧ start < start + 1
            omega
          rw [ite_eq_left inside]
          simp [lower, Term.occurrences]
        · have different : 2 * index + 1 ≠ 2 * start + 1 := by omega
          have outside : ¬ (start ≤ index ∧ index < start + holes .hole) := by
            change ¬ (start ≤ index ∧ index < start + 1)
            omega
          rw [ite_eq_right outside]
          simp only [lower, Term.occurrences]
          exact ite_eq_right different
    | app name args => exact args_anonymous_occurrences args start index
  theorem args_anonymous_occurrences (args : List Head) (start index : Nat) :
      argsOccurrences (2 * index + 1) (lowerArgs start args) =
        if start ≤ index ∧ index < start + argsHoles args then 1 else 0 := by
    cases args with
    | nil =>
        have outside : ¬ (start ≤ index ∧ index < start + argsHoles []) := by
          change ¬ (start ≤ index ∧ index < start + 0)
          omega
        rw [ite_eq_right outside]
        rfl
    | cons head tail =>
        simp only [lowerArgs, argsOccurrences, anonymous_occurrences,
          args_anonymous_occurrences, argsHoles]
        exact interval_counts_add start (holes head) (argsHoles tail) index
end

mutual
  /-- Repeated explicit names keep exactly their original sharing. -/
  theorem named_occurrences (head : Head) (start name : Nat) :
      (lower start head).occurrences (2 * name) = namedOccurrences name head := by
    cases head with
    | named current =>
        have same : (2 * name = 2 * current) ↔ name = current := by omega
        simp [lower, Term.occurrences, namedOccurrences, same]
    | hole => simp [lower, Term.occurrences, namedOccurrences, show 2 * name ≠ 2 * start + 1 by omega]
    | app _ args => exact args_named_occurrences args start name
  theorem args_named_occurrences (args : List Head) (start name : Nat) :
      argsOccurrences (2 * name) (lowerArgs start args) = argsNamedOccurrences name args := by
    cases args with
    | nil => rfl
    | cons head tail => simp [lowerArgs, argsOccurrences, argsNamedOccurrences,
        named_occurrences, args_named_occurrences]
end

theorem anonymous_identifiers_distinct {left right : Nat} (different : left ≠ right) :
    2 * left + 1 ≠ 2 * right + 1 := by omega

theorem anonymous_cannot_capture_named (anonymous named : Nat) :
    2 * anonymous + 1 ≠ 2 * named := by omega

mutual
  /-- A where-term has resolved names, with no anonymous-variable syntax. -/
  def namedHead : Term → Head
    | .var name => .named name
    | .app name args => .app name (namedArgs args)
  def namedArgs : List Term → List Head
    | [] => []
    | head :: tail => namedHead head :: namedArgs tail
end

mutual
  theorem namedHead_no_holes (term : Term) : holes (namedHead term) = 0 := by
    cases term with
    | var _ => rfl
    | app _ args => exact namedArgs_no_holes args
  theorem namedArgs_no_holes (args : List Term) : argsHoles (namedArgs args) = 0 := by
    cases args with
    | nil => rfl
    | cons head tail => simp [namedArgs, argsHoles, namedHead_no_holes, namedArgs_no_holes]
end

def lowerWhere (term : Term) : Term := lower 0 (namedHead term)

theorem where_cannot_reference_anonymous (term : Term) (index : Nat) :
    (lowerWhere term).occurrences (2 * index + 1) = 0 := by
  simp [lowerWhere, anonymous_occurrences, namedHead_no_holes]

def lowerGoal (goal : Goal) : Goal :=
  ⟨goal.role, goal.args.map lowerWhere⟩

def declaration (role : Nat) (head : List Head) (conditions : List Goal) (id : Nat) : Impl :=
  ⟨role, lowerArgs 0 head, conditions.map lowerGoal, id⟩

/-- Lowered declarations use the existing exact one-way matcher, without a
special wildcard or reference rule inside the resolver. -/
theorem declaration_matches (role : Nat) (head : List Head)
    (conditions : List Goal) (id : Nat) (arguments : List Term) :
    headMatches (declaration role head conditions id) ⟨role, arguments⟩ = true ↔
      ∃ substitution, substArgs substitution (lowerArgs 0 head) = arguments := by
  simp [matches_iff, Matches, declaration]

/-- Substitution preserves the outer nominal constructor. -/
theorem whole_receiver_constructor (owner receiver : Nat) (parameters arguments : List Term)
    (substitution : Subst)
    (matched : (Term.app owner parameters).subst substitution = .app receiver arguments) :
    owner = receiver := by
  exact (Term.app.inj matched).1

theorem other_constructor_does_not_match (role owner receiver id : Nat)
    (parameters arguments : List Term) (conditions : List Goal) (different : owner ≠ receiver) :
    headMatches ⟨role, [.app owner parameters], conditions, id⟩
      ⟨role, [.app receiver arguments]⟩ = false := by
  cases matched : headMatches (⟨role, [.app owner parameters], conditions, id⟩ : Impl)
      ⟨role, [.app receiver arguments]⟩ with
  | false => rfl
  | true =>
      obtain ⟨_, substitution, equal⟩ := (matches_iff _ _).mp matched
      have same : (Term.app owner parameters).subst substitution = .app receiver arguments := by
        exact List.cons.inj equal |>.1
      exact False.elim (different (whole_receiver_constructor _ _ _ _ _ same))

namespace Examples

def integer : Term := .app 0 []
def string : Term := .app 1 []
def reference (effect content : Term) : Term := .app 2 [effect, content]
def pair (left right : Term) : Term := .app 3 [left, right]

def anonymousPair : Impl := declaration 0 [.app 3 [.hole, .hole]] [] 0
def sharedPair : Impl := declaration 0 [.app 3 [.named 0, .named 0]] [] 1
def integerMethod : Impl := declaration 0 [.app 0 []] [] 2
def referenceIntegerMethod : Impl := declaration 0 [.app 2 [.hole, .app 0 []]] [] 3

theorem two_holes_accept_all_types (left right : Term) :
    headMatches anonymousPair ⟨0, [pair left right]⟩ = true := by
  apply (matches_iff _ _).mpr
  refine ⟨rfl, fun index => if index = 1 then left else right, ?_⟩
  rfl

theorem repeated_name_matches_iff_equal (left right : Term) :
    headMatches sharedPair ⟨0, [pair left right]⟩ = true ↔ left = right := by
  rw [matches_iff]
  constructor
  · rintro ⟨_, substitution, equal⟩
    have same : substitution 0 = left ∧ substitution 0 = right := by
      simpa [sharedPair, declaration, lowerArgs, lower, holes, pair, substArgs, Term.subst]
        using equal
    exact same.1.symm.trans same.2
  · intro equal
    subst right
    exact ⟨rfl, fun _ => left, rfl⟩

theorem two_holes_accept_different_types :
    headMatches anonymousPair ⟨0, [pair integer string]⟩ = true := by decide

theorem repeated_name_rejects_different_types :
    headMatches sharedPair ⟨0, [pair integer string]⟩ = false := by decide

theorem holes_and_named_variables_are_disjoint :
    lowerArgs 0 [.hole, .named 0, .hole, .named 0] = [.var 1, .var 0, .var 3, .var 0] := rfl

theorem ref_does_not_delegate_to_content (effect : Term) :
    headMatches integerMethod ⟨0, [reference effect integer]⟩ = false :=
  other_constructor_does_not_match 0 0 2 2 [] [effect, integer] [] (by decide)

theorem ref_specialization_accepts_any_effect (effect : Term) :
    headMatches referenceIntegerMethod ⟨0, [reference effect integer]⟩ = true := by
  apply (matches_iff _ _).mpr
  refine ⟨rfl, fun _ => effect, ?_⟩
  rfl

theorem ref_specialization_rejects_other_content (effect : Term) :
    headMatches referenceIntegerMethod ⟨0, [reference effect string]⟩ = false := by
  simp [headMatches, referenceIntegerMethod, declaration, lowerArgs, lower,
    matchingSubst, extractArgs, Term.extract, substArgs, Term.subst, reference, string]

theorem method_selection_does_not_dereference (effect : Term) :
    Methods.resolve (fun receiver => headMatches integerMethod ⟨0, [receiver]⟩)
      [reference effect integer] = .missing := by
  simp [Methods.resolve, Methods.candidates, ref_does_not_delegate_to_content, Methods.select]

theorem specialized_ref_method_is_selected (effect : Term) :
    Methods.resolve (fun receiver => headMatches referenceIntegerMethod ⟨0, [receiver]⟩)
      [reference effect integer] = .unique (reference effect integer) := by
  simp [Methods.resolve, Methods.candidates, ref_specialization_accepts_any_effect,
    Methods.select, Methods.AllEqual]

end Examples
end Yulang.ImplHeads
