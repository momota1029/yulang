import Yulang.Inference
import Yulang.RolesAssoc

/-!
# Deferred role predicates and ordinary associated-type equations

Role predicates are finite data over the existing first-order type terms.
Abstract dictionaries and concrete impl resolution are distinct: a definition
may assume its local qualifiers, whereas a use must discharge them. The concrete
adapter uses the checked resolver, including its ambiguity policy.

Associated-type resolution only adds an ordinary equation. The store lemmas
describe all substitutions, not a chosen eager binding of the associated slot.
They do not claim a solver for the combined structural-subtyping problem.
-/

namespace Yulang.RoleConstraints

open Inference

structure Predicate (Ty : Type u) where
  role : Nat
  args : List Ty
  deriving DecidableEq, Repr

def Predicate.map (f : A → B) (p : Predicate A) : Predicate B :=
  ⟨p.role, p.args.map f⟩

abbrev Goal (α : Type) := Predicate (TyTerm α)
abbrev Theory (m : Model) := Predicate m.Ty → Prop

def Goal.eval (m : Model) (ρ : α → Comp m) (g : Goal α) : Predicate m.Ty :=
  g.map (TyTerm.eval m ρ)

def Goal.rename (f : α → β) (g : Goal α) : Goal β := g.map (TyTerm.rename f)
def Goal.subst (f : α → CompTerm β) (g : Goal α) : Goal β := g.map (TyTerm.subst f)

@[simp] theorem Goal.eval_rename (m : Model) (ρ : β → Comp m)
    (f : α → β) (g : Goal α) :
    (g.rename f).eval m ρ = g.eval m (ρ ∘ f) := by
  cases g
  simp [rename, eval, Predicate.map, List.map_map, Function.comp_def]

@[simp] theorem Goal.eval_subst (m : Model) (ρ : β → Comp m)
    (f : α → CompTerm β) (g : Goal α) :
    (g.subst f).eval m ρ = g.eval m (fun x => (f x).eval m ρ) := by
  cases g
  simp [subst, eval, Predicate.map, List.map_map, Function.comp_def]

def Satisfies (theory : Predicate Ty → Prop) (goals : List (Predicate Ty)) : Prop :=
  ∀ goal ∈ goals, theory goal

/-- Only the explicitly supplied dictionaries are added to a theory. -/
def WithEvidence (theory : Predicate Ty → Prop) (evidence : List (Predicate Ty)) :
    Predicate Ty → Prop := fun goal => theory goal ∨ goal ∈ evidence

theorem given_satisfies (theory : Predicate Ty → Prop) (evidence : List (Predicate Ty)) :
    Satisfies (WithEvidence theory evidence) evidence := fun _ h => Or.inr h

theorem no_new_evidence (theory : Predicate Ty → Prop) (evidence : List (Predicate Ty))
    (goal : Predicate Ty) (absent : goal ∉ evidence) :
    WithEvidence theory evidence goal ↔ theory goal := by
  simp [WithEvidence, absent]

def Predicate.toGoal (p : Predicate Roles.Term) : Roles.Goal := ⟨p.role, p.args⟩

/-- Concrete evidence includes uniqueness; mere derivability would accept an
ambiguous impl database and would not match the language's resolver. -/
def Resolves (impls : List Roles.Impl) (goal : Roles.Goal) : Prop :=
  Roles.Derives impls goal ∧ ¬ Roles.ReachesOverlap impls goal

theorem resolve_exact (impls : List Roles.Impl) (wf : Roles.WellFormed impls) (goal : Roles.Goal) :
    Roles.resolve impls wf goal = .resolved ↔ Resolves impls goal := by
  constructor
  · intro resolved
    refine ⟨Roles.resolve_sound impls wf goal resolved, ?_⟩
    intro overlap
    have ambiguous := (Roles.resolve_ambiguous_iff impls wf goal).mpr overlap
    rw [resolved] at ambiguous
    cases ambiguous
  · rintro ⟨derivation, unique⟩
    exact Roles.resolve_complete impls wf goal derivation unique

def resolvingTheory {m : Model} (decode : m.Ty → Roles.Term) (impls : List Roles.Impl) : Theory m :=
  fun goal => Resolves impls ((goal.map decode).toGoal)

theorem resolvingTheory_iff {m : Model} (decode : m.Ty → Roles.Term) (impls : List Roles.Impl)
    (wf : Roles.WellFormed impls) (goal : Predicate m.Ty) :
    resolvingTheory decode impls goal ↔
      Roles.resolve impls wf (goal.map decode).toGoal = .resolved :=
  (resolve_exact impls wf _).symm

theorem empty_resolver_has_no_evidence (goal : Roles.Goal) : ¬ Resolves [] goal := by
  rintro ⟨derivation, _⟩
  cases derivation with
  | impl _ _ member _ _ _ => cases member

structure Equation where
  left : Roles.Term
  right : Roles.Term
  deriving DecidableEq, Repr

def Equation.Holds (σ : Roles.Subst) (equation : Equation) : Prop :=
  equation.left.subst σ = equation.right.subst σ

abbrev Store := List Equation

def Store.Holds (σ : Roles.Subst) (store : Store) : Prop :=
  ∀ equation ∈ store, equation.Holds σ

def Store.check (σ : Roles.Subst) (store : Store) : Bool :=
  store.all (fun equation => decide (equation.left.subst σ = equation.right.subst σ))

@[simp] theorem Store.check_exact (σ : Roles.Subst) (store : Store) :
    store.check σ = true ↔ store.Holds σ := by
  simp [check, Holds, Equation.Holds, List.all_eq_true]

theorem Store.append_exact (σ : Roles.Subst) (left right : Store) :
    Store.Holds σ (left ++ right) ↔ left.Holds σ ∧ right.Holds σ := by
  simp [Holds, List.mem_append, or_imp, forall_and]

theorem Store.add_comm (σ : Roles.Subst) (store : Store) (a b : Equation) :
    Store.Holds σ (a :: b :: store) ↔ Store.Holds σ (b :: a :: store) := by
  simp [Holds, and_left_comm]

theorem Store.add_idempotent (σ : Roles.Subst) (store : Store) (a : Equation) :
    Store.Holds σ (a :: a :: store) ↔ Store.Holds σ (a :: store) := by
  simp [Holds]

theorem Store.order_independent (σ : Roles.Subst) {left right : Store}
    (permutation : left.Perm right) : left.Holds σ ↔ right.Holds σ := by
  simp only [Holds]
  constructor <;> intro h equation member
  · exact h equation (permutation.mem_iff.mpr member)
  · exact h equation (permutation.mem_iff.mp member)

def Store.SolutionsEqual (left right : Store) : Prop :=
  ∀ σ, left.Holds σ ↔ right.Holds σ

theorem Store.permutation_preserves_solutions {left right : Store} (h : left.Perm right) :
    left.SolutionsEqual right := fun σ => order_independent σ h

/-- At a supplied substitution, an added equation either checks or contradicts
the store. This executable check does not search for a substitution. -/
theorem Store.check_dichotomy (σ : Roles.Subst) (store : Store) :
    (store.check σ = true ∧ store.Holds σ) ∨
      (store.check σ = false ∧ ¬ store.Holds σ) := by
  cases h : store.check σ with
  | false => exact Or.inr ⟨rfl, by intro held; rw [(check_exact σ store).mpr held] at h; cases h⟩
  | true => exact Or.inl ⟨rfl, (check_exact σ store).mp h⟩

/-- The associated variable is not assigned by selecting an impl. Its ordinary
equation is appended to whatever constraints were already accumulated. -/
def addAssociated (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (goal : Roles.Goal) (name slot : Nat)
    (store : Store) : Option Store :=
  (Roles.assocOf env roles wf goal name).map (fun value => ⟨.var slot, value⟩ :: store)

theorem add_associated_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (goal : Roles.Goal) (name slot : Nat)
    (store : Store) (value : Roles.Term) (selected : Roles.assocOf env roles wf goal name = some value)
    (σ : Roles.Subst) :
    addAssociated env roles wf goal name slot store = some (⟨.var slot, value⟩ :: store) ∧
      (Store.Holds σ (⟨.var slot, value⟩ :: store) ↔ σ slot = value.subst σ ∧ store.Holds σ) := by
  constructor
  · simp [addAssociated, selected]
  · simp [Store.Holds, Equation.Holds, Roles.Term.subst]

theorem selected_impl_adds_ordinary_equation (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (goal : Roles.Goal) (name slot : Nat)
    (resolved : Roles.resolve env.cores wf goal = .resolved)
    (impl : Roles.AssocImpl) (member : impl ∈ env.impls)
    (unique : Roles.candidates env.cores goal = [impl.impl])
    (value : Roles.Term) (body : Roles.assocValue impl (roles goal.role) goal name = some value)
    (store : Store) :
    addAssociated env roles wf goal name slot store = some (⟨.var slot, value⟩ :: store) := by
  simp only [addAssociated,
    Roles.assoc_independent_of_constraints env roles wf goal name resolved impl member unique, body]
  rfl

theorem two_associated_equations_commute (σ : Roles.Subst) (store : Store)
    (left right : Roles.Term) (x y : Nat) :
    Store.Holds σ (⟨.var x, left⟩ :: ⟨.var y, right⟩ :: store) ↔
      Store.Holds σ (⟨.var y, right⟩ :: ⟨.var x, left⟩ :: store) := Store.add_comm ..

namespace AssocExamples

open Roles.AssocExamples
open Roles.Examples

/-- Prior constraints may agree with the selected char result. -/
theorem matching_constraint_accepts :
    Store.check (fun _ => char) [⟨.var 9, char⟩, ⟨.var 9, char⟩] = true := by
  decide

/-- A prior demand for str cannot be overwritten by the later char equation. -/
theorem conflicting_constraint_rejects (σ : Roles.Subst) :
    ¬ Store.Holds σ [⟨.var 9, char⟩, ⟨.var 9, str⟩] := by
  intro h
  have hc := h ⟨.var 9, char⟩ (by simp)
  have hs := h ⟨.var 9, str⟩ (by simp)
  have impossible := hc.symm.trans hs
  simp [Roles.Term.subst, char, str, Roles.substArgs] at impossible

end AssocExamples
end Yulang.RoleConstraints
