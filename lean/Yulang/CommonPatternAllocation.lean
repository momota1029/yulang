import Yulang.CommonPatternGeneration

/-!
# A source-name allocator shared by patterns and their consumers

Every binder is allocated once from the actual written name list. Later
defaults and a future guard/body use these same references. The finite
existential closure below keeps the ambient slots free and distinct.
-/

namespace Yulang.CommonPatternAllocation

set_option backward.isDefEq.respectTransparency false

open Core.PresenceGeneration
open CommonPatternEnvironment
open CommonPatternGeneration
open CasePatterns (Pattern)

def Slots (α : Type) : Nat → Type
  | 0 => α
  | n + 1 => Option (Slots α n)

def ambient : (n : Nat) → α → Slots α n
  | 0, name => name
  | n + 1, name => some (ambient n name)

def assignment (ρ : α → Comp Common.model) :
    {n : Nat} → (Fin n → Comp Common.model) → Slots α n → Comp Common.model
  | 0, _ => ρ
  | _ + 1, values => extend (assignment ρ (fun i => values i.succ)) (values 0)

@[simp] theorem assignment_ambient (ρ : α → Comp Common.model)
    (values : Fin n → Comp Common.model) : assignment ρ values ∘ ambient n = ρ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext name
    exact congrFun (ih (fun i => values i.succ)) name

def close : (n : Nat) → Formula (Slots α n) → Formula α
  | 0, formula => formula
  | n + 1, formula => close n (.existsSlot formula)

/-- Finite binder closure is exact for every ambient assignment and every
formula; there is no satisfiability or successful-solver premise. -/
theorem close_exact (n : Nat) (formula : Formula (Slots α n))
    (ρ : α → Comp Common.model) :
    (close n formula).Holds Common.model ρ ↔
      ∃ values : Fin n → Comp Common.model, formula.Holds Common.model (assignment ρ values) := by
  induction n with
  | zero => exact ⟨fun held => ⟨Fin.elim0, held⟩, fun ⟨_, held⟩ => held⟩
  | succ n ih =>
    rw [close, ih]
    simp only [Formula.Holds]
    constructor
    · rintro ⟨tail, head, held⟩
      exact ⟨Fin.cases head tail, by simpa [assignment] using held⟩
    · rintro ⟨values, held⟩
      exact ⟨fun i => values i.succ, values 0, held⟩

def bindingSlots : (names : List Nat) → NamedTerms (Slots α names.length)
  | [] => []
  | name :: rest => (name, .var none) :: renameBindings some (bindingSlots rest)

def bindingValues : (names : List Nat) → (Fin names.length → Comp Common.model) → NamedTypes
  | [], _ => []
  | name :: rest, values =>
      (name, (values 0).1) :: bindingValues rest (fun i => values i.succ)

@[simp] theorem bindingSlots_eval (names : List Nat) (ρ : α → Comp Common.model)
    (values : Fin names.length → Comp Common.model) :
    evalTypes (assignment ρ values) (bindingSlots names) = bindingValues names values := by
  induction names with
  | nil => rfl
  | cons name rest ih =>
      simpa [bindingSlots, bindingValues, evalTypes, assignment, TyTerm.eval, renameBindings, List.map_map,
        Function.comp_def] using congrArg (List.cons (name, (values 0).1))
          (ih (fun i => values i.succ))

@[simp] theorem bindingValues_names (names : List Nat)
    (values : Fin names.length → Comp Common.model) :
    (bindingValues names values).map Prod.fst = names := by
  induction names with
  | nil => rfl
  | cons name rest ih => simp [bindingValues, ih]

/-- Any ordered binding list with these source names is recovered literally,
including all repeated references or equal types; no type is freshened. -/
theorem bindingValues_complete (names : List Nat) (bindings : NamedTypes)
    (same : bindings.map Prod.fst = names) :
    ∃ values : Fin names.length → Comp Common.model, bindingValues names values = bindings := by
  induction names generalizing bindings with
  | nil =>
      have empty : bindings = [] := List.map_eq_nil_iff.mp same
      subst bindings
      exact ⟨Fin.elim0, rfl⟩
  | cons name rest ih =>
      cases bindings with
      | nil => cases same
      | cons binding tail =>
          rcases binding with ⟨actual, type⟩
          have parts := List.cons.inj same
          have nameEq : actual = name := parts.1
          subst actual
          obtain ⟨values, equal⟩ := ih tail parts.2
          exact ⟨Fin.cases (Comp.pure Common.model type) values,
            by simpa [bindingValues, Comp.pure] using congrArg (List.cons (name, type)) equal⟩

def constraints (pattern : Pattern Empty Inference.Expr) (environment : SchemeEnv α)
    (priorBindings : NamedTerms α) (input : TyTerm α) : Formula (Slots α pattern.names.length) :=
  generatePattern pattern (environment.rename (ambient pattern.names.length))
    (renameBindings (ambient pattern.names.length) priorBindings)
    (input.rename (ambient pattern.names.length)) (bindingSlots pattern.names)

def generateAllocatedPattern (pattern : Pattern Empty Inference.Expr) (environment : SchemeEnv α)
    (priorBindings : NamedTerms α) (input : TyTerm α) : Formula α :=
  close pattern.names.length (constraints pattern environment priorBindings input)

theorem constraints_exact (pattern : Pattern Empty Inference.Expr)
    (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (semantic : List (Binding Common.model)) (outer : EnvRel Common.model ρ symbolic semantic)
    (priorBindings : NamedTerms α) (input : TyTerm α)
    (values : Fin pattern.names.length → Comp Common.model) :
    (constraints pattern symbolic priorBindings input).Holds Common.model (assignment ρ values) ↔
      CommonPatternTyping.Typing (DefaultTyping semantic) (evalTypes ρ priorBindings) pattern
        (input.eval Common.model ρ) (bindingValues pattern.names values) := by
  simpa only [constraints, evalTypes_rename, TyTerm.eval_rename, assignment_ambient,
    bindingSlots_eval] using
      generatePattern_exact pattern (assignment ρ values)
        (symbolic.rename (ambient pattern.names.length)) semantic
        (outer.rename _ _ (assignment_ambient ρ values))
        (renameBindings (ambient pattern.names.length) priorBindings)
        (input.rename (ambient pattern.names.length)) (bindingSlots pattern.names)

/-- The actual source traversal allocates every output binder jointly, for
arbitrary source patterns, captured environments, subject types, and free
ambient assignments. The independent judgment retains its stated boundaries. -/
theorem generateAllocatedPattern_exact (pattern : Pattern Empty Inference.Expr)
    (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (semantic : List (Binding Common.model)) (outer : EnvRel Common.model ρ symbolic semantic)
    (priorBindings : NamedTerms α) (input : TyTerm α) :
    (generateAllocatedPattern pattern symbolic priorBindings input).Holds Common.model ρ ↔
      ∃ bindings, CommonPatternTyping.Typing (DefaultTyping semantic) (evalTypes ρ priorBindings)
        pattern (input.eval Common.model ρ) bindings := by
  simp only [generateAllocatedPattern, close_exact,
    constraints_exact pattern ρ symbolic semantic outer priorBindings input]
  constructor
  · rintro ⟨values, typed⟩; exact ⟨_, typed⟩
  · rintro ⟨bindings, typed⟩
    obtain ⟨values, same⟩ := bindingValues_complete pattern.names bindings typed.binding_names.symm
    exact ⟨values, by simpa only [same] using typed⟩

/-- Completeness recovers an arbitrarily prescribed independent result list
literally, rather than merely choosing some successful output environment. -/
theorem allocated_bindings_exact (pattern : Pattern Empty Inference.Expr)
    (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (semantic : List (Binding Common.model)) (outer : EnvRel Common.model ρ symbolic semantic)
    (priorBindings : NamedTerms α) (input : TyTerm α) (bindings : NamedTypes) :
    (∃ values : Fin pattern.names.length → Comp Common.model,
      (constraints pattern symbolic priorBindings input).Holds Common.model (assignment ρ values) ∧
        bindingValues pattern.names values = bindings) ↔
      CommonPatternTyping.Typing (DefaultTyping semantic) (evalTypes ρ priorBindings)
        pattern (input.eval Common.model ρ) bindings := by
  simp only [constraints_exact pattern ρ symbolic semantic outer priorBindings input]
  constructor
  · rintro ⟨values, typed, same⟩; exact same ▸ typed
  · intro typed
    obtain ⟨values, same⟩ := bindingValues_complete pattern.names bindings typed.binding_names.symm
    exact ⟨values, same.symm ▸ typed, same⟩

/-- A consumer is inserted inside the same binder scope. In particular a guard
or body cannot accidentally receive an independently chosen output list. -/
def withPattern (pattern : Pattern Empty Inference.Expr) (environment : SchemeEnv α)
    (priorBindings : NamedTerms α) (input : TyTerm α)
    (consumer : Formula (Slots α pattern.names.length)) : Formula α :=
  close pattern.names.length (.and (constraints pattern environment priorBindings input) consumer)

theorem withPattern_exact (pattern : Pattern Empty Inference.Expr)
    (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (semantic : List (Binding Common.model)) (outer : EnvRel Common.model ρ symbolic semantic)
    (priorBindings : NamedTerms α) (input : TyTerm α)
    (consumer : Formula (Slots α pattern.names.length)) :
    (withPattern pattern symbolic priorBindings input consumer).Holds Common.model ρ ↔
      ∃ values : Fin pattern.names.length → Comp Common.model,
        CommonPatternTyping.Typing (DefaultTyping semantic) (evalTypes ρ priorBindings)
          pattern (input.eval Common.model ρ) (bindingValues pattern.names values) ∧
        consumer.Holds Common.model (assignment ρ values) := by
  simp only [withPattern, close_exact, Formula.Holds,
    constraints_exact pattern ρ symbolic semantic outer priorBindings input]

end Yulang.CommonPatternAllocation
