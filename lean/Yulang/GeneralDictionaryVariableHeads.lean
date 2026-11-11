import Yulang.GeneralDictionaryVariablePlans
import Yulang.GeneralDictionaryVariableRealization

/-!
# Partial head materialization from exact captured input variables

No head vector is supplied. Each actual positional head pattern must normalize
to an input variable with identical captured endpoint identities, present in
the state's source map. Compound heads and unequal intervals remain deferred.
This does not discover or validate the capture as a candidate head match.
-/
namespace Yulang.GeneralDictionaryVariableHeads
open GeneralDeclarations GeneralDeclarationPatterns GeneralDeclarationDemands
open GeneralDictionaryStateEquations
open GeneralDictionaryBinderLocations (Inputs sourceSlot sourceSlot_exact)
open GeneralSourceState (State Demand Assignment)
open Core.PresenceGeneration (TyTerm)
variable {roles : Roles.RoleDecls} {state : State} {demand : Demand roles}

structure HeadlessInputs (state : State) (demand : Demand roles) where
  lower : Fin (roles demand.role).arity → Fin state.slots
  upper : Fin (roles demand.role).arity → Fin state.slots
  target : Fin demand.outputs.length → Fin state.slots
  arguments : ∀ index, demand.arguments index = (state.source (lower index), state.source (upper index))
  targets : ∀ index, (demand.outputs[index]).target = state.source (target index)

/-- Independent positional provenance and exact localization. -/
def DenotesAt (state : State) (declaration : Declaration) (capture : Capture)
    (index : Nat) (term : TyTerm (Fin state.slots)) : Prop :=
  ∃ pattern binder slot, declaration.head[index]? = some pattern ∧
    normalize pattern = .var binder ∧ binder ∈ declaration.inputNames ∧
    (capture.inputs binder).1 = (capture.inputs binder).2 ∧
    state.source slot = (capture.inputs binder).1 ∧ term = .var slot

def compileAt (state : State) (declaration : Declaration) (capture : Capture)
    (index : Nat) : Option (TyTerm (Fin state.slots)) :=
  declaration.head[index]?.bind fun pattern =>
    match normalize pattern with
    | .var binder =>
      if binder ∈ declaration.inputNames ∧
          (capture.inputs binder).1 = (capture.inputs binder).2 then
        (sourceSlot state (capture.inputs binder).1).map TyTerm.var
      else none
    | _ => none

theorem compileAt_exact (state : State) (declaration : Declaration) (capture : Capture)
    (index : Nat) (term : TyTerm (Fin state.slots)) :
    compileAt state declaration capture index = some term ↔
      DenotesAt state declaration capture index term := by
  unfold compileAt DenotesAt
  rw [Option.bind_eq_some_iff]
  constructor
  · rintro ⟨pattern, present, found⟩
    cases normalized : normalize pattern <;> simp only [normalized] at found
    all_goals try { cases found }
    next binder =>
      split at found
      next supported =>
        obtain ⟨slot, located, same⟩ := Option.map_eq_some_iff.mp found
        exact ⟨pattern, binder, slot, present, normalized, supported.1, supported.2,
          (sourceSlot_exact state _ slot).mp located, same.symm⟩
      next unsupported => cases found
  · rintro ⟨pattern, binder, slot, present, normalized, input, same, source, rfl⟩
    refine ⟨pattern, present, ?_⟩
    simp only [normalized]
    rw [ite_eq_left ⟨input, same⟩]
    rw [(sourceSlot_exact state _ slot).mpr source]
    rfl

def HeadDenotes (declaration : Declaration) (capture : Capture) (demand : Demand roles)
    (head : Fin (roles demand.role).arity → TyTerm (Fin state.slots)) : Prop :=
  declaration.role = demand.role ∧ declaration.head.length = (roles demand.role).arity ∧
    ∀ index, DenotesAt state declaration capture index.val (head index)

/-- Concrete head predicate for the existing whole-tree transaction interface. -/
def heads (roles : Roles.RoleDecls) (state : State) :
    GeneralDictionaryVariablePlans.HeadInstances roles state :=
  fun root declaration capture head => HeadDenotes declaration capture root.demand head

def build (declaration : Declaration) (_checked : DeclarationChecked constructors roles declaration)
    (_sameRole : declaration.role = demand.role) (capture : Capture)
    (inputs : HeadlessInputs state demand) : Option (Inputs state demand) :=
  if complete : ∀ index : Fin (roles demand.role).arity,
      (compileAt state declaration capture index.val).isSome = true then
    some { lower := inputs.lower
           upper := inputs.upper
           target := inputs.target
           arguments := inputs.arguments
           targets := inputs.targets
           head := fun index => (compileAt state declaration capture index.val).get (complete index) }
  else none

theorem build_head_denotes (declaration : Declaration)
    (checked : DeclarationChecked constructors roles declaration)
    (sameRole : declaration.role = demand.role) (capture : Capture)
    (inputs : HeadlessInputs state demand) (result : Inputs state demand)
    (built : build declaration checked sameRole capture inputs = some result) :
    HeadDenotes declaration capture demand result.head := by
  unfold build at built
  split at built
  next complete =>
    cases built
    refine ⟨sameRole, ?_, ?_⟩
    · rw [← sameRole]; exact checked.signature.1
    · intro index
      exact (compileAt_exact state declaration capture _ _).mp
        (Option.some_get (complete index)).symm
  next incomplete => cases built

theorem build_preserves (declaration : Declaration)
    (checked : DeclarationChecked constructors roles declaration)
    (sameRole : declaration.role = demand.role) (capture : Capture)
    (inputs : HeadlessInputs state demand) (result : Inputs state demand)
    (built : build declaration checked sameRole capture inputs = some result) :
    result.lower = inputs.lower ∧ result.upper = inputs.upper ∧ result.target = inputs.target := by
  unfold build at built
  split at built
  · cases built; exact ⟨rfl, rfl, rfl⟩
  · cases built

/-- Exactness for any supported concrete head vector and the retained locations. -/
theorem build_exact (declaration : Declaration)
    (checked : DeclarationChecked constructors roles declaration)
    (sameRole : declaration.role = demand.role) (capture : Capture)
    (inputs : HeadlessInputs state demand) (result : Inputs state demand) :
    build declaration checked sameRole capture inputs = some result ↔
      result.lower = inputs.lower ∧ result.upper = inputs.upper ∧ result.target = inputs.target ∧
        HeadDenotes declaration capture demand result.head := by
  constructor
  · intro built
    have preserved := build_preserves declaration checked sameRole capture inputs result built
    exact ⟨preserved.1, preserved.2.1, preserved.2.2,
      build_head_denotes declaration checked sameRole capture inputs result built⟩
  · rintro ⟨lower, upper, target, denoted⟩
    have compiled : ∀ index : Fin (roles demand.role).arity,
        compileAt state declaration capture index.val = some (result.head index) := by
      intro index
      exact (compileAt_exact state declaration capture _ _).mpr (denoted.2.2 index)
    have complete : ∀ index : Fin (roles demand.role).arity,
        (compileAt state declaration capture index.val).isSome = true := by
      intro index; rw [compiled index]; rfl
    unfold build
    rw [dite_eq_left complete]
    apply congrArg some
    have head : (fun index : Fin (roles demand.role).arity =>
        (compileAt state declaration capture index.val).get (complete index)) = result.head := by
      funext index
      simp only [compiled index, Option.get_some]
    cases inputs
    cases result
    simp_all

/-- Positional meaning is valid for every realization of the supplied capture. -/
theorem denotesAt_realization (declaration : Declaration) (capture : Capture)
    (assignment : Assignment) (values : Nat → Common.Ty)
    (realized : GeneralDictionaryVariableRealization.Realizes declaration capture assignment values)
    (index : Nat) (term : TyTerm (Fin state.slots))
    (denoted : DenotesAt state declaration capture index term) :
    ∃ pattern binder, declaration.head[index]? = some pattern ∧ normalize pattern = .var binder ∧
      Common.Equivalent (values binder) ((liftType state term).eval Common.model assignment) := by
  obtain ⟨pattern, binder, slot, present, normalized, input, same, source, rfl⟩ := denoted
  refine ⟨pattern, binder, present, normalized, ?_⟩
  change Common.Equivalent (values binder) (assignment (state.source slot)).1
  rw [source]
  exact GeneralDictionaryVariableRealization.singleton_value capture assignment binder
    (values binder) same (realized.1 binder input)

end Yulang.GeneralDictionaryVariableHeads
