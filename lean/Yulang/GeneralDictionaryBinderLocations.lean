import Yulang.GeneralDictionaryOutputBinderTerms

/-!
# Computing local ordinary terms from actual source output binders

Source-slot lookup uses the state's injective source map, not a supplied term
interpretation. Every output is compiled; any unsupported or unlocated output
keeps the whole package deferred. Supplied input/head/target locations remain
explicit, and no global source ID is mistaken for a local slot number.
-/
namespace Yulang.GeneralDictionaryBinderLocations
open GeneralDeclarations GeneralDeclarationDemands
open GeneralSourceState (State Demand Assignment Models)
open GeneralDictionaryStateEquations
open GeneralDictionaryOutputBinderTerms (Interpreted)
open Core.PresenceGeneration (TyTerm)
variable {roles : Roles.RoleDecls} {state : State} {demand : Demand roles}

def sourceSlot (state : State) (source : Nat) : Option (Fin state.slots) :=
  (List.finRange state.slots).find? (fun slot => state.source slot == source)

theorem sourceSlot_exact (state : State) (source : Nat) (slot : Fin state.slots) :
    sourceSlot state source = some slot ↔ state.source slot = source := by
  constructor
  · intro found
    simpa using List.find?_some found
  · intro same
    cases found : sourceSlot state source with
    | none =>
      have absent := List.find?_eq_none.mp found slot (List.mem_finRange slot)
      simp [same] at absent
    | some other =>
      have equal : state.source other = source := by simpa using List.find?_some found
      have slots := state.source_injective (equal.trans same.symm)
      subst other
      rfl

def locateTerm (state : State) : TyTerm Nat → Option (TyTerm (Fin state.slots))
  | .var source => (sourceSlot state source).map TyTerm.var
  | _ => none

theorem locateTerm_lifts (state : State) (source : TyTerm Nat) (localTerm : TyTerm (Fin state.slots))
    (found : locateTerm state source = some localTerm) : liftType state localTerm = source := by
  cases source <;> simp only [locateTerm] at found
  all_goals try { cases found }
  next source =>
    obtain ⟨slot, present, rfl⟩ := Option.map_eq_some_iff.mp found
    have same := (sourceSlot_exact state source slot).mp present
    change TyTerm.var (state.source slot) = .var source
    rw [same]

def compile (state : State) (roles : Roles.RoleDecls) (declaration : Declaration)
    (capture : Capture) (name : Nat) : Option (TyTerm (Fin state.slots)) :=
  (GeneralDictionaryOutputBinderTerms.lookup roles declaration capture name).bind (locateTerm state)

theorem compile_interpreted (state : State) (roles : Roles.RoleDecls) (declaration : Declaration)
    (capture : Capture) (name : Nat) (term : TyTerm (Fin state.slots))
    (found : compile state roles declaration capture name = some term) :
    GeneralDictionaryOutputBinderTerms.lookup roles declaration capture name = some (liftType state term) := by
  obtain ⟨source, original, localized⟩ := Option.bind_eq_some_iff.mp found
  rw [locateTerm_lifts state source term localized]
  exact original

/-- Completeness for every located explicit source variable. Source identity is
checked against the actual state map rather than assumed equal to a slot number. -/
theorem compile_source_complete (state : State) (roles : Roles.RoleDecls) (declaration : Declaration)
    (capture : Capture) (name : Nat) (slot : Fin state.slots)
    (found : GeneralDictionaryOutputBinderTerms.lookup roles declaration capture name =
      some (.var (state.source slot))) :
    compile state roles declaration capture name = some (.var slot) := by
  simp only [compile, found, Option.bind_some, locateTerm]
  rw [(sourceSlot_exact state (state.source slot) slot).mpr rfl]
  rfl

/-- Complete lookup/localization iff for each local slot and actual RHS. -/
theorem compile_slot_exact (state : State) (roles : Roles.RoleDecls) (declaration : Declaration)
    (capture : Capture) (unique : (declaration.associated.map Equation.name).Nodup)
    (name : Nat) (slot : Fin state.slots) :
    compile state roles declaration capture name = some (.var slot) ↔
      GeneralDictionaryOutputBinderTerms.Denotes roles declaration capture name (.var (state.source slot)) := by
  constructor
  · intro found
    exact (GeneralDictionaryOutputBinderTerms.lookup_exact roles declaration capture unique name _).mp
      (compile_interpreted state roles declaration capture name (.var slot) found)
  · intro denoted
    exact compile_source_complete state roles declaration capture name slot
      ((GeneralDictionaryOutputBinderTerms.lookup_exact roles declaration capture unique name _).mpr denoted)

/-- No output terms or output interpretation proof is a field of this input. -/
structure Inputs (state : State) (demand : Demand roles) where
  lower : Fin (roles demand.role).arity → Fin state.slots
  upper : Fin (roles demand.role).arity → Fin state.slots
  head : Fin (roles demand.role).arity → TyTerm (Fin state.slots)
  target : Fin demand.outputs.length → Fin state.slots
  arguments : ∀ index, demand.arguments index = (state.source (lower index), state.source (upper index))
  targets : ∀ index, (demand.outputs[index]).target = state.source (target index)

/-- All finite output occurrences must compile. A failed output is not dropped. -/
def build (declaration : Declaration) (capture : Capture) (inputs : Inputs state demand) :
    Option (Located state demand) :=
  if complete : ∀ index : Fin demand.outputs.length,
      (compile state roles declaration capture (demand.outputs[index]).name).isSome = true then
    some { lower := inputs.lower
           upper := inputs.upper
           head := inputs.head
           target := inputs.target
           arguments := inputs.arguments
           targets := inputs.targets
           output := fun index => (compile state roles declaration capture (demand.outputs[index]).name).get (complete index) }
  else none

theorem build_interpreted (declaration : Declaration) (capture : Capture)
    (inputs : Inputs state demand) (located : Located state demand)
    (built : build declaration capture inputs = some located) : Interpreted declaration capture located := by
  unfold build at built
  split at built
  next complete =>
    cases built
    intro index
    apply compile_interpreted
    exact (Option.some_get (complete index)).symm
  next incomplete => cases built

/-- The actual compiled package supplies RHS provenance and all-model output
meaning, without any caller-supplied output vector or interpretation predicate. -/
theorem built_output_denotes (declaration : Declaration) (capture : Capture)
    (unique : (declaration.associated.map Equation.name).Nodup)
    (inputs : Inputs state demand) (located : Located state demand)
    (built : build declaration capture inputs = some located)
    (assignment : Assignment) (model : Models (GeneralDictionaryEquationRecording.record located) assignment)
    (index : Fin demand.outputs.length) :
    GeneralDictionaryOutputBinderTerms.Denotes roles declaration capture
      (demand.outputs[index]).name (located.equations.output index) ∧
      Common.Equivalent (assignment (demand.outputs[index]).target).1
        ((located.equations.output index).eval Common.model assignment) :=
  GeneralDictionaryOutputBinderTerms.recorded_output_denotes declaration capture unique located
    (build_interpreted declaration capture inputs located built) assignment model index

end Yulang.GeneralDictionaryBinderLocations
