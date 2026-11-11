import Yulang.GeneralDictionaryVariablePlans

/-!
# Independent exactness of complete variable-output materialization

The independent package relation fixes all supplied non-output fields and
requires actual RHS denotation at every output occurrence. It contains no
lookup/build-success premise. Exactness preserves repeated targets and every
source identity, while keeping the head and capture inputs explicit.
-/
namespace Yulang.GeneralDictionaryVariableMaterialization
open GeneralDeclarations GeneralDeclarationDemands GeneralSourceDictionaries
open GeneralSourceState (State Demand)
open GeneralDictionaryStateEquations
open GeneralDictionaryBinderLocations (Inputs sourceSlot sourceSlot_exact locateTerm)
open GeneralDictionaryVariableTerms (Denotes lookup compile build)
open GeneralDictionaryEmissionPlans
open Core.PresenceGeneration (TyTerm)
variable {roles : Roles.RoleDecls} {state : State} {demand : Demand roles}

theorem compile_slot_exact (roles : Roles.RoleDecls) (state : State)
    (declaration : Declaration) (capture : Capture)
    (unique : (declaration.associated.map Equation.name).Nodup) (name : Nat)
    (slot : Fin state.slots) :
    compile state roles declaration capture name = some (.var slot) ↔
      Denotes roles declaration capture name (.var (state.source slot)) := by
  constructor
  · intro found
    exact (GeneralDictionaryVariableTerms.lookup_exact roles declaration capture unique name _).mp
      (GeneralDictionaryVariableTerms.compile_interpreted state roles declaration capture name _ found)
  · intro denoted
    have found := (GeneralDictionaryVariableTerms.lookup_exact roles declaration capture unique name _).mpr denoted
    simp only [compile, found, Option.bind_some, locateTerm]
    rw [(sourceSlot_exact state (state.source slot) slot).mpr rfl]
    rfl

/-- The current compiler produces a located source variable, not a chosen
constructor interpretation or an invented interval midpoint. -/
theorem compile_variable (roles : Roles.RoleDecls) (state : State)
    (declaration : Declaration) (capture : Capture) (name : Nat)
    (term : TyTerm (Fin state.slots))
    (found : compile state roles declaration capture name = some term) :
    ∃ slot, term = .var slot := by
  obtain ⟨source, _, located⟩ := Option.bind_eq_some_iff.mp found
  cases source <;> simp only [locateTerm] at located
  all_goals try { cases located }
  next source =>
    obtain ⟨slot, _, same⟩ := Option.map_eq_some_iff.mp located
    exact ⟨slot, same.symm⟩

def Matches (inputs : Inputs state demand) (located : Located state demand) : Prop :=
  located.lower = inputs.lower ∧ located.upper = inputs.upper ∧
    located.head = inputs.head ∧ located.target = inputs.target

/-- Independent membership/provenance and source-map equality at every output.
No executable success fact is hidden in this relation. -/
def Materializes (declaration : Declaration) (capture : Capture)
    (inputs : Inputs state demand) (located : Located state demand) : Prop :=
  Matches inputs located ∧ ∀ index, ∃ slot,
    located.output index = .var slot ∧
    Denotes roles declaration capture (demand.outputs[index]).name (.var (state.source slot))

private theorem located_ext (first last : Located state demand)
    (lower : first.lower = last.lower) (upper : first.upper = last.upper)
    (head : first.head = last.head) (target : first.target = last.target)
    (output : first.output = last.output) : first = last := by
  cases first
  cases last
  simp_all

/-- Exact iff for arbitrary finite output lists, including repeated names.
Only actual supported RHS denotation and source locations enter the right side. -/
theorem build_exact (declaration : Declaration) (capture : Capture)
    (unique : (declaration.associated.map Equation.name).Nodup)
    (inputs : Inputs state demand) (located : Located state demand) :
    build declaration capture inputs = some located ↔ Materializes declaration capture inputs located := by
  constructor
  · intro built
    unfold build at built
    split at built
    next complete =>
      cases built
      refine ⟨⟨rfl, rfl, rfl, rfl⟩, ?_⟩
      intro index
      have found := (Option.some_get (complete index)).symm
      obtain ⟨slot, same⟩ := compile_variable roles state declaration capture _ _ found
      refine ⟨slot, same, ?_⟩
      rw [same] at found
      exact (compile_slot_exact roles state declaration capture unique _ slot).mp found
    next incomplete => cases built
  · rintro ⟨sameInputs, outputs⟩
    have compiled : ∀ index,
        compile state roles declaration capture (demand.outputs[index]).name = some (located.output index) := by
      intro index
      obtain ⟨slot, same, denoted⟩ := outputs index
      rw [same]
      exact (compile_slot_exact roles state declaration capture unique _ slot).mpr denoted
    have complete : ∀ index : Fin demand.outputs.length,
        (compile state roles declaration capture (demand.outputs[index]).name).isSome = true := by
      intro index
      rw [compiled index]
      rfl
    unfold build
    rw [dite_eq_left complete]
    apply congrArg some
    apply located_ext
    · exact sameInputs.1.symm
    · exact sameInputs.2.1.symm
    · exact sameInputs.2.2.1.symm
    · exact sameInputs.2.2.2.symm
    · funext index
      simp only [compiled index, Option.get_some]

/-- Missing support or source location is partial materialization failure, not
a proof that the source role demand must be rejected. -/
theorem build_none_exact (declaration : Declaration) (capture : Capture)
    (unique : (declaration.associated.map Equation.name).Nodup)
    (inputs : Inputs state demand) :
    build declaration capture inputs = none ↔
      ∀ located, ¬ Materializes declaration capture inputs located := by
  constructor
  · intro absent located materialized
    have found := (build_exact declaration capture unique inputs located).mpr materialized
    rw [absent] at found
    cases found
  · intro absent
    cases found : build declaration capture inputs with
    | none => rfl
    | some located => exact False.elim (absent located
        ((build_exact declaration capture unique inputs located).mp found))

/-- Same checked visible declaration, canonical children and independent package
materialization characterize the complete registry operation. -/
theorem plan_lookup_exact (registry : Registry) (checked : Checked registry)
    (frame : Frame registry.roles) (root : Occurrence registry.roles) (key : Nat)
    (inputs : Inputs state root.demand) (result : GeneralDictionaryVariablePlans.Result state root) :
    GeneralDictionaryVariablePlans.lookup registry checked frame root key inputs = some result ↔
      ∃ declaration, ∃ present : declaration ∈ registry.declarations,
        declaration.id = key ∧ declaration.role = root.demand.role ∧
        Materializes declaration (frame.capture declaration.id) inputs result.located ∧
        result.children = children frame root declaration (checked.2 declaration present) := by
  rw [GeneralDictionaryVariablePlans.lookup_exact]
  constructor
  · rintro ⟨declaration, present, key, role, built, children⟩
    exact ⟨declaration, present, key, role,
      (build_exact declaration _ (checked.2 declaration present).identified.2.2.1 inputs _).mp built, children⟩
  · rintro ⟨declaration, present, key, role, materialized, children⟩
    exact ⟨declaration, present, key, role,
      (build_exact declaration _ (checked.2 declaration present).identified.2.2.1 inputs _).mpr materialized, children⟩

end Yulang.GeneralDictionaryVariableMaterialization
