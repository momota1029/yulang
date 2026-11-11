import Yulang.GeneralDictionaryVariableHeads

/-!
# Computing every demand endpoint and output-target location

Only the injective state source map is used. All unnamed endpoints and every
output occurrence are retained, including repeated targets. Missing source
identities defer the entire localization; no allocation or interval midpoint
is invented. Localization does not inspect heads or select a candidate.
-/
namespace Yulang.GeneralDictionaryHeadlessLocations
open GeneralSourceState (State Demand Linked)
open GeneralDictionaryVariableHeads (HeadlessInputs)
open GeneralDictionaryBinderLocations (sourceSlot sourceSlot_exact)
variable {roles : Roles.RoleDecls} {state : State} {demand : Demand roles}

/-- Source membership alone, independently of any executable search. -/
def Available (state : State) (demand : Demand roles) : Prop :=
  (∀ index, ∃ slot, state.source slot = (demand.arguments index).1) ∧
  (∀ index, ∃ slot, state.source slot = (demand.arguments index).2) ∧
  (∀ index : Fin demand.outputs.length, ∃ slot, state.source slot = (demand.outputs[index]).target)

private theorem get_source (state : State) (source : Nat)
    (present : (sourceSlot state source).isSome = true) :
    state.source ((sourceSlot state source).get present) = source :=
  (sourceSlot_exact state source _).mp (Option.some_get present).symm

/-- Endpoint and target slot vectors are computed, never supplied by the caller. -/
def locate (state : State) (demand : Demand roles) : Option (HeadlessInputs state demand) :=
  if complete :
      (∀ index, (sourceSlot state (demand.arguments index).1).isSome = true) ∧
      (∀ index, (sourceSlot state (demand.arguments index).2).isSome = true) ∧
      (∀ index : Fin demand.outputs.length,
        (sourceSlot state (demand.outputs[index]).target).isSome = true) then
    some {
      lower := fun index => (sourceSlot state (demand.arguments index).1).get (complete.1 index)
      upper := fun index => (sourceSlot state (demand.arguments index).2).get (complete.2.1 index)
      target := fun index => (sourceSlot state (demand.outputs[index]).target).get (complete.2.2 index)
      arguments := fun index => Prod.ext (get_source state _ (complete.1 index)).symm
        (get_source state _ (complete.2.1 index)).symm
      targets := fun index => (get_source state _ (complete.2.2 index)).symm }
  else none

/-- Injectivity makes the entire proof-carrying input package unique. -/
theorem inputs_unique (first last : HeadlessInputs state demand) : first = last := by
  have lower : first.lower = last.lower := by
    funext index
    apply state.source_injective
    exact (congrArg Prod.fst (first.arguments index)).symm.trans
      (congrArg Prod.fst (last.arguments index))
  have upper : first.upper = last.upper := by
    funext index
    apply state.source_injective
    exact (congrArg Prod.snd (first.arguments index)).symm.trans
      (congrArg Prod.snd (last.arguments index))
  have target : first.target = last.target := by
    funext index
    exact state.source_injective ((first.targets index).symm.trans (last.targets index))
  cases first
  cases last
  simp_all

theorem inputs_available (inputs : HeadlessInputs state demand) : Available state demand := by
  exact ⟨fun index => ⟨inputs.lower index, (congrArg Prod.fst (inputs.arguments index)).symm⟩,
    fun index => ⟨inputs.upper index, (congrArg Prod.snd (inputs.arguments index)).symm⟩,
    fun index => ⟨inputs.target index, (inputs.targets index).symm⟩⟩

/-- Exact domain characterization. This relation contains no lookup premise. -/
theorem locate_success_iff (state : State) (demand : Demand roles) :
    (∃ inputs, locate state demand = some inputs) ↔ Available state demand := by
  constructor
  · rintro ⟨inputs, _⟩
    exact inputs_available inputs
  · intro available
    have lower : ∀ index, (sourceSlot state (demand.arguments index).1).isSome = true := by
      intro index
      obtain ⟨slot, source⟩ := available.1 index
      rw [(sourceSlot_exact state _ slot).mpr source]
      rfl
    have upper : ∀ index, (sourceSlot state (demand.arguments index).2).isSome = true := by
      intro index
      obtain ⟨slot, source⟩ := available.2.1 index
      rw [(sourceSlot_exact state _ slot).mpr source]
      rfl
    have target : ∀ index : Fin demand.outputs.length,
        (sourceSlot state (demand.outputs[index]).target).isSome = true := by
      intro index
      obtain ⟨slot, source⟩ := available.2.2 index
      rw [(sourceSlot_exact state _ slot).mpr source]
      rfl
    unfold locate
    rw [dite_eq_left ⟨lower, upper, target⟩]
    exact ⟨_, rfl⟩

/-- Every formerly supplied valid package is exactly the computed package. -/
theorem locate_inputs (inputs : HeadlessInputs state demand) : locate state demand = some inputs := by
  obtain ⟨computed, found⟩ := (locate_success_iff state demand).mpr (inputs_available inputs)
  rw [inputs_unique computed inputs] at found
  exact found

theorem locate_none_iff (state : State) (demand : Demand roles) :
    locate state demand = none ↔ ¬ Available state demand := by
  constructor
  · intro absent available
    obtain ⟨inputs, found⟩ := (locate_success_iff state demand).mpr available
    rw [absent] at found
    cases found
  · intro absent
    cases found : locate state demand with
    | none => rfl
    | some inputs => exact False.elim (absent (inputs_available inputs))

/-- Linked additionally records interval membership; localization requires only
the weaker source membership that follows from it. -/
theorem linked_available (linked : Linked state demand) : Available state demand := by
  refine ⟨?_, ?_, ?_⟩
  · intro index
    obtain ⟨pair, _, endpoints⟩ := linked.1 index
    exact ⟨pair.1, congrArg Prod.fst endpoints⟩
  · intro index
    obtain ⟨pair, _, endpoints⟩ := linked.1 index
    exact ⟨pair.2, congrArg Prod.snd endpoints⟩
  · intro index
    exact linked.2 (demand.outputs[index]) (List.getElem_mem index.isLt)

theorem locate_linked (linked : Linked state demand) :
    ∃ inputs, locate state demand = some inputs :=
  (locate_success_iff state demand).mpr (linked_available linked)

end Yulang.GeneralDictionaryHeadlessLocations
