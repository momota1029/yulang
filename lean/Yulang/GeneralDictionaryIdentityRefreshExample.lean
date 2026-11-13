import Yulang.GeneralDictionaryIdentityEvidenceExample
noncomputable section
/-! A concrete exact Shared refresh learns the installed identity output is int.
Its source base changes, so ordinary-extension transport does not apply. -/
namespace Yulang.GeneralDictionaryIdentityRefreshExample
open GeneralNominalIdentityExample GeneralNominalSaturationState
open GeneralDictionaryIdentityEvidenceExample CommonNominalFullCarrier
local instance : NeZero finish.current.context.state.base.slots := ⟨by change 2 ≠ 0; decide⟩

abbrev nextBase : GeneralSourceState.State where
  slots := 2
  source := Fin.val
  source_injective := fun _ _ equal => Fin.ext equal
  rowSource := Fin.val
  ordinary := GeneralSourceState.equationAtoms 0 (.base .int) ++
    GeneralSourceState.equationAtoms 1 (.base .int)
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  heads := fun _ => .scalar .int
  intervals := []
  heads_sound := by
    intro assignment valid slot term recorded
    cases Option.some.inj recorded
    have zero := (GeneralSourceState.equationAtoms_exact 0 (.base .int) assignment).mp
      (fun atom member => valid atom (List.mem_append_left _ member))
    have one := (GeneralSourceState.equationAtoms_exact 1 (.base .int) assignment).mp
      (fun atom member => valid atom (List.mem_append_right _ member))
    have cases : slot = 0 ∨ slot = 1 := by by_cases h : slot = 0; exact Or.inl h; right; apply Fin.ext; have := slot.isLt; have : slot.val ≠ 0 := fun eq => h (Fin.ext eq); omega
    rcases cases with rfl|rfl
    · exact zero
    · exact one
  intervals_sound := by intro _ _ _ impossible; cases impossible

abbrev nextView : GeneralNormalizedObservation.Snapshot nextBase where
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  canonical := by intro i; exact Fin.elim0 i
  heads := fun _ => .scalar .int
  checked := by intro slot term recorded; cases Option.some.inj recorded; exact .head rfl

abbrev nextState : GeneralNominalState.State where
  base := nextBase
  view := nextView
  constructors := constructors
  nominals := fun _ => none
  catalogue := by intro _ _ impossible; cases impossible
  bodies_opaque := by intro _ _ impossible; cases impossible
  seed := finish.current.context.state.seed
  allocated := finish.current.context.state.allocated
  reserved := finish.current.context.state.reserved
  ordinary := finish.current.context.state.ordinary
abbrev nextContext : GeneralNominalCandidates.Context := ⟨nextState,interpretation⟩

noncomputable def refines : GeneralNominalRefinements.Refines finish.current.context.state nextState where
  base := ⟨id,(by intro _; rfl),(by intro _; rfl),
    (by
      change ∀ atom ∈ base.ordinary, atom.rename (id : Fin 2 → Fin 2) ∈ nextBase.ordinary
      intro atom member
      simp only [base,GeneralSourceState.equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl <;> decide +kernel),
    (by intro _ _; simp [GeneralSourceState.State.graph,GeneralSourceState.Head.node]),
    (by intro _ impossible; cases impossible)⟩
  heads := by
    intro slot term recorded
    change (if slot = 0 then GeneralSourceState.Head.scalar .int else .unresolved).equation = some term at recorded
    split at recorded
    · cases Option.some.inj recorded
      exact .head rfl
    · cases recorded
  nominals := by intro _ _ impossible; cases impossible
  ordinary := fun _ member => member
  known := by
    intro identity known
    obtain ⟨slot,same,_⟩ := known
    exact ⟨slot,same,Or.inl (by simp [GeneralNormalizedObservation.Snapshot.graph,GeneralNormalizedObservation.Head.node])⟩
  reserved := fun _ member => member
  allocated := fun _ member => member
  seed := rfl
  constructors := rfl
theorem refreshed_raw (m : GeneralNominalCommonBridge.Assignment) (valid : Models finish.current m) :
    GeneralNominalState.Models nextState m := by
  have zero : Equivalent (m 0).1 (.base .int) := valid.1.1.2.1 0 (.base .int) rfl
  have alias := installed_alias m valid
  have one : Equivalent (m 1).1 (.base .int) :=
    ⟨subtype_trans alias.1 zero.1,subtype_trans zero.2 alias.2⟩
  refine ⟨⟨?_,?_,?_⟩,?_,valid.1.2.2⟩
  · intro atom member
    change atom ∈ GeneralSourceState.equationAtoms (0 : Fin 2) (.base .int) ++
      GeneralSourceState.equationAtoms 1 (.base .int) at member
    simp only [GeneralSourceState.equationAtoms,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with (rfl|rfl)|(rfl|rfl)
    · exact zero.1
    · exact zero.2
    · exact one.1
    · exact one.2
  · intro slot term recorded
    cases Option.some.inj recorded
    change Fin 2 at slot
    have cases : slot = 0 ∨ slot = 1 := by
      by_cases h : slot = 0
      · exact Or.inl h
      · right; apply Fin.ext; have := slot.isLt
        have : slot.val ≠ 0 := fun eq => h (Fin.ext eq)
        omega
    rcases cases with rfl|rfl
    · exact zero
    · exact one
  · intro pair impossible; cases impossible
  · intro slot descriptor impossible; cases impossible

noncomputable def certificate : GeneralNominalFeedbackSteps.Refresh finish.current nextContext where
  refines := refines
  interpretation := rfl
  exact := refreshed_raw
  support := by
    intro identity member
    exact member

noncomputable def refreshed : GeneralNominalSupport.Tracked roles :=
  {finish with current := regenerate finish.current nextContext}

theorem old_unknown : ¬ GeneralNominalState.Known finish.current.context.state 1 := by
  rintro ⟨slot,eq,head|⟨descriptor,recorded⟩⟩
  · have same : slot = (1 : Fin 2) := Fin.ext eq
    subst slot
    exact head rfl
  · cases recorded

theorem new_known : GeneralNominalState.Known nextState 1 :=
  ⟨1,rfl,Or.inl (by simp [GeneralNormalizedObservation.Snapshot.graph,GeneralNormalizedObservation.Head.node])⟩

theorem refresh_step : GeneralNominalSharedSteps.Step registry root finish refreshed := by
  refine ⟨root,.root,.administrative root _ (.refresh root nextContext certificate 1 ?_ old_unknown new_known)⟩
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨(1 : Fin 2),rfl⟩)))

theorem refreshed_formed : GeneralNominalSharedSteps.SourceFormed registry root refreshed :=
  .update formed refresh_step

theorem refreshed_models (m : GeneralNominalCommonBridge.Assignment) :
    Models refreshed.current m ↔ Models finish.current m :=
  GeneralNominalCycleSteps.refresh_models certificate m

theorem refreshed_evidence (m : GeneralNominalCommonBridge.Assignment)
    (valid : Models refreshed.current m) :
    GeneralDictionaryRecursiveEvidence.Evidence registry refreshed.current.context m root
      (.node declaration.id []) :=
  GeneralDictionarySharedSourceRetention.identity_current_evidence refreshed_formed packet
    List.mem_cons_self shape 0 point m valid

theorem nonvacuous_refreshed_evidence :
    GeneralNominalSharedSteps.SourceFormed registry root refreshed ∧
    Models refreshed.current (model .int) ∧
    GeneralDictionaryRecursiveEvidence.Evidence registry refreshed.current.context (model .int) root
      (.node declaration.id []) :=
  ⟨refreshed_formed,(refreshed_models _).mpr current_model,
    refreshed_evidence _ ((refreshed_models _).mpr current_model)⟩

theorem not_ordinary_extension :
    ¬ GeneralDictionaryOrdinaryTrace.Extension finish.current.context refreshed.current.context := by
  rintro ⟨reserved,atoms,allocated,equal⟩
  have lengths := congrArg (fun ctx : GeneralNominalCandidates.Context => ctx.state.base.ordinary.length) equal
  change 4 = 2 at lengths
  contradiction

end Yulang.GeneralDictionaryIdentityRefreshExample
