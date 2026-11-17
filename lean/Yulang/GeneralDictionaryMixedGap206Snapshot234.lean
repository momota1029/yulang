import Yulang.GeneralDictionaryMixedGap206Trusted234
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryMixedGap206Snapshot234
open GeneralDictionaryDefaultGap206Source
open GeneralDictionaryVersionedGap206Feedback234 (feedback)
open Core.PresenceGeneration (TyTerm)
open GeneralSourceState (equationAtoms)
open CommonNominalFullCarrier

abbrev base : GeneralSourceState.State where
  slots := 3
  source := Fin.val
  source_injective := fun _ _ same => Fin.ext same
  rowSource := Fin.val
  ordinary := GeneralNominalCenteredTerminalForkSource.base.ordinary ++ equationAtoms 0 (.base .int)
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  heads := fun _ => .scalar .int
  intervals := []
  heads_sound := by
    intro assignment valid slot term recorded
    have same : term = (.base .int : TyTerm (Fin 3)) := Option.some.inj recorded.symm
    subst term
    have values := (PresenceNormalForm.all_append ..).mp valid
    have zero := (GeneralSourceState.equationAtoms_exact ..).mp values.2
    have others := (PresenceNormalForm.all_append ..).mp values.1
    have one := (GeneralSourceState.equationAtoms_exact ..).mp others.1
    have two := (GeneralSourceState.equationAtoms_exact ..).mp others.2
    rcases show slot = 0 ∨ slot = 1 ∨ slot = 2 by omega with rfl | rfl | rfl
    · exact zero
    · exact one
    · exact two
  intervals_sound := by intro _ _ _ member; cases member

abbrev view : GeneralNormalizedObservation.Snapshot base where
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  canonical := by intro i; exact Fin.elim0 i
  heads := fun _ => .scalar .int
  checked := by
    intro slot term recorded
    have same : term = (.base .int : TyTerm (Fin 3)) := Option.some.inj recorded.symm
    subst term
    exact .head rfl

noncomputable abbrev snapshot : GeneralNominalState.State where
  base := base
  view := view
  constructors := GeneralDeclarationExamples.constructors
  nominals := fun _ => none
  catalogue := by intro slot descriptor recorded; cases recorded
  bodies_opaque := by intro slot descriptor recorded; cases recorded
  seed := GeneralDictionaryDefaultGap206Source.snapshot.seed
  allocated := feedback.core.erased.current.context.state.allocated
  reserved := feedback.core.erased.current.context.state.reserved
  ordinary := feedback.core.erased.current.context.state.ordinary

noncomputable abbrev context : GeneralNominalCandidates.Context := ⟨snapshot,GeneralNominalExamples.interpretation⟩

noncomputable def refines : GeneralNominalRefinements.Refines feedback.core.erased.current.context.state snapshot := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,rfl,rfl⟩
  · refine ⟨id,fun _ => rfl,fun _ => rfl,?_,?_,?_⟩
    · intro atom member
      apply List.mem_append_left
      exact (GeneralNominalRefinements.refl feedback.core.erased.current.context.state).base.ordinary atom member
    · intro slot known
      intro impossible; cases impossible
    · intro pair member; cases member
  · intro slot term found
    change Fin 3 at slot
    change (if slot = 0 then GeneralSourceState.Head.unresolved else .scalar .int).equation = some term at found
    split at found
    · cases found
    · have same : term = (.base .int : TyTerm (Fin 3)) := Option.some.inj found.symm
      subst term
      exact .head rfl
  · intro slot descriptor found; cases found
  · intro atom member; exact member
  · intro identity known
    obtain ⟨slot,same,_⟩ := known
    exact ⟨slot,same,Or.inl (by intro impossible; cases impossible)⟩
  · intro identity member; exact member
  · intro key member; exact member

theorem support : ∀ identity ∈ GeneralNominalState.sources snapshot,
    identity ∈ GeneralNominalState.sources feedback.core.erased.current.context.state := by
  intro identity member
  exact member

theorem zero_unknown : ¬ GeneralNominalState.Known feedback.core.erased.current.context.state 0 := by
  rintro ⟨slot,same,head | ⟨descriptor,nominal⟩⟩
  · have zero : slot = (0 : Fin 3) := Fin.ext same
    subst slot
    exact head rfl
  · cases nominal

theorem zero_known : GeneralNominalState.Known snapshot 0 :=
  ⟨(0 : Fin 3),rfl,Or.inl (by intro impossible; cases impossible)⟩

end Yulang.GeneralDictionaryMixedGap206Snapshot234
