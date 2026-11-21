import Yulang.GeneralMixedCompoundPointFeedback308
import Yulang.GeneralMixedCompoundUpperBase307

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralMixedCompoundPointViewBase308
open GeneralDictionaryJournalRefinement228Source (snapshot)
open GeneralDictionaryCompoundBase239 (extendedBase extendedView)
open GeneralDictionaryCompoundVersionedModel238 (names)
open GeneralSourceState (equationAtoms equationAtoms_exact)
abbrev upper := GeneralDictionaryCompoundPointHead238.freshName 1
abbrev embed (slot : Fin 7) : Fin 8 := slot.castSucc
def source : Fin 8 → Nat := Fin.lastCases upper GeneralDictionaryCompoundBase239.source

theorem source_old (slot : Fin 7) : source (embed slot) = GeneralDictionaryCompoundBase239.source slot :=
  Fin.lastCases_castSucc slot

theorem source_new : source 7 = upper := Fin.lastCases_last

theorem injective : Function.Injective source := by unfold Function.Injective; decide +kernel

abbrev shapes (kind : Fin 2) : GeneralSourceState.Shape 8 := if kind = 0 then .emptyRecord else .variant 0
abbrev heads (slot : Fin 8) : GeneralSourceState.Head shapes :=
  if slot = 2 ∨ slot = 7 then .structural 0 Fin.elim0 else
  if slot = 5 then .structural 1 (fun _ => 2) else
  if slot = 6 then .structural 1 (fun _ => 2) else .unresolved

abbrev base : GeneralSourceState.State where
  slots := 8
  source := source
  source_injective := injective
  rowSource := source
  ordinary := GeneralDictionaryJournalRefinement228Source.base.ordinary.map (PresenceNormalForm.Atom.rename (fun i => embed (GeneralDictionaryCompoundBase239.embed i))) ++
    (equationAtoms 5 (.variant 0 (.var 2)) ++ equationAtoms 6 (.variant 0 (.var 2)) ++ equationAtoms 7 .emptyRecord)
  kinds := 2
  shapes := shapes
  shapes_injective := by
    intro a b h
    by_cases az : a = 0 <;> by_cases bz : b = 0
    · exact az.trans bz.symm
    · simp [shapes,az,bz] at h
    · simp [shapes,az,bz] at h
    · have al := a.isLt; have bl := b.isLt; exact Fin.ext (by omega)
  heads := heads
  intervals := []
  heads_sound := by
    intro assignment valid slot term found
    have parts := (PresenceNormalForm.all_append ..).mp valid
    have old := (PresenceNormalForm.all_rename ..).mp parts.1
    have ⟨ports,agg⟩ := (PresenceNormalForm.all_append ..).mp parts.2
    have ⟨lo,hi⟩ := (PresenceNormalForm.all_append ..).mp ports
    by_cases two : slot = 2
    · subst slot
      have same : term = .emptyRecord := Option.some.inj found.symm
      subst term
      exact GeneralDictionaryJournalRefinement228Source.base.heads_sound _ old 2 .emptyRecord rfl
    · by_cases seven : slot = 7
      · subst slot
        have same : term = .emptyRecord := Option.some.inj found.symm
        subst term
        exact (equationAtoms_exact ..).mp agg
      · by_cases five : slot = 5
        · subst slot
          have same : term = .variant 0 (.var 2) := Option.some.inj found.symm
          subst term
          exact (equationAtoms_exact ..).mp lo
        · by_cases six : slot = 6
          · subst slot
            have same : term = .variant 0 (.var 2) := Option.some.inj found.symm
            subst term
            exact (equationAtoms_exact ..).mp hi
          · simp [heads,two,seven,five,six,GeneralSourceState.Head.equation] at found
  intervals_sound := by intro _ _ _ impossible; cases impossible

abbrev viewHeads (slot : Fin 8) :
    GeneralNormalizedObservation.Head GeneralDictionaryCompoundBase239.viewShapes 8 :=
  if slot = 2 ∨ slot = 7 then .structural 0 Fin.elim0 else
  if slot = 5 then .structural 1 (fun _ => 2) else
  if slot = 6 then .structural 1 (fun _ => 2) else .deferred .unresolved

abbrev view : GeneralNormalizedObservation.Snapshot base where
  kinds := extendedView.kinds
  shapes := extendedView.shapes
  shapes_injective := extendedView.shapes_injective
  canonical := extendedView.canonical
  heads := viewHeads
  checked := by
    intro slot term found
    by_cases empty : slot = 2 ∨ slot = 7
    · rcases empty with rfl|rfl <;>
        have same : term = .emptyRecord := Option.some.inj found.symm <;> subst term <;> exact .head rfl
    · by_cases five : slot = 5
      · subst slot
        have same : term = .variant 0 (.var 2) := Option.some.inj found.symm
        subst term; exact .head rfl
      · by_cases six : slot = 6
        · subst slot
          have same : term = .variant 0 (.var 2) := Option.some.inj found.symm
          subst term; exact .head rfl
        · simp [viewHeads,empty,five,six,GeneralNormalizedObservation.Head.term,
            GeneralNormalizedObservation.Deferred.term] at found

end Yulang.GeneralMixedCompoundPointViewBase308
