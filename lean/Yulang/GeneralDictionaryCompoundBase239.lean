import Yulang.GeneralDictionaryCompoundTrust239
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryCompoundBase239
open GeneralDictionaryJournalRefinement228Source
open GeneralSourceState (equationAtoms equationAtoms_exact)
abbrev lo := GeneralDictionaryCompoundModel238.names 0
abbrev hi := GeneralDictionaryCompoundModel238.names 1
abbrev embed (slot : Fin 5) : Fin 7 := ⟨slot.val,by omega⟩
def source (slot : Fin 7) : Nat := if slot.val < 5 then slot.val else if slot.val = 5 then lo else hi

theorem source_embed (slot : Fin 5) : source (embed slot) = slot.val := by
  simp only [source,slot.isLt,ite_true]
theorem source_five : source 5 = lo := rfl
theorem source_six : source 6 = hi := rfl
theorem source_injective : Function.Injective source := by unfold Function.Injective; decide +kernel

abbrev shapes (kind : Fin 2) : GeneralSourceState.Shape 7 := if kind = 0 then .emptyRecord else .variant 0
abbrev heads (slot : Fin 7) : GeneralSourceState.Head shapes :=
  if slot = 2 then .structural 0 Fin.elim0 else
  if slot = 5 then .structural 1 (fun _ => 4) else
  if slot = 6 then .structural 1 (fun _ => 2) else .unresolved
abbrev extendedBase : GeneralSourceState.State where
  slots := 7
  source := source
  source_injective := source_injective
  rowSource := source
  ordinary := base.ordinary.map (PresenceNormalForm.Atom.rename embed) ++
    (equationAtoms 5 (.variant 0 (.var 4)) ++ equationAtoms 6 (.variant 0 (.var 2)))
  kinds := 2
  shapes := shapes
  shapes_injective := by
    intro a b same
    by_cases az : a = 0 <;> by_cases bz : b = 0
    · exact az.trans bz.symm
    · simp [shapes,az,bz] at same
    · simp [shapes,az,bz] at same
    · have ah := a.isLt; have bh := b.isLt; exact Fin.ext (by omega)
  heads := heads
  intervals := []
  heads_sound := by
    intro assignment valid slot term found
    have parts := (PresenceNormalForm.all_append ..).mp valid
    have old := (PresenceNormalForm.all_rename ..).mp parts.1
    have added := (PresenceNormalForm.all_append ..).mp parts.2
    by_cases two : slot = 2
    · subst slot
      have same : term = .emptyRecord := Option.some.inj found.symm
      subst term
      exact base.heads_sound (assignment ∘ embed) old 2 .emptyRecord rfl
    · by_cases five : slot = 5
      · subst slot
        have same : term = .variant 0 (.var 4) := Option.some.inj found.symm
        subst term
        exact (equationAtoms_exact ..).mp added.1
      · by_cases six : slot = 6
        · subst slot
          have same : term = .variant 0 (.var 2) := Option.some.inj found.symm
          subst term
          exact (equationAtoms_exact ..).mp added.2
        · simp [heads,two,five,six,GeneralSourceState.Head.equation] at found
  intervals_sound := by intro _ _ _ impossible; cases impossible

abbrev viewShapes (kind : Fin 2) : GeneralNormalizedObservation.Shape := if kind = 0 then .record [] else .variant 0
abbrev viewHeads (slot : Fin 7) : GeneralNormalizedObservation.Head viewShapes 7 :=
  if slot = 2 then .structural 0 Fin.elim0 else
  if slot = 5 then .structural 1 (fun _ => 4) else
  if slot = 6 then .structural 1 (fun _ => 2) else .deferred .unresolved
abbrev extendedView : GeneralNormalizedObservation.Snapshot extendedBase where
  kinds := 2
  shapes := viewShapes
  shapes_injective := by unfold Function.Injective; decide +kernel
  canonical := by intro kind; by_cases zero : kind = 0 <;> simp [viewShapes,zero,GeneralNormalizedObservation.Shape.Canonical]
  heads := viewHeads
  checked := by
    intro slot term found
    by_cases two : slot = 2
    · subst slot
      have same : term = .emptyRecord := Option.some.inj found.symm
      subst term
      exact .head rfl
    · by_cases five : slot = 5
      · subst slot
        have same : term = .variant 0 (.var 4) := Option.some.inj found.symm
        subst term
        exact .head rfl
      · by_cases six : slot = 6
        · subst slot
          have same : term = .variant 0 (.var 2) := Option.some.inj found.symm
          subst term
          exact .head rfl
        · simp [viewHeads,two,five,six,GeneralNormalizedObservation.Head.term,GeneralNormalizedObservation.Deferred.term] at found
end Yulang.GeneralDictionaryCompoundBase239
