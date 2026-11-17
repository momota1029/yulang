import Yulang.GeneralDictionaryVersionedTrusted233
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryMixedClosedBase234
open GeneralDictionaryJournalRefinement228Source
abbrev oldHi := GeneralDictionaryVersionedInitialModel233.names 1
abbrev newLo := GeneralDictionaryVersionedNames231.freshName 0
abbrev newHi := GeneralDictionaryVersionedNames231.freshName 1
open GeneralSourceState (equationAtoms equationAtoms_exact)

abbrev embed (slot : Fin 5) : Fin 8 := ⟨slot.val,by omega⟩
def source (slot : Fin 8) : Nat := if slot.val < 5 then slot.val else if slot.val = 5 then oldHi else if slot.val = 6 then newLo else newHi

theorem source_embed (slot : Fin 5) : source (embed slot) = slot.val := by
  simp only [source,slot.isLt,ite_true]
theorem source_five : source 5 = oldHi := rfl
theorem source_six : source 6 = newLo := rfl
theorem source_seven : source 7 = newHi := rfl

theorem source_injective : Function.Injective source := by unfold Function.Injective; decide +kernel

abbrev shapes (_ : Fin 1) : GeneralSourceState.Shape 8 := .emptyRecord
abbrev heads (slot : Fin 8) : GeneralSourceState.Head shapes :=
  if slot = 2 ∨ 5 ≤ slot.val then .structural 0 Fin.elim0 else .unresolved

abbrev extendedBase : GeneralSourceState.State where
  slots := 8
  source := source
  source_injective := source_injective
  rowSource := source
  ordinary := base.ordinary.map (PresenceNormalForm.Atom.rename embed) ++ (equationAtoms 5 .emptyRecord ++ equationAtoms 6 .emptyRecord ++ equationAtoms 7 .emptyRecord)
  kinds := 1
  shapes := shapes
  shapes_injective := by intro a b _; exact Subsingleton.elim a b
  heads := heads
  intervals := []
  heads_sound := by
    intro assignment valid slot term found
    have parts := (PresenceNormalForm.all_append ..).mp valid
    have old := (PresenceNormalForm.all_rename ..).mp parts.1
    by_cases two : slot = 2
    · subst slot
      have same : term = .emptyRecord := Option.some.inj found.symm
      subst term
      exact base.heads_sound (assignment ∘ embed) old 2 .emptyRecord rfl
    · by_cases five : 5 ≤ slot.val
      · have same : term = .emptyRecord := by
          simpa [heads,shapes,two,five,GeneralSourceState.Head.equation,GeneralSourceState.Shape.term] using found.symm
        subst term
        have parts := (PresenceNormalForm.all_append ..).mp parts.2
        have cases : slot = 5 ∨ slot = 6 ∨ slot = 7 := by have bound := slot.isLt; omega
        rcases cases with rfl | rfl | rfl
        · exact (equationAtoms_exact ..).mp ((PresenceNormalForm.all_append ..).mp parts.1).1
        · exact (equationAtoms_exact ..).mp ((PresenceNormalForm.all_append ..).mp parts.1).2
        · exact (equationAtoms_exact ..).mp parts.2
      · simp [heads,two,five,GeneralSourceState.Head.equation] at found
  intervals_sound := by intro _ _ _ impossible; cases impossible

abbrev viewShapes (_ : Fin 1) : GeneralNormalizedObservation.Shape := .record []
abbrev viewHeads (slot : Fin 8) : GeneralNormalizedObservation.Head viewShapes 8 :=
  if slot = 2 ∨ 5 ≤ slot.val then .structural 0 Fin.elim0 else .deferred .unresolved
abbrev extendedView : GeneralNormalizedObservation.Snapshot extendedBase where
  kinds := 1
  shapes := viewShapes
  shapes_injective := by intro a b _; exact Subsingleton.elim a b
  canonical := by intro _; exact List.Pairwise.nil
  heads := viewHeads
  checked := by
    intro slot term found
    by_cases known : slot = 2 ∨ 5 ≤ slot.val
    · have same : term = .emptyRecord := by
        simpa [viewHeads,known,GeneralNormalizedObservation.Head.term,
          GeneralNormalizedObservation.Shape.term,GeneralNormalizedObservation.recordTerm] using found.symm
      subst term
      apply GeneralNormalizedObservation.Rewrites.head
      simp [heads,known,GeneralSourceState.Head.equation,GeneralSourceState.Shape.term]
    · simp [viewHeads,known,GeneralNormalizedObservation.Head.term,GeneralNormalizedObservation.Deferred.term] at found

end Yulang.GeneralDictionaryMixedClosedBase234
