import Yulang.GeneralDictionaryOptionalInstall229
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryUpper230Base
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInstall229 (hi fresh_large)
open GeneralSourceState (equationAtoms equationAtoms_exact)

abbrev embed (slot : Fin 5) : Fin 6 := ⟨slot.val,Nat.lt_succ_of_lt slot.isLt⟩
def source (slot : Fin 6) : Nat := if slot.val < 5 then slot.val else hi

theorem source_embed (slot : Fin 5) : source (embed slot) = slot.val := by
  simp only [source,slot.isLt,ite_true]
theorem source_last : source 5 = hi := rfl

theorem source_injective : Function.Injective source := by
  intro a b equal
  by_cases first : a.val < 5
  · by_cases last : b.val < 5
    · exact Fin.ext (by simpa only [source,first,last,ite_true] using equal)
    · have large : 4 < hi := fresh_large 1
      have same : a.val = hi := by simpa only [source,first,last,ite_true,ite_false] using equal
      omega
  · by_cases last : b.val < 5
    · have large : 4 < hi := fresh_large 1
      have same : hi = b.val := by simpa only [source,first,last,ite_true,ite_false] using equal
      omega
    · have one := a.isLt
      have two := b.isLt
      apply Fin.ext
      omega

abbrev shapes (_ : Fin 1) : GeneralSourceState.Shape 6 := .emptyRecord
abbrev heads (slot : Fin 6) : GeneralSourceState.Head shapes :=
  if slot = 2 ∨ slot = 5 then .structural 0 Fin.elim0 else .unresolved

abbrev extendedBase : GeneralSourceState.State where
  slots := 6
  source := source
  source_injective := source_injective
  rowSource := source
  ordinary := base.ordinary.map (PresenceNormalForm.Atom.rename embed) ++ equationAtoms 5 .emptyRecord
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
    · by_cases five : slot = 5
      · subst slot
        have same : term = .emptyRecord := Option.some.inj found.symm
        subst term
        exact (equationAtoms_exact ..).mp parts.2
      · simp [heads,two,five,GeneralSourceState.Head.equation] at found
  intervals_sound := by intro _ _ _ impossible; cases impossible

abbrev viewShapes (_ : Fin 1) : GeneralNormalizedObservation.Shape := .record []
abbrev viewHeads (slot : Fin 6) : GeneralNormalizedObservation.Head viewShapes 6 :=
  if slot = 2 ∨ slot = 5 then .structural 0 Fin.elim0 else .deferred .unresolved
abbrev extendedView : GeneralNormalizedObservation.Snapshot extendedBase where
  kinds := 1
  shapes := viewShapes
  shapes_injective := by intro a b _; exact Subsingleton.elim a b
  canonical := by intro _; exact List.Pairwise.nil
  heads := viewHeads
  checked := by
    intro slot term found
    by_cases known : slot = 2 ∨ slot = 5
    · have same : term = .emptyRecord := by
        simpa [viewHeads,known,GeneralNormalizedObservation.Head.term,
          GeneralNormalizedObservation.Shape.term,GeneralNormalizedObservation.recordTerm] using found.symm
      subst term
      apply GeneralNormalizedObservation.Rewrites.head
      simp [heads,known,GeneralSourceState.Head.equation,GeneralSourceState.Shape.term]
    · simp [viewHeads,known,GeneralNormalizedObservation.Head.term,GeneralNormalizedObservation.Deferred.term] at found

end Yulang.GeneralDictionaryUpper230Base
