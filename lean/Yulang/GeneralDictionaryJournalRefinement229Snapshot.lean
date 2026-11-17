import Yulang.GeneralDictionaryJournalRefinement228Trusted
import Yulang.GeneralDictionaryJournalRefinement228Stage
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryJournalRefinement229Snapshot
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryJournalRefinement228Stage
open GeneralSourceState (equationAtoms equationAtoms_exact)
private theorem cases2 (k : Fin 2) : k = 0 ∨ k = 1 := by
  have bound := k.isLt
  have : k.val = 0 ∨ k.val = 1 := by omega
  rcases this with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)
abbrev shapes (k : Fin 2) : GeneralSourceState.Shape 5 := if k = 0 then .emptyRecord else .exactEmpty
abbrev heads (slot : Fin 5) : GeneralSourceState.Head shapes :=
  if slot = 2 then .structural 0 Fin.elim0 else if slot = 4 then .structural 1 Fin.elim0 else .unresolved

abbrev refreshedBase : GeneralSourceState.State where
  slots := 5
  source := Fin.val
  source_injective := fun _ _ h => Fin.ext h
  rowSource := Fin.val
  ordinary := base.ordinary ++ equationAtoms 4 .exactEmpty
  kinds := 2
  shapes := shapes
  shapes_injective := by
    intro a b h
    rcases cases2 a with rfl | rfl <;> rcases cases2 b with rfl | rfl <;> first | rfl | cases h
  heads := heads
  intervals := []
  heads_sound := by
    intro assignment valid slot term found
    have parts := (PresenceNormalForm.all_append ..).mp valid
    by_cases two : slot = 2
    · subst slot
      have equal : term = .emptyRecord := Option.some.inj found.symm
      subst term
      exact base.heads_sound assignment parts.1 2 .emptyRecord rfl
    · by_cases four : slot = 4
      · subst slot
        have equal : term = .exactEmpty := Option.some.inj found.symm
        subst term
        exact (equationAtoms_exact ..).mp parts.2
      · simp [heads,two,four,GeneralSourceState.Head.equation] at found
  intervals_sound := by intro _ _ _ impossible; cases impossible
abbrev viewShapes (k : Fin 2) : GeneralNormalizedObservation.Shape := if k = 0 then .record [] else .exactEmpty
abbrev viewHeads (slot : Fin 5) : GeneralNormalizedObservation.Head viewShapes 5 :=
  if slot = 2 then .structural 0 Fin.elim0 else if slot = 4 then .structural 1 Fin.elim0 else .deferred .unresolved

abbrev refreshedView : GeneralNormalizedObservation.Snapshot refreshedBase where
  kinds := 2
  shapes := viewShapes
  shapes_injective := by
    intro a b h
    rcases cases2 a with rfl | rfl <;> rcases cases2 b with rfl | rfl <;> first | rfl | cases h
  canonical := by
    intro k
    rcases cases2 k with rfl | rfl
    · exact List.Pairwise.nil
    · trivial
  heads := viewHeads
  checked := by
    intro slot term recorded
    by_cases two : slot = 2
    · subst slot
      have equal : term = .emptyRecord := Option.some.inj recorded.symm
      subst term
      exact .head rfl
    · by_cases four : slot = 4
      · subst slot
        have equal : term = .exactEmpty := Option.some.inj recorded.symm
        subst term
        exact .head rfl
      · simp [viewHeads,two,four,GeneralNormalizedObservation.Head.term,GeneralNormalizedObservation.Deferred.term] at recorded
noncomputable abbrev refreshedSnapshot : GeneralNominalState.State where
  base := refreshedBase
  view := refreshedView
  constructors := constructors
  nominals := GeneralDictionaryJournalRefinement228Reobserve.pointSnapshot.nominals
  catalogue := GeneralDictionaryJournalRefinement228Reobserve.pointSnapshot.catalogue
  bodies_opaque := by
    intro slot d found
    change (if slot = 0 ∨ slot = 1 then some _ else none) = some d at found
    split at found
    · rename_i either
      rcases either with rfl | rfl <;> rfl
    · cases found
  allocated := allocated
  reserved := reserved
  ordinary := ordinary
  seed := snapshot.seed
noncomputable abbrev refreshedContext : GeneralNominalCandidates.Context := ⟨refreshedSnapshot,interpretation⟩
end Yulang.GeneralDictionaryJournalRefinement229Snapshot
