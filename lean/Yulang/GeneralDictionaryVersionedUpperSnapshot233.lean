import Yulang.GeneralDictionaryVersionedUpperBase233
import Yulang.GeneralDictionaryVersionedSecondInstall233
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryVersionedUpperSnapshot233
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryJournalRefinement228Reobserve
open GeneralDictionaryVersionedSecondInstall233 (installed)
noncomputable abbrev allocated := installed.core.erased.current.context.state.allocated
noncomputable abbrev reserved := installed.core.erased.current.context.state.reserved
noncomputable abbrev ordinary := installed.core.erased.current.context.state.ordinary
open GeneralDictionaryVersionedUpperBase233

abbrev pointDesc : GeneralNominalState.Descriptor 6 :=
  GeneralNominalRefinements.renameDescriptor embed exactCopy
noncomputable abbrev extendedSnapshot : GeneralNominalState.State where
  base := extendedBase
  view := extendedView
  constructors := constructors
  nominals := fun slot => if slot = 0 ∨ slot = 1 then some pointDesc else none
  catalogue := by
    intro slot d found
    split at found
    · cases Option.some.inj found; rfl
    · cases found
  bodies_opaque := by
    intro slot d found
    split at found
    · rename_i either
      rcases either with rfl | rfl <;> rfl
    · cases found
  allocated := allocated
  reserved := reserved
  ordinary := ordinary
  seed := snapshot.seed
noncomputable abbrev extendedContext : GeneralNominalCandidates.Context := ⟨extendedSnapshot,interpretation⟩

noncomputable def refines : GeneralNominalRefinements.Refines
    installed.core.erased.current.context.state extendedSnapshot := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,rfl,rfl⟩
  · refine ⟨embed,source_embed,source_embed,?_,?_,?_⟩
    · intro atom member
      exact List.mem_append_left _ (List.mem_map.mpr ⟨atom,member,rfl⟩)
    · intro slot known
      change Fin 5 at slot
      change (base.heads slot).node ≠ _ at known
      by_cases two : slot = 2
      · subst slot; decide +kernel
      · exact False.elim (known (by simp [base,two,GeneralSourceState.Head.node]))
    · intro pair member; cases member
  · intro slot term found
    change Fin 5 at slot
    change (base.heads slot).equation = some term at found
    by_cases two : slot = 2
    · subst slot
      have same : term = .emptyRecord := Option.some.inj found.symm
      subst term
      exact .head rfl
    · simp [base,two,GeneralSourceState.Head.equation] at found
  · intro slot d found
    change Fin 5 at slot
    change (if slot = 0 ∨ slot = 1 then some exactCopy else none) = some d at found
    split at found
    · rename_i either
      cases Option.some.inj found
      rcases either with rfl | rfl <;> rfl
    · cases found
  · intro atom member; exact member
  · intro identity known
    obtain ⟨slot,same,normalized | ⟨d,nominal⟩⟩ := known
    · refine ⟨embed slot,?_,Or.inl ?_⟩
      · exact (source_embed slot).trans same
      · change Fin 5 at slot
        change (view.heads slot).node ≠ _ at normalized
        by_cases two : slot = 2
        · subst slot; decide +kernel
        · exact False.elim (normalized (by simp [two,GeneralNormalizedObservation.Head.node]))
    · refine ⟨embed slot,(source_embed slot).trans same,Or.inr ⟨pointDesc,?_⟩⟩
      change Fin 5 at slot
      change (if slot = 0 ∨ slot = 1 then some exactCopy else none) = some d at nominal
      split at nominal
      · rename_i either
        rcases either with rfl | rfl <;> rfl
      · cases nominal
  · intro identity member; exact member
  · intro key member; exact member

theorem assignment_transport (m : GeneralNominalCommonBridge.Assignment) :
    GeneralNominalCommonBridge.assignment extendedBase m ∘ embed =
      GeneralNominalCommonBridge.assignment base m := by
  funext slot
  change ((m (source (embed slot))).1,(m (source (embed slot))).2) = ((m slot.val).1,(m slot.val).2)
  rw [source_embed]

end Yulang.GeneralDictionaryVersionedUpperSnapshot233
