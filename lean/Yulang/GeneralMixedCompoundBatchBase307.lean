import Yulang.GeneralMixedCompoundRefreshBound307

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralMixedCompoundBatchBase307
open GeneralDictionaryJournalRefinement228Source (snapshot base)
open GeneralDictionaryJournalRefinement228Reobserve (exactCopy)
open GeneralDictionaryCompoundPoint238 (point)
open GeneralDictionaryCompoundSnapshot239 (extendedSnapshot pointDesc)
open GeneralMixedCompoundUpperBase307 (source source_old source_new)
open GeneralMixedCompoundUpperSnapshot307 (snap refineRaw)
open GeneralNominalRefinements (Refines renameDescriptor)
open GeneralNominalState (Known)
open GeneralSourceState (equationAtoms)

abbrev embed (slot : Fin 5) : Fin 8 :=
  GeneralMixedCompoundUpperBase307.embed (GeneralDictionaryCompoundBase239.embed slot)

theorem source_eq (slot : Fin 5) : source (embed slot) = slot.val :=
  (source_old _).trans (GeneralDictionaryCompoundBase239.source_embed slot)

theorem atom_membership (atom : PresenceNormalForm.Atom (Fin 5)) (present : atom ∈ base.ordinary) :
    atom.rename embed ∈ GeneralMixedCompoundUpperBase307.base.ordinary := by
  have first := GeneralDictionaryCompoundSnapshot239.refines.base.ordinary atom present
  have second := refineRaw.base.ordinary (atom.rename GeneralDictionaryCompoundBase239.embed) first
  have same : (atom.rename GeneralDictionaryCompoundBase239.embed).rename GeneralMixedCompoundUpperBase307.embed =
      atom.rename embed := by
    simp only [base,equationAtoms,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with (((rfl|rfl)|(rfl|rfl))|(rfl|rfl))|rfl <;> rfl
  change (atom.rename GeneralDictionaryCompoundBase239.embed).rename GeneralMixedCompoundUpperBase307.embed ∈
    GeneralMixedCompoundUpperBase307.base.ordinary at second
  rw [same] at second
  exact second

theorem known_point {n : Nat} (observed : Known point.core.erased.current.context.state n) :
    Known snap n :=
  refineRaw.known _ (GeneralDictionaryCompoundSnapshot239.refines.known _ observed)

noncomputable def refineBatch : Refines point.core.erased.current.context.state snap where
  base := ⟨embed,source_eq,source_eq,atom_membership,
    (fun slot nonempty => GeneralMixedCompoundUpperSnapshot307.base_known _
      (GeneralDictionaryCompoundSnapshot239.refines.base.known slot nonempty)),
    (fun _ h => nomatch h)⟩
  heads := by
    intro slot term saved
    change (base.heads slot).equation = some term at saved
    by_cases same : slot = (2 : Fin 5)
    · subst slot
      have termEq : term = .emptyRecord := Option.some.inj saved.symm
      subst term
      exact .head rfl
    · simp [base,same,GeneralSourceState.Head.equation] at saved
  nominals := by
    intro slot d saved
    change Fin 5 at slot
    change (if slot = 0 ∨ slot = 1 then some exactCopy else none) = some d at saved
    split at saved
    · rename_i prev
      cases Option.some.inj saved
      rcases prev with rfl|rfl <;> rfl
    · cases saved
  ordinary := fun _ h => h
  known := fun _ h => known_point h
  reserved := fun _ h => h
  allocated := fun _ h => h
  seed := rfl
  constructors := rfl

end Yulang.GeneralMixedCompoundBatchBase307
