import Yulang.GeneralDictionaryNominalSlotTransport
import Yulang.GeneralDictionaryHeadlessLocations

/-!
# Successful variable localization survives certified slot transport

The source demand, declaration and global capture stay fixed. Only local slot
indices are renamed through the supplied transport. These are one-way success
results: adding represented source IDs can turn an old failure into success.
No computed-frame equality between different candidate contexts is asserted.
-/
namespace Yulang.GeneralDictionarySlotLocalizationTransport
open GeneralDeclarations GeneralDeclarationDemands
open GeneralSourceState (Demand)
open GeneralDictionaryNominalSlotTransport (Transport)
open GeneralDictionaryBinderLocations (sourceSlot locateTerm)
open GeneralDictionaryVariableHeads (HeadlessInputs)
open Core.PresenceGeneration (TyTerm)
variable {before after : GeneralNominalState.State} {roles : Roles.RoleDecls}

/-- Lookup follows the retained global source identity, not its local number. -/
theorem sourceSlot_success (transport : Transport before after) (source : Nat)
    (slot : Fin before.base.slots) (found : sourceSlot before.base source = some slot) :
    sourceSlot after.base source = some (transport.embed slot) := by
  apply (GeneralDictionaryBinderLocations.sourceSlot_exact _ _ _).mpr
  rw [transport.source]
  exact (GeneralDictionaryBinderLocations.sourceSlot_exact _ _ _).mp found

theorem locateTerm_success (transport : Transport before after) (source : TyTerm Nat)
    (term : TyTerm (Fin before.base.slots)) (found : locateTerm before.base source = some term) :
    locateTerm after.base source = some (term.rename transport.embed) := by
  cases source <;> simp only [locateTerm] at found ⊢
  all_goals try { cases found }
  next source =>
    obtain ⟨slot, present, rfl⟩ := Option.map_eq_some_iff.mp found
    rw [sourceSlot_success transport source slot present]
    rfl

/-- The output-only compiler preserves its exact local result. -/
theorem binder_compile_success (transport : Transport before after) (declaration : Declaration)
    (capture : Capture) (name : Nat) (term : TyTerm (Fin before.base.slots))
    (found : GeneralDictionaryBinderLocations.compile before.base roles declaration capture name = some term) :
    GeneralDictionaryBinderLocations.compile after.base roles declaration capture name =
      some (term.rename transport.embed) := by
  obtain ⟨source, original, localized⟩ := Option.bind_eq_some_iff.mp found
  exact Option.bind_eq_some_iff.mpr ⟨source, original, locateTerm_success transport source term localized⟩

/-- Both supported explicit input- and output-variable RHS cases are retained. -/
theorem variable_compile_success (transport : Transport before after) (declaration : Declaration)
    (capture : Capture) (name : Nat) (term : TyTerm (Fin before.base.slots))
    (found : GeneralDictionaryVariableTerms.compile before.base roles declaration capture name = some term) :
    GeneralDictionaryVariableTerms.compile after.base roles declaration capture name =
      some (term.rename transport.embed) := by
  obtain ⟨source, original, localized⟩ := Option.bind_eq_some_iff.mp found
  exact Option.bind_eq_some_iff.mpr ⟨source, original, locateTerm_success transport source term localized⟩

/-- Reindex all occurrences, retaining duplicated demand endpoints and targets. -/
def headlessInputs (transport : Transport before after) (inputs : HeadlessInputs before.base demand) :
    HeadlessInputs after.base demand where
  lower := fun index => transport.embed (inputs.lower index)
  upper := fun index => transport.embed (inputs.upper index)
  target := fun index => transport.embed (inputs.target index)
  arguments := by intro index; simpa only [transport.source] using inputs.arguments index
  targets := by intro index; simpa only [transport.source] using inputs.targets index

/-- The computed target package is exactly the reindexed old package. An old
valid package already certifies old localization, so no lookup premise is needed. -/
theorem headless_locate (transport : Transport before after) (demand : Demand roles)
    (inputs : HeadlessInputs before.base demand) :
    GeneralDictionaryHeadlessLocations.locate after.base demand = some (headlessInputs transport inputs) :=
  GeneralDictionaryHeadlessLocations.locate_inputs (headlessInputs transport inputs)

theorem available (transport : Transport before after) (demand : Demand roles)
    (present : GeneralDictionaryHeadlessLocations.Available before.base demand) :
    GeneralDictionaryHeadlessLocations.Available after.base demand := by
  refine ⟨?_, ?_, ?_⟩
  · intro index
    obtain ⟨slot, source⟩ := present.1 index
    exact ⟨transport.embed slot, (transport.source slot).trans source⟩
  · intro index
    obtain ⟨slot, source⟩ := present.2.1 index
    exact ⟨transport.embed slot, (transport.source slot).trans source⟩
  · intro index
    obtain ⟨slot, source⟩ := present.2.2 index
    exact ⟨transport.embed slot, (transport.source slot).trans source⟩

/-- Head identity equality and provenance are kept, rather than replaced by
semantic equality of two distinct captured endpoints. -/
theorem head_denotesAt (transport : Transport before after) (declaration : Declaration)
    (capture : Capture) (index : Nat) (term : TyTerm (Fin before.base.slots))
    (denoted : GeneralDictionaryVariableHeads.DenotesAt before.base declaration capture index term) :
    GeneralDictionaryVariableHeads.DenotesAt after.base declaration capture index (term.rename transport.embed) := by
  obtain ⟨pattern, binder, slot, present, normalized, input, singleton, source, rfl⟩ := denoted
  exact ⟨pattern, binder, transport.embed slot, present, normalized, input, singleton,
    (transport.source slot).trans source, rfl⟩

theorem head_compile_success (transport : Transport before after) (declaration : Declaration)
    (capture : Capture) (index : Nat) (term : TyTerm (Fin before.base.slots))
    (found : GeneralDictionaryVariableHeads.compileAt before.base declaration capture index = some term) :
    GeneralDictionaryVariableHeads.compileAt after.base declaration capture index =
      some (term.rename transport.embed) :=
  (GeneralDictionaryVariableHeads.compileAt_exact _ _ _ _ _).mpr
    (head_denotesAt transport declaration capture index term
      ((GeneralDictionaryVariableHeads.compileAt_exact _ _ _ _ _).mp found))

end Yulang.GeneralDictionarySlotLocalizationTransport
