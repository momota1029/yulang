import Yulang.GeneralNominalRebaseRawProjection242
/-! Fixed public assignments hide private type coordinates existentially.
This establishes same-public-model preservation for the explicit definition
replacement, not a full source boundary or its evidence interpretation. -/
namespace Yulang.GeneralNominalRebasePublicModel242
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalFiniteEquationRealization236
open GeneralNominalRebaseEscapedProjection242
open GeneralNominalRebaseEscapedReplace242
open GeneralNominalRebaseRawProjection242

def PublicAgree (hidden : List Nat) (internal publicModel : Assignment) : Prop :=
 (∀ name, name ∉ hidden → internal name = publicModel name) ∧
 (∀ name, (internal name).2 = (publicModel name).2)

def Models (hidden : List Nat) (internalModels : Assignment → Prop) (publicModel : Assignment) : Prop :=
 ∃ internal, PublicAgree hidden internal publicModel ∧ internalModels internal

theorem preserves_public (entries : List Entry)
 (hidden : ∀ entry ∈ entries, entry.1 ∈ privateNames)
 (localSame : Preserves entries first middle)
 (publicSame : PublicAgree privateNames middle last) : PublicAgree privateNames first last := by
 constructor
 · intro name outside
   have absent : ∀ entry ∈ entries, entry.1 ≠ name := by
     intro entry member same
     exact outside (same ▸ hidden entry member)
   exact (localSame.1 name absent).trans (publicSame.1 name outside)
 · exact fun name => (localSame.2 name).trans (publicSame.2 name)

theorem replacement_models_iff (oldEntries newEntries : List Entry)
 (oldCoherent : Coherent oldEntries) (oldExternal : External oldEntries)
 (newCoherent : Coherent newEntries) (newExternal : External newEntries)
 (within : TargetsWithin newEntries oldEntries)
 (hidden : ∀ entry ∈ oldEntries, entry.1 ∈ privateNames)
 (retained : Assignment → Prop) (congruent : Congruent retained)
 (publicModel : Assignment) :
 Models privateNames (fun internal => Definitions oldEntries internal ∧ retained internal) publicModel ↔
 Models privateNames (fun internal => Definitions newEntries internal ∧ retained (patch oldEntries internal)) publicModel := by
 constructor
 · rintro ⟨old,same,definitions,valid⟩
   have original : ∃ extension, Preserves oldEntries extension old ∧ Definitions oldEntries extension ∧ retained extension :=
     ⟨old,⟨fun _ _ => rfl,fun _ => rfl⟩,definitions,valid⟩
   obtain ⟨next,localSame,newDefs,newValid⟩ :=
     (predicate_replacement oldEntries newEntries oldCoherent oldExternal newCoherent newExternal within retained congruent old).mp original
   exact ⟨next,preserves_public oldEntries hidden localSame same,newDefs,newValid⟩
 · rintro ⟨next,same,newDefs,valid⟩
   have original : ∃ extension, Preserves oldEntries extension next ∧ Definitions newEntries extension ∧ retained (patch oldEntries extension) :=
     ⟨next,⟨fun _ _ => rfl,fun _ => rfl⟩,newDefs,valid⟩
   obtain ⟨old,localSame,oldDefs,oldValid⟩ :=
     (predicate_replacement oldEntries newEntries oldCoherent oldExternal newCoherent newExternal within retained congruent next).mpr original
   exact ⟨old,preserves_public oldEntries hidden localSame same,oldDefs,oldValid⟩

/-- This is exactly same-public-assignment implication, not an implication that
changes the public model argument. Internal values may change. -/
theorem raw_step_models (oldEntries newEntries : List Entry)
 (oldCoherent : Coherent oldEntries) (oldExternal : External oldEntries)
 (newCoherent : Coherent newEntries) (newExternal : External newEntries)
 (within : TargetsWithin newEntries oldEntries)
 (hidden : ∀ entry ∈ oldEntries, entry.1 ∈ privateNames)
 (raw : GeneralNominalState.State) (atoms : List (PresenceNormalForm.Atom Nat))
 (publicModel : Assignment)
 (valid : Models privateNames (fun internal => Definitions newEntries internal ∧
   GeneralNominalState.Models raw (patch oldEntries internal) ∧
   PresenceNormalForm.All CommonNominalFullCarrier.model (patch oldEntries internal) atoms) publicModel) :
 Models privateNames (fun internal => Definitions oldEntries internal ∧
   GeneralNominalState.Models raw internal ∧ PresenceNormalForm.All CommonNominalFullCarrier.model internal atoms) publicModel :=
 (replacement_models_iff oldEntries newEntries oldCoherent oldExternal newCoherent newExternal within hidden
   _ (raw_atoms_congruent raw atoms) publicModel).mpr valid
end Yulang.GeneralNominalRebasePublicModel242
