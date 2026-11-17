import Yulang.GeneralNominalRebaseEscapedReplace242
import Yulang.GeneralNominalRawCongruence238
set_option backward.isDefEq.respectTransparency false
/-! Semantic pullback for all raw consumers, including nominal descriptors.
No executable raw State rewrite is constructed by this interpretation. -/
namespace Yulang.GeneralNominalRebaseRawProjection242
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalFiniteEquationRealization236
open GeneralNominalRebaseEscapedProjection242
open GeneralNominalRebaseEscapedReplace242

def Congruent (retained : Assignment → Prop) : Prop :=
 ∀ first last, GeneralNominalAssignmentCongruence238.Same first last →
   (retained first ↔ retained last)

theorem predicate_projection (entries : List Entry) (coherent : Coherent entries)
 (external : External entries) (retained : Assignment → Prop) (congruent : Congruent retained)
 (model : Assignment) :
 (∃ extension, Preserves entries extension model ∧ Definitions entries extension ∧ retained extension) ↔
 retained (patch entries model) := by
 constructor
 · rintro ⟨extension,kept,definitions,valid⟩
   exact (congruent extension (patch entries model)
     (extension_same entries coherent external extension model kept definitions)).mp valid
 · intro valid
   exact ⟨patch entries model,patch_preserves entries model,
     patch_definitions entries coherent external model,valid⟩

theorem predicate_replacement (oldEntries newEntries : List Entry)
 (oldCoherent : Coherent oldEntries) (oldExternal : External oldEntries)
 (newCoherent : Coherent newEntries) (newExternal : External newEntries)
 (within : TargetsWithin newEntries oldEntries)
 (retained : Assignment → Prop) (congruent : Congruent retained) (model : Assignment) :
 (∃ old, Preserves oldEntries old model ∧ Definitions oldEntries old ∧ retained old) ↔
 (∃ next, Preserves oldEntries next model ∧ Definitions newEntries next ∧
   retained (patch oldEntries next)) := by
 rw [predicate_projection oldEntries oldCoherent oldExternal retained congruent model]
 constructor
 · intro valid
   have kept := new_patch_preserves oldEntries newEntries within model
   refine ⟨patch newEntries model,kept,patch_definitions newEntries newCoherent newExternal model,?_⟩
   rw [patch_congr oldEntries oldCoherent oldExternal _ model kept]
   exact valid
 · rintro ⟨next,kept,_,valid⟩
   rw [patch_congr oldEntries oldCoherent oldExternal next model kept] at valid
   exact valid

def RawInline (entries : List Entry) (raw : GeneralNominalState.State) (model : Assignment) : Prop :=
 GeneralNominalState.Models raw (patch entries model)

theorem raw_congruent (raw : GeneralNominalState.State) : Congruent (GeneralNominalState.Models raw) :=
 fun _ _ same => GeneralNominalRawCongruence238.models_iff raw same

theorem raw_projection (entries : List Entry) (coherent : Coherent entries)
 (external : External entries) (raw : GeneralNominalState.State) (model : Assignment) :
 (∃ extension, Preserves entries extension model ∧ Definitions entries extension ∧
   GeneralNominalState.Models raw extension) ↔ RawInline entries raw model :=
 predicate_projection entries coherent external _ (raw_congruent raw) model

theorem raw_replacement (oldEntries newEntries : List Entry)
 (oldCoherent : Coherent oldEntries) (oldExternal : External oldEntries)
 (newCoherent : Coherent newEntries) (newExternal : External newEntries)
 (within : TargetsWithin newEntries oldEntries) (raw : GeneralNominalState.State) (model : Assignment) :
 (∃ old, Preserves oldEntries old model ∧ Definitions oldEntries old ∧ GeneralNominalState.Models raw old) ↔
 (∃ next, Preserves oldEntries next model ∧ Definitions newEntries next ∧ RawInline oldEntries raw next) :=
 predicate_replacement oldEntries newEntries oldCoherent oldExternal newCoherent newExternal within
   _ (raw_congruent raw) model

theorem raw_atoms_congruent (raw : GeneralNominalState.State) (atoms : List (PresenceNormalForm.Atom Nat)) :
 Congruent (fun model => GeneralNominalState.Models raw model ∧
   PresenceNormalForm.All CommonNominalFullCarrier.model model atoms) :=
 fun _ _ same => and_congr (GeneralNominalRawCongruence238.models_iff raw same)
   (GeneralNominalAssignmentCongruence238.all_iff same atoms)

theorem raw_atoms_replacement (oldEntries newEntries : List Entry)
 (oldCoherent : Coherent oldEntries) (oldExternal : External oldEntries)
 (newCoherent : Coherent newEntries) (newExternal : External newEntries)
 (within : TargetsWithin newEntries oldEntries)
 (raw : GeneralNominalState.State) (atoms : List (PresenceNormalForm.Atom Nat)) (model : Assignment) :
 (∃ old, Preserves oldEntries old model ∧ Definitions oldEntries old ∧
   GeneralNominalState.Models raw old ∧ PresenceNormalForm.All CommonNominalFullCarrier.model old atoms) ↔
 (∃ next, Preserves oldEntries next model ∧ Definitions newEntries next ∧
   RawInline oldEntries raw next ∧ PresenceNormalForm.All CommonNominalFullCarrier.model next
     (atoms.map (GeneralNominalRebaseInline241.atomSubst (GeneralNominalRebaseInline241.substitution oldEntries)))) := by
 have base := predicate_replacement oldEntries newEntries oldCoherent oldExternal newCoherent
   newExternal within _ (raw_atoms_congruent raw atoms) model
 constructor
 · intro valid
   obtain ⟨next,kept,definitions,rawValid,atomValid⟩ := base.mp valid
   exact ⟨next,kept,definitions,rawValid,
     (GeneralNominalRebaseInline241.all_inline oldCoherent atoms next).mpr atomValid⟩
 · rintro ⟨next,kept,definitions,rawValid,atomValid⟩
   exact base.mpr ⟨next,kept,definitions,rawValid,
     (GeneralNominalRebaseInline241.all_inline oldCoherent atoms next).mp atomValid⟩
end Yulang.GeneralNominalRebaseRawProjection242
