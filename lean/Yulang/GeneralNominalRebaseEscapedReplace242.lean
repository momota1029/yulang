import Yulang.GeneralNominalRebaseEscapedProjection242
set_option backward.isDefEq.respectTransparency false
/-! A replacement producer for finite ordinary consumers that escape into
private target cells. Old consumers are retained by old-definition inlining. -/
namespace Yulang.GeneralNominalRebaseEscapedReplace242
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalFiniteEquationRealization236
open GeneralNominalRebaseInline241
open GeneralNominalRebaseEscapedProjection242
open CommonNominalFullCarrier

theorem patch_congr (entries : List Entry) (coherent : Coherent entries)
 (external : External entries) (first last : Assignment)
 (kept : Preserves entries first last) : patch entries first = patch entries last := by
 classical
 funext name
 apply Prod.ext
 · by_cases found : ∃ entry ∈ entries, entry.1 = name
   · obtain ⟨entry,member,rfl⟩ := found
     rw [value entries coherent entry member,value entries coherent entry member]
     exact GeneralNominalCenteredModelExtension.type_eval_same entry.2
       (fun source present => kept.1 source (external entry member source present))
   · have absent : ∀ entry ∈ entries, entry.1 ≠ name :=
       fun entry member equal => found ⟨entry,member,equal⟩
     rw [outside entries absent,outside entries absent,kept.1 name absent]
 · rw [row entries name,row entries name]
   exact kept.2 name

theorem inline_congr (entries : List Entry) (coherent : Coherent entries)
 (external : External entries) (atoms : List (PresenceNormalForm.Atom Nat))
 (first last : Assignment) (kept : Preserves entries first last) :
 PresenceNormalForm.All CommonNominalFullCarrier.model first
   (atoms.map (atomSubst (substitution entries))) ↔
 PresenceNormalForm.All CommonNominalFullCarrier.model last
   (atoms.map (atomSubst (substitution entries))) := by
 rw [all_inline coherent atoms first,all_inline coherent atoms last,
   patch_congr entries coherent external first last kept]

def TargetsWithin (newEntries oldEntries : List Entry) : Prop :=
 ∀ entry ∈ newEntries, ∃ old ∈ oldEntries, old.1 = entry.1

theorem new_patch_preserves (oldEntries newEntries : List Entry)
 (within : TargetsWithin newEntries oldEntries) (model : Assignment) :
 Preserves oldEntries (patch newEntries model) model := by
 refine ⟨?_,fun name => row newEntries name⟩
 intro name absent
 apply outside
 intro entry member same
 obtain ⟨old,present,equal⟩ := within entry member
 exact absent old present (equal.trans same)

theorem new_extension (oldEntries newEntries : List Entry)
 (oldCoherent : Coherent oldEntries) (oldExternal : External oldEntries)
 (newCoherent : Coherent newEntries) (newExternal : External newEntries)
 (within : TargetsWithin newEntries oldEntries)
 (atoms : List (PresenceNormalForm.Atom Nat)) (model : Assignment)
 (consumers : PresenceNormalForm.All CommonNominalFullCarrier.model model
   (atoms.map (atomSubst (substitution oldEntries)))) :
 ∃ extension, Preserves oldEntries extension model ∧ Definitions newEntries extension ∧
 PresenceNormalForm.All CommonNominalFullCarrier.model extension
   (atoms.map (atomSubst (substitution oldEntries))) := by
 have kept := new_patch_preserves oldEntries newEntries within model
 exact ⟨patch newEntries model,kept,patch_definitions newEntries newCoherent newExternal model,
   (inline_congr oldEntries oldCoherent oldExternal atoms _ model kept).mpr consumers⟩

/-- Both sides quantify over private types. This is not same-assignment model
inclusion. New and old defining equations are never conjoined. -/
theorem replacement_projection_iff (oldEntries newEntries : List Entry)
 (oldCoherent : Coherent oldEntries) (oldExternal : External oldEntries)
 (newCoherent : Coherent newEntries) (newExternal : External newEntries)
 (within : TargetsWithin newEntries oldEntries)
 (atoms : List (PresenceNormalForm.Atom Nat)) (model : Assignment) :
 (∃ old, Preserves oldEntries old model ∧ Definitions oldEntries old ∧
   PresenceNormalForm.All CommonNominalFullCarrier.model old atoms) ↔
 (∃ next, Preserves oldEntries next model ∧ Definitions newEntries next ∧
   PresenceNormalForm.All CommonNominalFullCarrier.model next
     (atoms.map (atomSubst (substitution oldEntries)))) := by
 rw [projected_iff oldEntries oldCoherent oldExternal atoms model]
 constructor
 · exact new_extension oldEntries newEntries oldCoherent oldExternal newCoherent newExternal within atoms model
 · rintro ⟨next,kept,_,consumers⟩
   exact (inline_congr oldEntries oldCoherent oldExternal atoms next model kept).mp consumers
end Yulang.GeneralNominalRebaseEscapedReplace242
