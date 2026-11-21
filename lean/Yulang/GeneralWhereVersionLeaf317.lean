import Yulang.GeneralWhereVersionLeafFresh317
import Yulang.GeneralWhereVersionLeafProof317

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 31000
set_option maxHeartbeats 39000000
namespace Yulang.GeneralWhereVersionLeaf317
open GeneralDictionaryJournalRefinement228Source (roles)
open GeneralLiveCompoundRegistry316 (registry sourceRegistry leaf checked leaf_checked declaration)
open GeneralWhereVersionCase317 (occ site)
open GeneralWhereVersionBase317 (loSlot hiSlot)
open GeneralWhereVersionSnapshot317 (context)
open GeneralWhereVersionCommit317 (core framedState terminal_outputs)
open GeneralWhereVersionWitness317 (ParentHolds)
open GeneralWhereVersionLeafHead317 (packet plan located)
open GeneralWhereVersionLeafFresh317 (prepared known)
open GeneralWhereVersionLeafProof317 (holds terminal)
open GeneralNominalVersionedCandidates231 (Survivor Unique)
open GeneralNominalVersionedEvidence231 (Frame Certificate Evidence)
open GeneralNominalCommonBridge (Assignment)

theorem frame (m : Assignment) (valid : ParentHolds m) : Frame registry core occ leaf.id plan :=
  ⟨rfl,rfl,rfl,rfl,List.mem_append_right _ (List.mem_singleton_self _),
    List.mem_append_right _ (List.mem_singleton_self _),
    List.mem_cons_of_mem _ (List.mem_singleton_self _),rfl,located,prepared m valid⟩

theorem survivor (m : Assignment) (valid : ParentHolds m) : Survivor registry context occ leaf.id [] :=
  ⟨known,leaf,List.mem_cons_of_mem _ (List.mem_singleton_self _),leaf_checked,rfl,rfl,
    [(loSlot,hiSlot)],located,prepared m valid,terminal.symm⟩

theorem unique (m : Assignment) (valid : ParentHolds m) : Unique registry context occ leaf.id [] := by
  refine ⟨survivor m valid,?_⟩
  intro other kids candidate
  have copy := candidate
  obtain ⟨_,d,visible,_,key,role,_,_,_,_⟩ := copy
  rcases List.mem_cons.mp visible with eq|last
  · subst d
    have clash : (0 : Nat) = 1 := role
    cases clash
  · cases List.mem_singleton.mp last
    subst other
    exact ⟨rfl,GeneralNominalVersionedCandidates231.survivor_children_functional checked candidate (survivor m valid)⟩

theorem certificate (m : Assignment) (valid : ParentHolds m) : Certificate registry core m occ leaf.id [] plan :=
  ⟨frame m valid,terminal.symm,holds m valid,(by intro out bad; rw [terminal_outputs] at bad; cases bad)⟩

theorem evidence (m : Assignment) (valid : ParentHolds m) : Evidence registry core m occ (.node leaf.id []) :=
  GeneralNominalVersionedEvidence231.evidence_leaf ⟨plan,certificate m valid⟩

end Yulang.GeneralWhereVersionLeaf317
