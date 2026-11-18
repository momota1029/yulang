import Yulang.GeneralPresenceReserveBlock250
import Yulang.GeneralNominalPersistentOwner250
/-! Adding fresh private reserved cells to an arbitrary materialized frame
preserves projected models. Complete finite metadata support is checked;
allocated-key absence alone is not asserted to imply this protection. -/
namespace Yulang.GeneralNominalFrameReservation250
open Core.PresenceGeneration PresenceNormalForm
open GeneralNominalCommonBridge (Assignment)
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceOrderedRebase247
open GeneralPresenceReserveBlock250 (reserve)
open GeneralPresenceConsumerSupport246 (listTypedReads)
open GeneralNominalMaterializedOwnerFrame249 (Frame Models)
open GeneralNominalMaterializedSequenceModels249 (PublicModels)
open CommonNominalFullCarrier

def pool (frame : Frame) : List Nat :=
 GeneralNominalJournalSupport249.support frame.metadata ++
 listTypedReads (frame.consumers ++ block frame.definitions) ++
 GeneralPresenceReserveBlock250.support frame.definitions

def extend (frame : Frame) (names : List Nat) : Frame :=
 ⟨frame.metadata,frame.consumers,frame.definitions ++ reserve names⟩

def Fresh (frame : Frame) (names : List Nat) : Prop := ∀ name ∈ names, name ∉ pool frame

theorem keeps_pool (frame : Frame) (names : List Nat) (fresh : Fresh frame names)
 (assignment : Assignment) (name : Nat) (member : name ∈ pool frame) :
 solve model (reserve names) assignment name = assignment name := by
 apply solve_outside
 intro entry present equal
 exact fresh entry.1 ((GeneralPresenceReserveBlock250.member_iff names entry).mp present).1 (equal ▸ member)

theorem models_forward (frame : Frame) (names : List Nat) (fresh : Fresh frame names)
 (assignment : Assignment) (valid : Models frame assignment) :
 Models (extend frame names) (solve model (reserve names) assignment) := by
 have rows := solve_rows model (reserve names) assignment
 have metadataValid : frame.metadata.Models (solve model (reserve names) assignment) := by
   apply (GeneralNominalJournalSupport249.models_iff frame.metadata _ assignment rows ?_).mpr valid.1
   intro name member
   exact congrArg Prod.fst (keeps_pool frame names fresh assignment name (List.mem_append_left _ (List.mem_append_left _ member)))
 have ordinary : All model (solve model (reserve names) assignment) (frame.consumers ++ block frame.definitions) := by
   apply (GeneralPresenceConsumerSupport246.all_iff model _ assignment rows _ ?_).mpr valid.2
   intro name member
   exact congrArg Prod.fst (keeps_pool frame names fresh assignment name
     (List.mem_append_left _ (List.mem_append_right _ member)))
 have new := block_satisfied model subtype_refl (reserve names) (GeneralPresenceReserveBlock250.safe names) assignment
 refine ⟨metadataValid,?_⟩
 change All model _ (frame.consumers ++ block (frame.definitions ++ reserve names))
 simp only [block,List.flatMap_append,← List.append_assoc]
 exact (all_append model _ _ _).mpr ⟨ordinary,new⟩

theorem models_backward (frame : Frame) (names : List Nat) (assignment : Assignment)
 (valid : Models (extend frame names) assignment) : Models frame assignment := by
 refine ⟨valid.1,?_⟩
 have ordinary := valid.2
 change All model assignment (frame.consumers ++ block (frame.definitions ++ reserve names)) at ordinary
 simp only [block,List.flatMap_append,← List.append_assoc] at ordinary
 exact ((all_append model assignment _ _).mp ordinary).1

theorem safe_extend (frame : Frame) (safe : SafeOrder frame.definitions)
 (names : List Nat) (fresh : Fresh frame names) : SafeOrder (extend frame names).definitions := by
 apply GeneralPresenceReserveBlock250.append_safe frame.definitions safe names
 intro name member contained
 exact fresh name member (List.mem_append_right _ contained)

theorem public_models_iff (frame : Frame) (names : List Nat) (fresh : Fresh frame names)
 (shared : Nat → Prop) (privateNames : ∀ name ∈ names, ¬ shared name) (boundary : Assignment) :
 PublicModels frame shared boundary ↔ PublicModels (extend frame names) shared boundary := by
 constructor
 · rintro ⟨assignment,valid,agree⟩
   refine ⟨solve model (reserve names) assignment,models_forward frame names fresh assignment valid,?_⟩
   intro name sharedName
   rw [solve_outside model (reserve names) assignment name ?_]
   · exact agree name sharedName
   · intro entry present equal
     exact privateNames entry.1 ((GeneralPresenceReserveBlock250.member_iff names entry).mp present).1 (equal ▸ sharedName)
 · rintro ⟨assignment,valid,agree⟩
   exact ⟨assignment,models_backward frame names assignment valid,agree⟩
end Yulang.GeneralNominalFrameReservation250
