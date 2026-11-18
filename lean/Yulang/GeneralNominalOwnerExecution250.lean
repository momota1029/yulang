import Yulang.GeneralNominalOwnerOpening250
import Yulang.GeneralNominalCheckedInstall250
/-! A complete finite owner-transformer pipeline: choose private slots once,
compile concrete merge commands, check their coverage/coherence, execute and
preserve projected solutions with every new metadata obligation explicit.
This is not the source scheduler or an unconditional acceptance theorem. -/
namespace Yulang.GeneralNominalOwnerExecution250
open Core.PresenceGeneration PresenceNormalForm
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalMaterializedOwnerFrame249 (Frame Models)
open GeneralNominalMaterializedSequenceModels249 (PublicModels)
open GeneralNominalOwnerOpening250 (Handle choose openFrame)
open GeneralNominalInstallCoverage250 (OwnerCommand commands Covered)
open GeneralNominalFiniteInstallTrace250 (Permitted)
open GeneralPresenceOrderedBlock247 GeneralPresenceOrderedRebase247
open GeneralPresenceReserveBlock250 (reserve)
open CommonNominalFullCarrier GeneralPresenceCommonLaws245

def program (handle : Handle) (source : List OwnerCommand) : List GeneralNominalFiniteInstallTrace250.Command :=
 commands handle.seed handle.root handle.declaration handle.names source

def result (frame : Frame) (handle : Handle) (source : List OwnerCommand) : Frame :=
 GeneralNominalFiniteInstallTrace250.run (openFrame frame handle) (program handle source)

def seedAssignment (handle : Handle) (assignment : Assignment) : Assignment := solve model (reserve handle.slots) assignment

theorem covered (frame : Frame) (handle : Handle) (source : List OwnerCommand) :
 Covered (openFrame frame handle) (program handle source) :=
 GeneralNominalInstallCoverage250.owner_trace_covered frame handle.seed handle.root handle.declaration handle.names source

theorem checked_success (frame : Frame) (safe : SafeOrder frame.definitions)
 (root declaration : Nat) (names shared : List Nat) (source : List OwnerCommand) :
 GeneralNominalCheckedInstall250.run (openFrame frame (choose frame root declaration names shared))
   (program (choose frame root declaration names shared) source) =
 some (result frame (choose frame root declaration names shared) source) :=
 GeneralNominalCheckedInstall250.run_success _
   (GeneralNominalOwnerOpening250.open_safe frame safe root declaration names shared) _ (covered _ _ _)

theorem public_execution_iff (frame : Frame) (safe : SafeOrder frame.definitions)
 (root declaration : Nat) (names shared : List Nat) (source : List OwnerCommand)
 (oldPrivate : ∀ name ∈ shared, ∀ entry ∈ frame.definitions, entry.1 ≠ name) (boundary : Assignment) :
 (∃ assignment, Models frame assignment ∧
   Permitted (openFrame frame (choose frame root declaration names shared))
     (program (choose frame root declaration names shared) source)
     (seedAssignment (choose frame root declaration names shared) assignment) ∧
   Agrees model (fun name => name ∈ shared) assignment boundary) ↔
 PublicModels (result frame (choose frame root declaration names shared) source)
   (fun name => name ∈ shared) boundary := by
 let handle := choose frame root declaration names shared
 have fresh := GeneralNominalOwnerOpening250.fresh frame root declaration names shared
 have privateSlots := GeneralNominalOwnerOpening250.private_names frame root declaration names shared
 have allPrivate : ∀ name ∈ shared, ∀ entry ∈ (openFrame frame handle).definitions, entry.1 ≠ name := by
   intro name member entry present
   rcases List.mem_append.mp present with present | present
   · exact oldPrivate name member entry present
   · intro equal
     exact privateSlots entry.1 ((GeneralPresenceReserveBlock250.member_iff _ _).mp present).1 (equal ▸ member)
 have trace := GeneralNominalFiniteInstallTrace250.public_run_iff (openFrame frame handle)
   (GeneralNominalOwnerOpening250.open_safe frame safe root declaration names shared)
   (program handle source) (fun name => name ∈ shared) allPrivate boundary
 constructor
 · rintro ⟨assignment,valid,permitted,agree⟩
   apply trace.mp
   refine ⟨seedAssignment handle assignment,
     GeneralNominalFrameReservation250.models_forward frame handle.slots fresh assignment valid,permitted,?_⟩
   intro name member
   rw [seedAssignment,solve_outside model (reserve handle.slots) assignment name ?_]
   · exact agree name member
   · intro entry present equal
     exact privateSlots entry.1 ((GeneralPresenceReserveBlock250.member_iff _ _).mp present).1 (equal ▸ member)
 · intro final
   obtain ⟨assignment,valid,permitted,agree⟩ := trace.mpr final
   refine ⟨assignment,GeneralNominalFrameReservation250.models_backward frame handle.slots assignment valid,?_,agree⟩
   apply (GeneralNominalFiniteInstallTrace250.permitted_iff (openFrame frame handle) (program handle source)
     (seedAssignment handle assignment) assignment ?_).mpr permitted
   apply GeneralPresenceOrderedRecovery247.solve_compatible model common_laws (reserve handle.slots) assignment
   have ordinary := valid.2
   change All model assignment (frame.consumers ++ GeneralPresenceDefinitionRewrite244.block (frame.definitions ++ reserve handle.slots)) at ordinary
   simp only [GeneralPresenceDefinitionRewrite244.block,List.flatMap_append,← List.append_assoc] at ordinary
   exact ((all_append model assignment _ _).mp ordinary).2
end Yulang.GeneralNominalOwnerExecution250
