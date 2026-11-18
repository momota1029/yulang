import Yulang.GeneralNominalPostInstall250
/-! Finite execution with changing observations, packets, effects and ordinary
constraints. Conditions are evaluated on each computed fresh witness. The list
is supplied; this proves neither that source steps generate it nor Acc. -/
namespace Yulang.GeneralNominalFiniteInstallTrace250
open Core.PresenceGeneration PresenceNormalForm
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalMaterializedOwnerFrame249 (Frame Models)
open GeneralNominalMaterializedSequenceModels249 (PublicModels same_domain_protected subset_private)
open GeneralNominalJournalAppend250 (Delta attach)
open GeneralNominalPersistentOwner250 (Block update)
open GeneralPresenceOrderedBlock247 GeneralPresenceOrderedDependence247
open GeneralPresenceOrderedSubstitution247 GeneralPresenceOrderedRebase247
open GeneralNominalAssignmentCongruence238 (Same)
open CommonNominalFullCarrier GeneralPresenceCommonLaws245

structure Command where
 raw : Block
 delta : Delta

def advance (frame : Frame) (command : Command) : Frame := attach (update frame command.raw) command.delta

def nextAssignment (frame : Frame) (command : Command) (assignment : Assignment) : Assignment :=
 solve model (update frame command.raw).definitions assignment

def run : Frame → List Command → Frame
 | frame,[] => frame
 | frame,command :: rest => run (advance frame command) rest

def realize : Frame → List Command → Assignment → Assignment
 | _,[],assignment => assignment
 | frame,command :: rest,assignment => realize (advance frame command) rest (nextAssignment frame command assignment)

def Permitted : Frame → List Command → Assignment → Prop
 | _,[],_ => True
 | frame,command :: rest,assignment => command.delta.Holds (nextAssignment frame command assignment) ∧
   Permitted (advance frame command) rest (nextAssignment frame command assignment)

theorem next_same (frame : Frame) (command : Command) (first last : Assignment) (same : Same first last) :
 Same (nextAssignment frame command first) (nextAssignment frame command last) := by
 have result := GeneralNominalMaterializedDomain249.read_compatible
   (mapping (update frame command.raw).definitions) first last same
 rw [GeneralNominalOrderedRaw248.read_mapping,GeneralNominalOrderedRaw248.read_mapping] at result
 exact result

theorem permitted_iff (frame : Frame) (commands : List Command) (first last : Assignment) (same : Same first last) :
 Permitted frame commands first ↔ Permitted frame commands last := by
 induction commands generalizing frame first last with
 | nil => exact Iff.rfl
 | cons command rest ih =>
   exact and_congr (GeneralNominalPostInstall250.delta_iff command.delta _ _ (next_same frame command first last same))
     (ih (advance frame command) _ _ (next_same frame command first last same))

theorem targets_advance (frame : Frame) (command : Command) :
 (advance frame command).definitions.map Prod.fst = frame.definitions.map Prod.fst :=
 GeneralNominalPersistentOwner250.targets_update frame command.raw

theorem targets_run (frame : Frame) (commands : List Command) :
 (run frame commands).definitions.map Prod.fst = frame.definitions.map Prod.fst := by
 induction commands generalizing frame with
 | nil => rfl
 | cons command rest ih => exact (ih (advance frame command)).trans (targets_advance frame command)

theorem safe_advance (frame : Frame) (safe : SafeOrder frame.definitions) (command : Command) :
 SafeOrder (advance frame command).definitions := GeneralNominalPersistentOwner250.safe_update frame safe command.raw

theorem forward (frame : Frame) (safe : SafeOrder frame.definitions) (commands : List Command)
 (assignment : Assignment) (valid : Models frame assignment) (permitted : Permitted frame commands assignment) :
 Models (run frame commands) (realize frame commands assignment) := by
 induction commands generalizing frame assignment with
 | nil => exact valid
 | cons command rest ih =>
   apply ih (advance frame command) (safe_advance frame safe command) _ _ permitted.2
   apply (GeneralNominalJournalAppend250.attach_models _ _ _).mpr
   refine ⟨?_,permitted.1⟩
   exact GeneralNominalArbitraryOwnerFrame250.models_forward frame _ (safe_advance frame safe command)
     (same_domain_protected frame _ safe (GeneralPresencePersistentSnapshot250.refresh_within _ _)) assignment valid

theorem realize_outside (frame : Frame) (commands : List Command) (assignment : Assignment)
 (name : Nat) (outside : ∀ entry ∈ frame.definitions, entry.1 ≠ name) :
 realize frame commands assignment name = assignment name := by
 induction commands generalizing frame assignment with
 | nil => rfl
 | cons command rest ih =>
   have freshOutside := subset_private frame.definitions (update frame command.raw).definitions
     (GeneralPresencePersistentSnapshot250.refresh_within _ _) (fun n => n = name)
     (fun n equal => equal ▸ outside) name rfl
   exact (ih (advance frame command) (nextAssignment frame command assignment) freshOutside).trans
     (solve_outside model _ assignment name freshOutside)

theorem backward (frame : Frame) (safe : SafeOrder frame.definitions) (commands : List Command)
 (shared : Nat → Prop)
 (privateNames : ∀ name, shared name → ∀ entry ∈ frame.definitions, entry.1 ≠ name)
 (boundary : Assignment) (result : PublicModels (run frame commands) shared boundary) :
 ∃ assignment, Models frame assignment ∧ Permitted frame commands assignment ∧ Agrees model shared assignment boundary := by
 induction commands generalizing frame with
 | nil => obtain ⟨a,valid,agree⟩ := result; exact ⟨a,valid,True.intro,agree⟩
 | cons command rest ih =>
   have freshSafe := safe_advance frame safe command
   have within := GeneralPresencePersistentSnapshot250.refresh_within frame.definitions command.raw
   have nextPrivate := subset_private _ _ within shared privateNames
   obtain ⟨a,valid,tail,agree⟩ := ih (advance frame command) freshSafe nextPrivate result
   obtain ⟨updated,extra⟩ := (GeneralNominalJournalAppend250.attach_models _ _ _).mp valid
   let previous := solve model frame.definitions a
   have restored : nextAssignment frame command previous = nextAssignment frame command a :=
     solve_absorbs model _ frame.definitions freshSafe (GeneralPresencePersistentSnapshot250.old_within _ _) a
   have same : Same (nextAssignment frame command previous) a := by
     rw [restored]
     exact GeneralPresenceOrderedRecovery247.solve_compatible model common_laws _ a
       ((all_append model a _ _).mp updated.2).2
   refine ⟨previous,GeneralNominalMaterializedOwnerFrame249.models_backward frame safe _ a updated,?_,?_⟩
   · exact ⟨(GeneralNominalPostInstall250.delta_iff command.delta _ a same).mpr extra,
       (permitted_iff (advance frame command) rest _ a same).mpr tail⟩
   · intro name sharedName
     change solve model frame.definitions a name = boundary name
     rw [solve_outside model frame.definitions a name (privateNames name sharedName)]
     exact agree name sharedName

theorem public_run_iff (frame : Frame) (safe : SafeOrder frame.definitions) (commands : List Command)
 (shared : Nat → Prop)
 (privateNames : ∀ name, shared name → ∀ entry ∈ frame.definitions, entry.1 ≠ name)
 (boundary : Assignment) :
 (∃ assignment, Models frame assignment ∧ Permitted frame commands assignment ∧ Agrees model shared assignment boundary) ↔
 PublicModels (run frame commands) shared boundary := by
 constructor
 · rintro ⟨a,valid,permitted,agree⟩
   refine ⟨realize frame commands a,forward frame safe commands a valid permitted,?_⟩
   intro name sharedName
   rw [realize_outside frame commands a name (privateNames name sharedName)]
   exact agree name sharedName
 · exact backward frame safe commands shared privateNames boundary
end Yulang.GeneralNominalFiniteInstallTrace250
