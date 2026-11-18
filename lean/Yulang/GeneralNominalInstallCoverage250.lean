import Yulang.GeneralNominalFiniteInstallTrace250
import Yulang.GeneralNominalStableSlots250
/-! Coverage is separate from public model preservation: out-of-domain targets
and conflicting duplicate RHSs must not disappear silently. Concrete stable
owner commands supply both properties for every step of their finite trace. -/
namespace Yulang.GeneralNominalInstallCoverage250
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOwnerRewrite244
open GeneralPresenceOrderedBlock247 GeneralPresenceOrderedDependence247
open GeneralNominalMaterializedOwnerFrame249 (Frame)
open GeneralNominalFiniteInstallTrace250
open GeneralNominalJournalAppend250 (Delta)
open CommonNominalFullCarrier

def Covered (frame : Frame) : List Command → Prop
 | [] => True
 | command :: rest => TargetsWithin command.raw frame.definitions ∧ Coherent command.raw ∧ Covered (advance frame command) rest

theorem within_equal_targets (raw old fresh : List (Entry Nat))
 (equal : fresh.map Prod.fst = old.map Prod.fst) (within : TargetsWithin raw old) : TargetsWithin raw fresh := by
 intro entry member
 obtain ⟨original,present,equalName⟩ := within entry member
 have found : entry.1 ∈ old.map Prod.fst := List.mem_map.mpr ⟨original,present,equalName⟩
 rw [← equal] at found
 exact List.mem_map.mp found

theorem covered_from_initial (frame : Frame) (commands : List Command)
 (within : ∀ command ∈ commands, TargetsWithin command.raw frame.definitions)
 (coherent : ∀ command ∈ commands, Coherent command.raw) : Covered frame commands := by
 induction commands generalizing frame with
 | nil => trivial
 | cons command rest ih =>
   refine ⟨within command (by simp),coherent command (by simp),?_⟩
   apply ih (advance frame command)
   · intro next member
     exact within_equal_targets _ _ _ (targets_advance frame command) (within next (by simp [member]))
   · intro next member; exact coherent next (by simp [member])

theorem next_raw_satisfied (frame : Frame) (safe : SafeOrder frame.definitions) (command : Command)
 (within : TargetsWithin command.raw frame.definitions) (coherent : Coherent command.raw)
 (assignment : GeneralNominalCommonBridge.Assignment) :
 All model (nextAssignment frame command assignment)
   (block (transform (GeneralPresenceOrderedSubstitution247.mapping frame.definitions) command.raw)) :=
 GeneralPresencePersistentSnapshot250.raw_equations _ _ within coherent model _
   (block_satisfied model subtype_refl _ (safe_advance frame safe command) assignment)

structure OwnerCommand where
 bindings : GeneralNominalAllocation.Bindings
 delta : Delta

def compile (seed root declaration : Nat) (names : List Nat) (command : OwnerCommand) : Command :=
 ⟨GeneralNominalRebaseDefinitions241.entries seed root declaration command.bindings names,command.delta⟩

def commands (seed root declaration : Nat) (names : List Nat) (source : List OwnerCommand) : List Command :=
 source.map (compile seed root declaration names)

theorem owner_trace_covered (frame : Frame) (seed root declaration : Nat) (names : List Nat) (source : List OwnerCommand) :
 Covered (GeneralNominalFrameReservation250.extend frame (GeneralNominalStableSlots250.slots seed root declaration names))
   (commands seed root declaration names source) := by
 apply covered_from_initial
 · intro command member
   obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
   exact GeneralNominalStableSlots250.entries_covered frame seed root declaration names original.bindings
 · intro command member
   obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
   exact GeneralNominalRebaseDefinitions241.coherent seed root declaration original.bindings names

def coverageCheck (old raw : List (Entry Nat)) : Bool :=
 raw.all (fun entry => (old.map Prod.fst).contains entry.1)

theorem coverageCheck_exact (old raw : List (Entry Nat)) : coverageCheck old raw = true ↔ TargetsWithin raw old := by
 simp only [coverageCheck,List.all_eq_true,List.contains_iff_mem,List.mem_map,TargetsWithin]

theorem owner_check_success (frame : Frame) (seed root declaration : Nat) (names : List Nat)
 (bindings : GeneralNominalAllocation.Bindings) :
 coverageCheck (GeneralNominalFrameReservation250.extend frame (GeneralNominalStableSlots250.slots seed root declaration names)).definitions
   (GeneralNominalRebaseDefinitions241.entries seed root declaration bindings names) = true :=
 (coverageCheck_exact _ _).mpr (GeneralNominalStableSlots250.entries_covered frame seed root declaration names bindings)
end Yulang.GeneralNominalInstallCoverage250
