import Yulang.GeneralNominalInstallCoverage250
import Yulang.GeneralPresenceOrderedCheck247
/-! Executable certificate checks prevent dropping uncovered targets or
conflicting duplicates. None is an internal preparation failure, not a source
language rejection. Concrete covered owner traces always pass these checks. -/
namespace Yulang.GeneralNominalCheckedInstall250
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOwnerRewrite244
open GeneralPresenceOrderedBlock247 GeneralPresenceOrderedDependence247
open GeneralNominalMaterializedOwnerFrame249 (Frame)
open GeneralNominalFiniteInstallTrace250 (Command advance)
open GeneralNominalInstallCoverage250 (Covered coverageCheck)

def coherenceCheck (raw : List (Entry Nat)) : Bool :=
 raw.all (fun a => raw.all (fun b => if a.1 = b.1 then decide (a.2 = b.2) else true))

theorem coherenceCheck_exact (raw : List (Entry Nat)) : coherenceCheck raw = true ↔ Coherent raw := by
 simp only [coherenceCheck,List.all_eq_true,Coherent]
 apply forall_congr'; intro a
 apply forall_congr'; intro am
 apply forall_congr'; intro b
 apply forall_congr'; intro bm
 by_cases equal : a.1 = b.1 <;> simp [equal]

def check (frame : Frame) (command : Command) : Bool :=
 GeneralPresenceOrderedCheck247.check frame.definitions && coverageCheck frame.definitions command.raw && coherenceCheck command.raw

theorem check_exact (frame : Frame) (command : Command) : check frame command = true ↔
 SafeOrder frame.definitions ∧ TargetsWithin command.raw frame.definitions ∧ Coherent command.raw := by
 simp [check,GeneralPresenceOrderedCheck247.check_exact,GeneralNominalInstallCoverage250.coverageCheck_exact,coherenceCheck_exact,and_assoc]

def step (frame : Frame) (command : Command) : Option Frame :=
 if check frame command then some (advance frame command) else none

theorem step_success (frame : Frame) (command : Command) (safe : SafeOrder frame.definitions)
 (within : TargetsWithin command.raw frame.definitions) (coherent : Coherent command.raw) :
 step frame command = some (advance frame command) := by
 simp [step,(check_exact frame command).mpr ⟨safe,within,coherent⟩]

def run : Frame → List Command → Option Frame
 | frame,[] => some frame
 | frame,command :: rest => (step frame command).bind (fun next => run next rest)

theorem run_success (frame : Frame) (safe : SafeOrder frame.definitions) (commands : List Command)
 (covered : Covered frame commands) :
 run frame commands = some (GeneralNominalFiniteInstallTrace250.run frame commands) := by
 induction commands generalizing frame with
 | nil => rfl
 | cons command rest ih =>
   rw [run,step_success frame command safe covered.1 covered.2.1]
   exact ih (advance frame command) (GeneralNominalFiniteInstallTrace250.safe_advance frame safe command) covered.2.2

theorem run_sound (frame : Frame) (commands : List Command) (result : Frame) (success : run frame commands = some result) :
 result = GeneralNominalFiniteInstallTrace250.run frame commands ∧ Covered frame commands := by
 induction commands generalizing frame with
 | nil => exact ⟨(Option.some.inj success).symm,True.intro⟩
 | cons command rest ih =>
   unfold run step at success
   split at success
   · rename_i checked
     have good := (check_exact frame command).mp checked
     obtain ⟨equal,covered⟩ := ih (advance frame command) success
     exact ⟨equal,good.2.1,good.2.2,covered⟩
   · simp at success
end Yulang.GeneralNominalCheckedInstall250
