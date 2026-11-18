import Yulang.GeneralNominalRegisteredPlan251
/-! Supplied finite plan lists are compiled against each evolving frame.
This is not a proof that source execution generates finitely many plans. -/
namespace Yulang.GeneralNominalPlanTrace251
open GeneralNominalCenters (Plan)
open GeneralNominalMaterializedOwnerFrame249 (Frame)
open GeneralNominalOwnerOpening250 (Handle)
open GeneralNominalOwnerRegistry250 (Registered lookup)
open GeneralNominalFiniteInstallTrace250 (Command advance run)
open GeneralNominalInstallCoverage250 (Covered)
open GeneralPresenceOrderedBlock247

def compile (frame : Frame) (handles : List Handle) : List (Plan roles) → Option (List Command)
 | [] => some []
 | plan :: rest => (GeneralNominalRegisteredPlan251.compile plan frame handles).bind fun prepared =>
   (compile (advance frame prepared.2) handles rest).map (prepared.2 :: ·)

theorem covered (frame : Frame) (handles : List Handle) (registered : Registered frame handles)
 (plans : List (Plan roles)) (commands : List Command) (success : compile frame handles plans = some commands) :
 Covered frame commands := by
 induction plans generalizing frame commands with
 | nil => simp [compile] at success; subst commands; trivial
 | cons plan rest ih =>
   cases found : GeneralNominalRegisteredPlan251.compile plan frame handles with
   | none => simp [compile,found] at success
   | some prepared =>
     cases tail : compile (advance frame prepared.2) handles rest with
     | none => simp [compile,found,tail] at success
     | some commandsTail =>
       simp only [compile,found,Option.bind_some,tail,Option.map_some,Option.some.injEq] at success
       subst commands
       have valid := GeneralNominalRegisteredPlan251.covered plan frame handles registered prepared.1 prepared.2 found
       exact ⟨valid.1,valid.2,ih _ (GeneralNominalRegisteredPlan251.retains_registry frame handles registered prepared.2) _ tail⟩

theorem checked_success (frame : Frame) (safe : SafeOrder frame.definitions) (handles : List Handle)
 (registered : Registered frame handles) (plans : List (Plan roles)) (commands : List Command)
 (success : compile frame handles plans = some commands) :
 GeneralNominalCheckedInstall250.run frame commands = some (run frame commands) :=
 GeneralNominalCheckedInstall250.run_success frame safe commands (covered frame handles registered plans commands success)

def Known (handles : List Handle) (plans : List (Plan roles)) : Prop :=
 ∀ plan ∈ plans, ∃ handle,
 lookup handles plan.packet.site.occurrence.identity plan.packet.declaration.id = some handle ∧
 handle.names = plan.packet.declaration.inputNames

theorem total_on_known (frame : Frame) (handles : List Handle) (plans : List (Plan roles)) (known : Known handles plans) :
 ∃ commands, compile frame handles plans = some commands := by
 induction plans generalizing frame with
 | nil => exact ⟨[],rfl⟩
 | cons plan rest ih =>
   obtain ⟨handle,found,names⟩ := known plan (by simp)
   have prepared := GeneralNominalRegisteredPlan251.compile_success plan frame handles handle found names
   obtain ⟨commands,tail⟩ := ih (advance frame (GeneralNominalRegisteredPlan251.build plan frame handle))
     (fun p member => known p (List.mem_cons_of_mem _ member))
   exact ⟨GeneralNominalRegisteredPlan251.build plan frame handle :: commands,by simp [compile,prepared,tail]⟩

theorem length_exact (frame : Frame) (handles : List Handle) (plans : List (Plan roles)) (commands : List Command)
 (success : compile frame handles plans = some commands) : commands.length = plans.length := by
 induction plans generalizing frame commands with
 | nil => simp [compile] at success; subst commands; rfl
 | cons plan rest ih =>
   cases found : GeneralNominalRegisteredPlan251.compile plan frame handles with
   | none => simp [compile,found] at success
   | some prepared =>
     cases tail : compile (advance frame prepared.2) handles rest with
     | none => simp [compile,found,tail] at success
     | some commandsTail =>
       simp only [compile,found,Option.bind_some,tail,Option.map_some,Option.some.injEq] at success
       subst commands
       exact congrArg Nat.succ (ih _ _ tail)

theorem fixed_targets (frame : Frame) (_handles : List Handle) (_plans : List (Plan roles)) (commands : List Command) :
 (run frame commands).definitions.map Prod.fst = frame.definitions.map Prod.fst :=
 GeneralNominalFiniteInstallTrace250.targets_run frame commands
end Yulang.GeneralNominalPlanTrace251
