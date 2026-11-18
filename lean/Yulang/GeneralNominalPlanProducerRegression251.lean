import Yulang.GeneralNominalPlanTraceModels251
import Yulang.GeneralDictionaryOptionalInstall229
import Yulang.GeneralNominalPostInstallRegression250
/-! An actual checked Plan traverses the finite preparation pipeline twice.
These are structural/compiler regressions, not source acceptance claims. -/
namespace Yulang.GeneralNominalPlanProducerRegression251
open Core.PresenceGeneration
open GeneralNominalMaterializedOwnerFrame249 (Frame)
open GeneralNominalOwnerRegistry250 (Registered)
open GeneralNominalFiniteInstallTrace250 (Command)
open GeneralPresenceOrderedBlock247
abbrev plan := GeneralDictionaryOptionalInstall229.plan

def frame : Frame := ⟨GeneralNominalPostInstallRegression250.emptyJournal,[],[]⟩
def handle := GeneralNominalPlanProducer251.handle plan frame []
def initial := GeneralNominalPlanProducer251.opened plan frame []

theorem frame_safe : SafeOrder frame.definitions := by simp [frame,SafeOrder]

theorem initial_safe : SafeOrder initial.definitions :=
 GeneralNominalPlanProducer251.safe plan frame frame_safe []

theorem registered : Registered initial [handle] :=
 GeneralNominalOwnerRegistry250.new_registered frame [] (by intro _ member; cases member) handle

theorem same_owner : GeneralNominalPlanTrace251.Known [handle] [plan,plan] := by
 intro selected member
 simp only [List.mem_cons,List.not_mem_nil,or_false] at member
 have equal : selected = plan := member.elim id id
 subst selected
 refine ⟨handle,?_,rfl⟩
 exact GeneralNominalOwnerRegistry250.lookup_head handle []

theorem two_plans_compile : ∃ commands,
 GeneralNominalPlanTrace251.compile initial [handle] [plan,plan] = some commands ∧ commands.length = 2 ∧
 GeneralNominalCheckedInstall250.run initial commands = some (GeneralNominalFiniteInstallTrace250.run initial commands) := by
 obtain ⟨commands,compiled⟩ := GeneralNominalPlanTrace251.total_on_known initial [handle] [plan,plan] same_owner
 exact ⟨commands,compiled,GeneralNominalPlanTrace251.length_exact initial [handle] [plan,plan] commands compiled,
   GeneralNominalPlanTrace251.checked_success initial initial_safe [handle] registered [plan,plan] commands compiled⟩

theorem no_unregistered_plan : GeneralNominalRegisteredPlan251.compile plan initial [] = none := rfl

theorem no_version_growth (commands : List Command)
 (compiled : GeneralNominalPlanTrace251.compile initial [handle] [plan,plan] = some commands) :
 (GeneralNominalFiniteInstallTrace250.run initial commands).definitions.map Prod.fst = initial.definitions.map Prod.fst := by
 have _ := GeneralNominalPlanTrace251.length_exact initial [handle] [plan,plan] commands compiled
 exact GeneralNominalFiniteInstallTrace250.targets_run initial commands
end Yulang.GeneralNominalPlanProducerRegression251
