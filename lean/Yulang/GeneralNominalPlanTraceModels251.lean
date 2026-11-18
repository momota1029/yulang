import Yulang.GeneralNominalPlanTrace251
namespace Yulang.GeneralNominalPlanTraceModels251
open Core.PresenceGeneration (CompTerm)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenters (Plan)
open GeneralNominalMaterializedOwnerFrame249 (Frame Models)
open GeneralNominalOwnerOpening250 (Handle)
open GeneralNominalOwnerRegistry250 (Registered)
open GeneralNominalFiniteInstallTrace250 (Command advance nextAssignment Permitted run)
open GeneralPresenceOrderedBlock247
open CommonNominalFullCarrier

noncomputable def PlanHolds (plan : Plan roles) (frame : Frame) (handle : Handle) (assignment : Assignment) : Prop :=
 let fallback := GeneralNominalPlanProducer251.fallback plan frame
 let binders := GeneralNominalRoleBinder251.compile plan frame CompTerm.var
 let current := GeneralNominalStableCaptureStep250.next frame handle plan.packet.bindings assignment
 GeneralNominalRolePacket251.Holds plan
   (GeneralNominalStableRoleEnvironment251.compile frame handle plan.packet.bindings fallback binders CompTerm.var)
   (GeneralNominalStableRoleHead251.reference handle plan.packet.bindings fallback binders CompTerm.var
     (solve model frame.definitions assignment) current) current

theorem condition_exact (plan : Plan roles) (frame : Frame) (safe : SafeOrder frame.definitions) (handles : List Handle)
 (registered : Registered frame handles) (handle : Handle) (command : Command)
 (success : GeneralNominalRegisteredPlan251.compile plan frame handles = some (handle,command)) (assignment : Assignment) :
 command.delta.Holds (nextAssignment frame command assignment) ↔ PlanHolds plan frame handle assignment := by
 obtain ⟨member,_,rfl⟩ := GeneralNominalRegisteredPlan251.compile_exact plan frame handles handle command success
 exact (GeneralNominalStableRolePacket251.delta_exact ..).trans
   (GeneralNominalStableRolePacket251.generated_exact plan frame safe handle
     (GeneralNominalOwnerRegistry250.handle_coverage frame handles registered handle member plan.packet.bindings) _ _ _ assignment)

noncomputable def Holds (frame : Frame) (handles : List Handle) : List (Plan roles) → Assignment → Prop
 | [],_ => True
 | plan :: rest,assignment =>
   match GeneralNominalRegisteredPlan251.compile plan frame handles with
   | none => False
   | some prepared => PlanHolds plan frame prepared.1 assignment ∧
     Holds (advance frame prepared.2) handles rest (nextAssignment frame prepared.2 assignment)

theorem permitted_exact (frame : Frame) (safe : SafeOrder frame.definitions) (handles : List Handle)
 (registered : Registered frame handles) (plans : List (Plan roles)) (commands : List Command)
 (success : GeneralNominalPlanTrace251.compile frame handles plans = some commands) (assignment : Assignment) :
 Permitted frame commands assignment ↔ Holds frame handles plans assignment := by
 induction plans generalizing frame commands assignment with
 | nil => simp [GeneralNominalPlanTrace251.compile] at success; subst commands; exact Iff.rfl
 | cons plan rest ih =>
   cases found : GeneralNominalRegisteredPlan251.compile plan frame handles with
   | none => simp [GeneralNominalPlanTrace251.compile,found] at success
   | some prepared =>
     cases tail : GeneralNominalPlanTrace251.compile (advance frame prepared.2) handles rest with
     | none => simp [GeneralNominalPlanTrace251.compile,found,tail] at success
     | some commandsTail =>
       simp only [GeneralNominalPlanTrace251.compile,found,Option.bind_some,tail,Option.map_some,Option.some.injEq] at success
       subst commands
       simp only [Permitted,Holds,found]
       exact and_congr (condition_exact plan frame safe handles registered prepared.1 prepared.2 found assignment)
         (ih _ (GeneralNominalFiniteInstallTrace250.safe_advance frame safe prepared.2)
           (GeneralNominalRegisteredPlan251.retains_registry frame handles registered prepared.2) _ tail _)

theorem public_models_iff (frame : Frame) (safe : SafeOrder frame.definitions) (handles : List Handle)
 (registered : Registered frame handles) (plans : List (Plan roles)) (commands : List Command)
 (success : GeneralNominalPlanTrace251.compile frame handles plans = some commands)
 (shared : Nat → Prop)
 (privateNames : ∀ name, shared name → ∀ entry ∈ frame.definitions, entry.1 ≠ name) (boundary : Assignment) :
 (∃ assignment, Models frame assignment ∧ Holds frame handles plans assignment ∧
   GeneralPresenceOrderedRebase247.Agrees model shared assignment boundary) ↔
 GeneralNominalMaterializedSequenceModels249.PublicModels (run frame commands) shared boundary := by
 have trace := GeneralNominalFiniteInstallTrace250.public_run_iff frame safe commands shared privateNames boundary
 have congruent : (∃ assignment, Models frame assignment ∧ Permitted frame commands assignment ∧
   GeneralPresenceOrderedRebase247.Agrees model shared assignment boundary) ↔
   (∃ assignment, Models frame assignment ∧ Holds frame handles plans assignment ∧
     GeneralPresenceOrderedRebase247.Agrees model shared assignment boundary) := by
   apply exists_congr; intro assignment
   exact and_congr Iff.rfl (and_congr (permitted_exact frame safe handles registered plans commands success assignment) Iff.rfl)
 exact congruent.symm.trans trace
end Yulang.GeneralNominalPlanTraceModels251
