import Yulang.GeneralRebaseCompiledDisplay277

set_option maxRecDepth 28000
set_option maxHeartbeats 9900000
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseCompiledInstall277
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalExamples (registry context state model displayRoot displayChild intDisplay state_models)
open GeneralDeclarationExamples (roles display)
open GeneralNominalVersionedCandidates231
open GeneralRebaseDisplayFrame276 (before)
open GeneralRebaseCompiledDisplay277
open GeneralRebaseDisplaySafety276 (raw_acyclic semantic before_model administrative)
open GeneralNominalVersionedMixedKernel234 (Step AlternativesSafe Installable Committed)
open GeneralNominalVersionedJournal232
open GeneralNominalVersionedInstall232 (InstallationModels)
open GeneralNominalCommonBridge (Assignment)

theorem safe : B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles)
    compiled before displayRoot := by
 refine ⟨GeneralNominalNonleafLocal193.known,?_,?_,?_⟩
 · rintro (raw | (⟨i,cyclic⟩ | ⟨site,_,_,i,cyclic⟩))
   · obtain ⟨_,_,_,slot,_,cyclic⟩ := raw
     exact raw_acyclic (state true) rfl (state_models true) slot cyclic
   · exact semantic before_model _ cyclic
   · exact semantic before_model _ cyclic
 · rintro (raw | ⟨p,_,entry,_,cyclic⟩)
   · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cyclic⟩ := raw
     exact raw_acyclic (state true) rfl (state_models true) visited.1 cyclic
   · exact semantic before_model _ cyclic
 · rintro (⟨_,d,visible,role,notFailed,notPrepared⟩ | pending)
   · rcases compiled_members visible role with rfl|rfl
     · exact notFailed wrong_failed
     · exact notPrepared prepared_parent
   · exact pending administrative

theorem frame_decl {p : Plan roles} {key}
    (given : GeneralNominalVersionedEvidence231.Frame compiled before.core displayRoot key p) :
    p.packet.declaration = display := by
  rcases compiled_members given.visible given.role_eq with wrong|right
  · exact False.elim (wrong_not_prepared (wrong ▸ given.prepared))
  · exact right

theorem positions : GeneralNominalVersionedCycles232.Safe before parent :=
 ⟨GeneralRebaseDisplaySafety276.position_length,fun _ _ => semantic before_model _⟩

theorem alternatives : AlternativesSafe compiled before parent.input := by
 intro candidate same framed
 have atRoot : parent.input.occurrence = displayRoot := rfl
 have located : GeneralNominalVersionedEvidence231.Frame compiled before.core displayRoot
   candidate.packet.declaration.id candidate := atRoot ▸ framed
 have raw : candidate.packet.site = parent.packet.site := List.mem_singleton.mp located.raw_recorded
 have eq := GeneralRebaseScopedFrame276.same_frame located frame_parent (frame_decl located) raw same
 subst candidate
 exact positions

theorem raw_sites_eq :
    after.core.erased.current.sites = GeneralRebaseDisplayFrame276.after.core.erased.current.sites := rfl

theorem center_sites_eq :
    after.core.sites = GeneralRebaseDisplayFrame276.after.core.sites := rfl

theorem edges_eq :
    after.core.erased.current.edges = GeneralRebaseDisplayFrame276.after.core.erased.current.edges := rfl

theorem no_new_request (focus : Occurrence roles) :
    GeneralNominalCenteredHeadOutputs.requests after.core focus = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro output member
  obtain ⟨site,present,_,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
  rw [raw_sites_eq,GeneralRebaseDisplayEvidence276.raw_sites] at present
  simp only [List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl|rfl <;> cases within

theorem installation (m : Assignment) (valid : GeneralNominalState.Models (state true) m) :
    InstallationModels before effect m := by
  have holds : GeneralNominalVersionedPlans231.Holds parent m :=
    (GeneralRebaseCompiledRetag277.holds GeneralNominalNonleafPlan193.plan compiled rfl m).mpr
      (GeneralRebaseDisplayPacket276.holds m valid)
  refine ⟨(initial_models _ _ _).mpr ⟨valid,point_root_holds _ _ (fun _ => rfl) _⟩,
    holds,⟨GeneralNominalVersionedPlans231.head_models holds,GeneralRebaseDisplayFrame276.classes_empty
      GeneralRebaseDisplayFrame276.requests_empty parent m⟩,
    GeneralRebaseDisplayFrame276.classes_empty (no_new_request displayRoot) parent m,?_,?_⟩
  all_goals intro _ impossible; cases impossible

theorem installable : Installable compiled before effect := by
 refine ⟨rfl,rfl,safe,?_,?_,?_,positions,alternatives,model,installation model (state_models true)⟩
 · exact GeneralNominalVersionedMixedObservations233.legacy_cache
     (GeneralDictionaryDefaultCache208.initial_valid (context true) displayRoot)
 · change (GeneralNominalVersionedPlans231.emittedSchema parent).unknown = false
   rw [GeneralRebaseCompiledRetag277.schema_eq,GeneralRebaseDisplayPacket276.emitted]
 · intro prior appears
   cases appears

theorem novel : ¬ Committed before parent := by
 intro committed
 have impossible := committed.2 displayChild (GeneralRebaseCompiledDisplay277.children ▸ List.mem_singleton_self _)
 cases impossible

theorem actual_step : Step compiled displayRoot before after :=
 ⟨displayRoot,.root,.install effect installable novel⟩

theorem adapter_step :
    (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step registry displayRoot before after := actual_step

theorem reachable :
    B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry displayRoot after :=
  ⟨before,GeneralRebaseDisplayStep276.initial_source,.tail .refl adapter_step⟩

theorem models (m : Assignment) : Models after m ↔ Models before m := by
 constructor
 · exact GeneralNominalVersionedMixedKernel234.step_models actual_step
 · intro held
   have raw : GeneralNominalState.Models (state true) m := ((initial_models _ _ _).mp held).1
   exact (GeneralNominalVersionedInstall232.install_models (effect := effect) rfl).mpr (installation m raw)

theorem direct_models (m : Assignment) : Models after m ↔ Models GeneralRebaseDisplayFrame276.after m :=
  (models m).trans ((GeneralRebaseDisplayExecutor276.model_exact .source m).trans
    (GeneralRebaseDisplayExecutor276.model_exact .settled m).symm)

end Yulang.GeneralRebaseCompiledInstall277
