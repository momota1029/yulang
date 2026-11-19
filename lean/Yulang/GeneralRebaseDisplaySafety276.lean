import Yulang.GeneralRebaseTowerAcyclic276
import Yulang.GeneralRebaseAllWidthSafety275
import Yulang.GeneralRebaseDisplayEvidence276

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 9200000
namespace Yulang.GeneralRebaseDisplaySafety276
open GeneralNominalExamples (model state context registry displayRoot displayChild intDisplay state_models)
open GeneralDeclarationExamples (roles wrap)
open GeneralNominalNonleafPlan193 (plan packet declaration)
open GeneralRebaseDisplayFrame276 (before after frame prepared)
open GeneralNominalOutputGrowth (tower tower_equivalent)
open GeneralNominalVersionedJournal232 (Models)
open CommonNominalFullCarrier GeneralNominalRecursiveInspection

theorem towers (id : Nat) : ∃ depth, (model id).1 = tower depth := by
 by_cases h : id = 0
 · exact ⟨1,by simp [h,tower]⟩
 · exact ⟨0,by simp [h,tower]⟩

theorem before_model : Models before model :=
 (GeneralNominalVersionedJournal232.initial_models _ _ _).mpr
  ⟨state_models true,GeneralNominalCenters.point_root_holds _ _ (fun _ => rfl) _⟩

theorem after_model : Models after model :=
 (GeneralRebaseDisplayFrame276.after_models model).mpr (state_models true)

theorem semantic {s : GeneralNominalVersionedJournal232.State roles} (holds : Models s model) (origin) :
 ¬ GeneralNominalVersionedCycles232.Cyclic s origin :=
 GeneralRebaseTowerAcyclic276.acyclic holds towers origin

noncomputable def depth (snapshot : GeneralNominalState.State) (slot : Fin snapshot.base.slots) : Nat :=
 Classical.choose (towers (snapshot.base.source slot))

theorem depth_exact (snapshot : GeneralNominalState.State) (slot : Fin snapshot.base.slots) :
 (model (snapshot.base.source slot)).1 = tower (depth snapshot slot) :=
 Classical.choose_spec (towers (snapshot.base.source slot))

theorem raw_edge (snapshot : GeneralNominalState.State) (noShapes : snapshot.view.kinds = 0)
 (holds : GeneralNominalState.Models snapshot model)
 {a b : Fin snapshot.base.slots} (edge : GeneralNominalMixedRecurrence.Edge snapshot a b) :
 depth snapshot b < depth snapshot a := by
 rcases edge with ⟨kind,_,_,_⟩ | nominal
 · have contradiction := kind.isLt
   omega
 · obtain ⟨desc,_,i,value,seen,same⟩ :=
     GeneralNominalMixedRecurrence.actual_edge_sound snapshot a b nominal model holds
   have obs := embed_observation model _ value seen
   cases obs with
   | nominal parent equal found =>
     cases parent
     rw [depth_exact snapshot a] at equal
     obtain ⟨k,strict,meaning⟩ := GeneralRebaseTowerSemantics276.nominal_projection _ equal found
     rw [depth_exact snapshot b] at same
     have equalDepth := (tower_equivalent _ _).mp
        ⟨subtype_trans same.2 meaning.1,subtype_trans meaning.2 same.1⟩
     omega

theorem raw_acyclic (snapshot : GeneralNominalState.State) (noShapes : snapshot.view.kinds = 0)
 (holds : GeneralNominalState.Models snapshot model) (slot : Fin snapshot.base.slots) :
 ¬ GeneralNominalCycleK2.RecursAt snapshot slot := by
 intro cycle
 obtain ⟨next,edge,path⟩ := GeneralNominalCycleK2.recurs_cycle snapshot slot cycle
 have strict := raw_edge snapshot noShapes holds edge
 have reverse := GeneralRebaseAllWidthSafety275.path_rank (depth snapshot)
   (fun _ _ edge => raw_edge snapshot noShapes holds edge) _ _ path
 omega

theorem wrong_initial_failed :
 GeneralNominalVersionedCandidates231.Failed registry (context true) displayRoot intDisplay := by
 have old := GeneralNominalNonleafLocal193.prepared
 refine ⟨old.1,[(0,0)],rfl,?_,?_,?_,Or.inl ?_⟩
 · intro key _ overlap
   have high : 1 < GeneralNominalIdentities.source (state true).seed key :=
     GeneralNominalIdentities.source_above_seed _ _
   have small := GeneralRebaseDisplayFrame276.source_ids _ overlap
   change 1 < GeneralNominalIdentities.source (context true).state.seed key at high
   omega
 all_goals decide +kernel

theorem administrative : GeneralNominalVersionedDiagnostic232.AdministrativeReady before displayRoot := by
 constructor
 · exact ⟨plan.input,List.mem_singleton_self _,rfl⟩
 · intro a first _ b last _
   change a ∈ [_] at first
   change b ∈ [_] at last
   cases List.mem_singleton.mp first
   cases List.mem_singleton.mp last
   exact .refl _

theorem initial_safe : B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) registry before displayRoot := by
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
   · simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
     rcases visible with rfl|rfl|rfl
     · exact notFailed wrong_initial_failed
     · exact notPrepared prepared
     · cases role
   · exact pending administrative

theorem position_length :
 (GeneralNominalCenteredSteps.inspection plan).inspected.length =
   (GeneralNominalCenteredSteps.inspection plan).tests.length :=
 GeneralNominalNonleafInstallation193.enabled.positions.1

theorem initial_positions : GeneralNominalVersionedCycles232.Safe before plan :=
 ⟨position_length,fun _ _ => semantic before_model _⟩

end Yulang.GeneralRebaseDisplaySafety276
