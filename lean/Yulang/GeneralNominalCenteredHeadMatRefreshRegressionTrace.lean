import Yulang.GeneralNominalCenteredHeadMatRefreshRegressionSource
import Yulang.GeneralNominalCenteredHeadMatPairCycles

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralNominalCenteredHeadMatRefreshRegressionTrace
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredSourceUnsettledRefreshWitness
open GeneralNominalCenteredHeadMatRefreshRegressionSource
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalCenteredHeadMatStepKernel
open GeneralNominalCenteredHeadMatPairCycles (PairTree)
open CommonNominalFullCarrier

theorem witness_trees (identity : Nat) :
    ∃ tree : GeneralNominalBranchingReadback.Tree, PairTree tree ∧ (witness identity).1 = tree.value := by
  refine ⟨witnessTree identity,?_,rfl⟩
  unfold witnessTree
  split <;> first | trivial | split <;> trivial

theorem no_cycles {state : State roles} (valid : Models state witness) (origin) :
    ¬ GeneralNominalCenteredHeadMatStepCycles.Cyclic state origin :=
  GeneralNominalCenteredHeadMatPairCycles.acyclic valid witness_trees origin

theorem start_ready : GeneralNominalCenteredHeadMatStepLocal.AdministrativeReady start root := by
  refine ⟨⟨_,List.mem_singleton_self _,rfl⟩,?_⟩
  intro first one same last two _
  cases List.mem_singleton.mp one
  cases List.mem_singleton.mp two
  exact .refl _

theorem start_safe : B4TargetV6.SafeKnown (GeneralNominalCenteredHeadMatStepLocal.diagnosticBoundary roles) registry start root := by
  refine ⟨rootP_ready,?_,?_,?_⟩
  · rintro (old | (⟨index,cycle⟩ | ⟨site,present,same,index,cycle⟩))
    · obtain ⟨_,_,_,slot,_,recurs⟩ := old
      exact source_no_raw slot (GeneralNominalCycleK2.recurs_cycle _ _ recurs)
    · exact no_cycles start_model _ cycle
    · exact no_cycles start_model _ cycle
  · rintro (old | ⟨plan,frame,entry,member,cycle⟩)
    · obtain ⟨_,_,_,_,_,_,_,_,visited,_,recurs⟩ := old
      exact source_no_raw visited.1 (GeneralNominalCycleK2.recurs_cycle _ _ recurs)
    · exact no_cycles start_model _ cycle
  · rintro (⟨_,declaration,visible,role,_,unprepared⟩ | unclosed)
    · cases p_only declaration visible role
      exact unprepared head_prepared
    · exact unclosed start_ready

theorem installable : Installable registry start effectP := by
  refine ⟨rfl,rfl,start_safe,GeneralNominalCenteredHeadMatStepObservations.initial_cache context root,
    ?_,?_,?_,?_,⟨witness,installation_model⟩⟩
  · change (GeneralNominalCenteredHeadMatPlans.emittedSchema planP).unknown = false
    rw [emitted_schema]
  · intro prior member; cases member
  · exact ⟨inspectionP_count planP rfl rfl rfl locatedP,fun entry _ => no_cycles start_model entry.1⟩
  · intro plan same framed
    have declarationSame := p_only plan.packet.declaration framed.visible framed.role_eq
    have located : GeneralNominalRecursiveCandidates.arguments plan.packet.context plan.input.occurrence = some plan.packet.bounds := by
      rw [same]
      exact framed.located
    exact ⟨inspectionP_count plan same framed.context_eq declarationSame located,
      fun entry _ => no_cycles start_model entry.1⟩

theorem uncommitted : ¬ Committed start planP := by
  intro committed
  have member : emittedChild.occurrence ∈ planP.packet.children := childrenP_exact ▸ List.mem_singleton_self _
  have edge := committed.2 emittedChild.occurrence member
  cases edge

theorem stepP : Step registry root start installed :=
  ⟨root,.root,.install effectP installable uncommitted⟩

theorem installed_generated : GeneralNominalSaturationState.Generated installed.core.erased.current root emittedChild.occurrence :=
  .child .root (installed_child (effect := effectP) (childrenP_exact ▸ List.mem_singleton_self _))

theorem installed_unsettled (packet : GeneralNominalSaturationState.Packet roles) :
    ¬ GeneralNominalSettledSupport.PacketSettled installed.core.erased.current packet := by
  intro settled
  have noDone (focus : Occurrence roles) (done : GeneralNominalSupport.Discharged installed.core.erased.current focus) : False := by
    induction done with
    | packet installed present children ih =>
        cases List.mem_singleton.mp present
        exact ih emittedChild.occurrence (childrenP_exact ▸ List.mem_singleton_self _)
    | alias first last one two same done ih => exact ih
  exact noDone packet.site.occurrence (GeneralNominalSettledSupport.packet_settled_demand settled)

theorem packet_legacy (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalCenteredHeadMatStepPackets.Holds planP model) : planP.Holds model := by
  have output : Equivalent (model 2).1 (.base .int) := by
    have equations := valid.2.2
    unfold GeneralNominalCenteredHeadMatStepPackets.Outputs at equations
    rw [emitted_schema] at equations
    exact equations _ (List.mem_cons_self)
  have input := centered_inputsP model valid.1
  refine ⟨(GeneralNominalPacketSupport.packet_exact packetP model).mpr
    ⟨valid.1,inputsP model,outputsP model output⟩,
    input.2.1,input.2.2.1,input.2.2.2.1,input.2.2.2.2.1,namedSchemaP_holds model output,input.2.2.2.2.2⟩

theorem installed_legacy (model : GeneralNominalCommonBridge.Assignment) (valid : Models installed model) :
    GeneralNominalCenteredSteps.Models afterP model := by
  have previous := (install_models rfl).mp valid
  exact (GeneralNominalCenteredSteps.install_models (state := initialState) (plan := planP) (support := []) rfl model).mpr
    ⟨(GeneralNominalCenteredSteps.point_initial_models context root (fun _ => rfl) model).mpr previous.1.2.1,
      packet_legacy model previous.2.1⟩

end Yulang.GeneralNominalCenteredHeadMatRefreshRegressionTrace
