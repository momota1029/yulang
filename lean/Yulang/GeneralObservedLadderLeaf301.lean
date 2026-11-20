import Yulang.GeneralObservedLadderAdvance301
import Yulang.GeneralRebaseRetarget275

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 7500000
namespace Yulang.GeneralObservedLadderLeaf301
open GeneralObservedLadderSource301 (snapshot endpoint scalar_model)
open GeneralObservedLadderInitial301 (context)
open GeneralObservedLadderReport301 (point int_report int_query exact_at)
open GeneralObservedLadderPlan301 (compiled)
open GeneralObservedLadderRoute301
open GeneralObservedLadderLedger301
open GeneralObservedLadderStage301
open GeneralDeclarationExamples (roles)
open GeneralNominalExamples (intDisplay int_display_checked)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalOutputGrowth (finiteModel)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedEvidence231 (Frame Instance)
open GeneralNominalVersionedCandidates231 (Prepared Unique Survivor)
open GeneralNominalVersionedPlans231
open GeneralNominalVersionedFrame231 (children)
open GeneralNominalRecursiveInspection
open GeneralNominalCenters (Plan Site)
open CommonNominalFullCarrier

abbrev terminalPacket (p : Phase n (n+1)) : GeneralNominalSaturationState.Packet roles :=
  ⟨compiled,env p,GeneralNominalDemandMerging.pointSite (focus n (n+1)),intDisplay,int_display_checked,
    [point n (n+1) (Nat.le_refl _)]⟩

abbrev terminalPlan (p : Phase n (n+1)) : Plan roles :=
  ⟨terminalPacket p,site n (n+1),rfl⟩

theorem blank_report (p : Phase n (n+1)) :
    GeneralNominalPacketSupport.report (terminalPacket p) =
      { inspected := [point n (n+1) (Nat.le_refl _)],
        checked := [point n (n+1) (Nat.le_refl _),point n (n+1) (Nat.le_refl _)] } := by
  change GeneralNominalRecursiveCandidates.report (env p) intDisplay [point n (n+1) (Nat.le_refl _)] = _
  rw [GeneralDictionaryOrdinaryTransport.candidate_report_extended,int_report]
  rfl

theorem blank_bindings (p : Phase n (n+1)) : (terminalPacket p).bindings = [] := by
  change bindings (env p).state (GeneralNominalPacketSupport.report (terminalPacket p)) = []
  rw [blank_report]
  rfl

theorem children_empty (p : Phase n (n+1)) : children (terminalPacket p) = [] := by
  unfold children GeneralDictionaryEmissionPlans.children
  rw [GeneralRebaseRetarget275.no_emission _ _ _ _ _ (show intDisplay.requirements = [] from rfl)]
  rfl

theorem schema_empty (p : Phase n (n+1)) : emittedSchema (terminalPlan p) = ⟨[],false⟩ := by
  unfold emittedSchema emittedRequests
  rw [GeneralRebaseRetarget275.no_emission _ _ _ _ _ (show intDisplay.requirements = [] from rfl)]
  rfl

theorem ordinary (p : Phase n (n+1)) (m : Assignment) : Ordinary (terminalPacket p) m := by
  refine ⟨?_,?_,?_⟩
  · rw [blank_bindings]
    intro _ member
    cases member
  · intro _ member
    cases member
  · rw [blank_report]
    simp [selfChecks,PresenceNormalForm.All]
    exact subtype_refl _

theorem head_schema (p : Phase n (n+1)) :
    (terminalPlan p).headSchema = ⟨[],[(.source (n+1),.scalar .int)],false⟩ := by
  unfold Plan.headSchema
  rw [show GeneralNominalInspection.queries (terminalPacket p).context.state (terminalPacket p).context.interpretation
    (terminalPacket p).declaration = _ from int_query n]
  simp [GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,List.ofFn_succ]
  exact GeneralNominalCenters.point_center (snapshot n).seed (focus n (n+1)) _ rfl

theorem holds (p : Phase n (n+1)) (m : Assignment) (valid : Models p.state m) : Holds (terminalPlan p) m := by
  have now := valid.1.1
  rw [p.context_eq] at now
  have base := ((GeneralDictionaryOrdinaryTransport.models_extended ..).mp now).1
  refine ⟨now,⟨ordinary p m,?_,GeneralNominalCenters.point_root_holds _ _ (fun _ => rfl) m,?_,?_,?_,?_⟩,?_⟩
  · rw [blank_report]
    simp [ProjectionModels]
  · intro name used
    rcases used with head | ⟨_,present,_⟩
    · cases head
    · cases present
  · rw [head_schema]
    refine ⟨?_,by intro _ h; cases h⟩
    intro entry seen
    cases List.mem_singleton.mp seen
    refine ⟨⟨_,.source (n+1)⟩,?_⟩
    intro value observed
    cases observed
    exact scalar_model n m base
  · rw [schema_empty]
    intro _ found
    cases found
  · intro _ found
    cases found
  · unfold Outputs
    rw [schema_empty]
    intro _ found
    cases found

theorem prepared (p : Phase n (n+1)) : Prepared compiled (env p) (focus n (n+1)) intDisplay := by
  refine ⟨metadata p,linked p (Nat.le_refl _),[point n (n+1) (Nat.le_refl _)],
    located p (Nat.le_refl _),fresh p _,?_,finiteModel n,?_⟩
  · change Finished (GeneralNominalPacketSupport.report (terminalPacket p))
    rw [blank_report]
    exact ⟨rfl,rfl,rfl⟩
  · exact (GeneralNominalVersionedCandidates231.headModels_packet_iff (terminalPacket p) _).mpr
      (GeneralNominalVersionedPlans231.head_models (holds p _ (model p)))

theorem frame (p : Phase n (n+1)) : Frame compiled p.state.core (focus n (n+1)) 3 (terminalPlan p) := by
  refine ⟨rfl,p.context_eq.symm,rfl,rfl,raw_recorded p,center_recorded p,List.mem_cons_self ..,rfl,
    located p (Nat.le_refl _),?_⟩
  rw [p.context_eq]
  exact prepared p

theorem terminal_instance (p : Phase n (n+1)) (m : Assignment) (valid : Models p.state m) :
    Instance compiled p.state.core m (focus n (n+1)) 3 [] := by
  refine ⟨_,GeneralNominalVersionedEvidence231.certificate_of_semantics
    (frame p) (children_empty p).symm (holds p m valid) ?_ ?_⟩
  · intro _ no
    rw [current_requests] at no
    cases no
  · exact GeneralRebaseDisplayFrame276.classes_empty (current_requests p (focus n (n+1))) (terminalPlan p) m

theorem unique (p : Phase n (n+1)) : Unique compiled (env p) (focus n (n+1)) 3 [] := by
  have chosen : Survivor compiled (env p) (focus n (n+1)) 3 [] :=
    ⟨known p (Nat.le_refl _),intDisplay,List.mem_cons_self ..,int_display_checked,rfl,rfl,
      [point n (n+1) (Nat.le_refl _)],located p (Nat.le_refl _),prepared p,(children_empty p).symm⟩
  refine ⟨chosen,?_⟩
  intro key cs other
  have kept := other
  obtain ⟨_,d,visible,_,declaration,role,_,_,good,_⟩ := other
  rcases GeneralRebaseCompiledDisplay277.compiled_members visible role with rfl|rfl
  · subst key
    exact ⟨rfl,GeneralNominalVersionedCandidates231.survivor_children_functional
      GeneralRebaseCompiledDisplay277.compiled_checked kept chosen⟩
  · exact False.elim (no_list p good)

end Yulang.GeneralObservedLadderLeaf301
