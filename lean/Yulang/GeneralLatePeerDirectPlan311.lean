import Yulang.GeneralLatePeerFirst311
import Yulang.GeneralNominalSemanticRawFrame236
import Yulang.GeneralNominalRepeatedLocal190
import Yulang.GeneralRebaseCompiledChildFresh277

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 25500
set_option maxHeartbeats 14000000
namespace Yulang.GeneralLatePeerDirectPlan311
open GeneralLatePeerSource311 (compiled root initial receiver receiver_checked)
abbrev body : GeneralDeclarations.Equation := ⟨40,1,.app 2 []⟩
open GeneralLatePeerRoot311 (direct direct_args direct_center direct_output z)
open GeneralLatePeerFirst311 (after)
open GeneralDeclarationExamples (roles constructors)
open GeneralNominalExamples (interpretation)
open GeneralGeneratedNestedSource299 (snapshot model context snapshot_model)
open GeneralNominalSemanticRawFrame236 (sources source_models_same)
open GeneralDeclarations
open GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedPlans231
open GeneralNominalRecursiveInspection
open CommonNominalFullCarrier

abbrev ctx := after.core.erased.current.context
abbrev two : Fin ctx.state.base.slots := (2 : Fin 3)
abbrev packet : GeneralNominalSaturationState.Packet roles :=
 ⟨compiled,ctx,direct.observed,receiver,receiver_checked,[(two,two)]⟩
abbrev plan : Plan roles := ⟨packet,direct,rfl⟩

theorem query : GeneralNominalInspection.queries ctx.state ctx.interpretation receiver = [.scalar .int] := by
  change GeneralNominalInspection.queries snapshot interpretation receiver = _
  simp [GeneralNominalInspection.queries,GeneralDeclarations.Declaration.normalHead,
      GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
      GeneralNominalInspection.translate,GeneralNominalExamples.interpretation]

theorem report : GeneralNominalPacketSupport.report packet =
    { inspected := [(two,two)], checked := [(two,two),(two,two)] } := by
  unfold GeneralNominalPacketSupport.report GeneralNominalRecursiveCandidates.report
  have q : GeneralNominalInspection.queries packet.context.state packet.context.interpretation
      packet.declaration = _ := query
  rw [q]
  have no : ctx.state.nominals (2 : Fin 3) = none := rfl
  have scalar : ctx.state.view.heads (2 : Fin 3) = .scalar .int := rfl
  change { inspectMany ctx.state [.scalar .int] [(two,two)] (fun _ => none) 0 with
    checked := [(two,two)] ++ (inspectMany ctx.state [.scalar .int] [(two,two)] (fun _ => none) 0).checked } = _
  simp [inspectMany,inspect,Report.visit,Report.append,no,scalar]

theorem bindings_empty : packet.bindings = [] := by
  change bindings ctx.state (GeneralNominalPacketSupport.report packet) = []
  rw [report]
  rfl

theorem no_children : GeneralNominalVersionedFrame231.children packet = [] := by
  unfold GeneralNominalVersionedFrame231.children GeneralDictionaryEmissionPlans.children
  rw [GeneralRebaseRetarget275.no_emission _ _ _ _ _ (show receiver.requirements = [] from by rfl)]
  rfl

theorem named_requests : direct.occurrence.demand.outputs = [⟨1,z⟩] := direct_output

theorem emitted_exact :
    emittedSchema plan = ⟨[⟨z,.actual,.primitive (.scalar .int) []⟩],false⟩ := by
  unfold emittedSchema emittedRequests
  rw [GeneralRebaseRetarget275.no_emission _ _ _ _ _ rfl]
  rfl

theorem head_schema : plan.headSchema = ⟨[],[(.source 2,.scalar .int)],false⟩ := by
  unfold Plan.headSchema
  rw [show GeneralNominalInspection.queries ctx.state ctx.interpretation receiver = _ from query]
  simp [GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,
      GeneralNominalMaterialization.Schema.append,List.ofFn_succ,direct_center]

theorem ordinary (m : Assignment) : Ordinary packet m := by
  refine ⟨?_,?_,?_⟩
  · rw [bindings_empty]
    exact fun _ member => False.elim (List.not_mem_nil member)
  · intro a hit; cases hit
  · rw [report]
    simp [selfChecks,PresenceNormalForm.All]
    exact subtype_refl _

theorem holds (m : Assignment) (valid : Models after m)
    (output : Equivalent (m z).1 (.base .int)) : Holds plan m := by
  refine ⟨valid.1.1,⟨ordinary m,?_,?_,?_,?_,?_,?_⟩,?_⟩
  · change ProjectionModels ctx.state (GeneralNominalPacketSupport.report packet) m
    rw [report]; simp [ProjectionModels]
  · intro i
    change Subtype (m (direct.occurrence.demand.arguments i).1).1 (m (direct.center i)).1 ∧
      Subtype (m (direct.center i)).1 (m (direct.occurrence.demand.arguments i).2).1
    rw [direct_args,direct_center]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · intro _ hit
    rcases hit with named|⟨c,contained,_⟩
    · cases named
    · cases contained
  · rw [head_schema]
    refine ⟨?_,by intro _ h; cases h⟩
    intro entry seen
    cases List.mem_singleton.mp seen
    refine ⟨⟨_,.source 2⟩,?_⟩
    intro actual observed
    cases observed
    exact valid.1.1.1.2.1 (2 : Fin 3) (.base .int) rfl
  · rw [emitted_exact]
    intro e found wrong; cases List.mem_singleton.mp found; exact False.elim (wrong rfl)
  · intro _ found; cases found
  · unfold Outputs
    rw [emitted_exact]
    intro _ found; cases List.mem_singleton.mp found
    exact output

end Yulang.GeneralLatePeerDirectPlan311
