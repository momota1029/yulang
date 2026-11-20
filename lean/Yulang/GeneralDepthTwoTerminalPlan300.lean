import Yulang.GeneralDepthTwoSecondInstall300

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 12500000
namespace Yulang.GeneralDepthTwoTerminalPlan300
open GeneralGeneratedNestedSource299
open GeneralGeneratedNestedPredictions299 (compiled terminal)
open GeneralDepthTwoSecondInstall300 (final leafSite terminal_site)
open GeneralNominalExamples (intDisplay int_display_checked interpretation)
open GeneralDeclarationExamples (roles)
open GeneralNominalCenters
open GeneralNominalVersionedPlans231
open GeneralNominalRecursiveInspection
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

abbrev env := final.core.erased.current.context
abbrev packet : GeneralNominalSaturationState.Packet roles :=
  ⟨compiled,env,leafSite.observed,intDisplay,int_display_checked,[((2 : Fin 3),(2 : Fin 3))]⟩
abbrev plan : Plan roles := ⟨packet,leafSite,rfl⟩

theorem leaf_exact : leafSite = GeneralDepthTwoMiddlePlan300.child :=
  GeneralNominalVersionedTransport231.childSite_eq GeneralDepthTwoMiddleContext300.res
    GeneralDepthTwoMiddleContext300.updates GeneralDepthTwoMiddleContext300.owns
    GeneralDepthTwoMiddleContext300.pendingPlan GeneralDeclarationExamples.displayChild
    (GeneralDeclarationExamples.display_checked.signature.2.2.2 _ (by simp))

theorem leaf_center : ∀ i, leafSite.center i = 2 :=
  leaf_exact.symm ▸ GeneralDepthTwoMiddlePlan300.child_data.2

theorem leaf_args : ∀ i, leafSite.occurrence.demand.arguments i = (2,2) :=
  leaf_exact.symm ▸ GeneralDepthTwoMiddlePlan300.child_args

theorem leaf_input (m : Assignment) : leafSite.Holds m := by
  intro i
  rw [leaf_args,leaf_center]
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem query : GeneralNominalInspection.queries env.state env.interpretation intDisplay = [.scalar .int] := by
  change GeneralNominalInspection.queries snapshot interpretation intDisplay = _
  simp [GeneralNominalInspection.queries,GeneralDeclarations.Declaration.normalHead,
    GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
    GeneralNominalInspection.translate,interpretation]

theorem report_exact : GeneralNominalPacketSupport.report packet =
    { inspected := [((2 : Fin 3),(2 : Fin 3))],
      checked := [((2 : Fin 3),(2 : Fin 3)),((2 : Fin 3),(2 : Fin 3))] } := by
  unfold GeneralNominalPacketSupport.report GeneralNominalRecursiveCandidates.report
  rw [show GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration = _
    from query]
  have nom : env.state.nominals (2 : Fin 3) = none := rfl
  have ints : env.state.view.heads (2 : Fin 3) = .scalar .int := rfl
  simp [inspectMany,inspect,Report.visit,Report.append,nom,ints]

theorem bindings_empty : packet.bindings = [] := by
  change bindings env.state (GeneralNominalPacketSupport.report packet) = []
  rw [report_exact]
  rfl

theorem children_empty : GeneralNominalVersionedFrame231.children packet = [] := by
  unfold GeneralNominalVersionedFrame231.children GeneralDictionaryEmissionPlans.children
  rw [GeneralRebaseRetarget275.no_emission _ _ _ _ _ (show intDisplay.requirements = [] from rfl)]
  rfl

theorem schema_empty : emittedSchema plan = ⟨[],false⟩ := by
  unfold emittedSchema emittedRequests
  rw [GeneralRebaseRetarget275.no_emission _ _ _ _ _ (show intDisplay.requirements = [] from rfl)]
  have blank : leafSite.occurrence.demand.outputs = [] := by decide +kernel
  change GeneralNominalCenteredHeadMatSchemas.generated _ _
      (GeneralNominalMaterialization.rootRequests intDisplay leafSite.occurrence ++ _) = _
  simp [GeneralNominalMaterialization.rootRequests,blank]
  rfl

theorem ordinary (m : Assignment) : Ordinary packet m := by
  refine ⟨?_,?_,?_⟩
  · rw [bindings_empty]
    intro _ member
    cases member
  · intro _ member
    cases member
  · rw [report_exact]
    simp [selfChecks,PresenceNormalForm.All]
    exact subtype_refl _

theorem head_schema : plan.headSchema = ⟨[],[(.source 2,.scalar .int)],false⟩ := by
  unfold Plan.headSchema
  rw [show GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration = _
    from query]
  simp [GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,List.ofFn_succ,leaf_center]

theorem holds (m : Assignment) (valid : Models final m) : Holds plan m := by
  refine ⟨valid.1.1,⟨ordinary m,?_,leaf_input m,?_,?_,?_,?_⟩,?_⟩
  · rw [report_exact]
    simp [ProjectionModels]
  · intro name used
    rcases used with head | ⟨_,present,_⟩
    · cases head
    · cases present
  · rw [head_schema]
    refine ⟨?_,by intro _ h; cases h⟩
    intro entry seen
    cases List.mem_singleton.mp seen
    refine ⟨⟨_,.source 2⟩,?_⟩
    intro actual observed
    cases observed
    exact valid.1.1.1.2.1 (2 : Fin 3) (.base .int) rfl
  · rw [schema_empty]
    intro _ found
    cases found
  · intro _ found
    cases found
  · unfold Outputs
    rw [schema_empty]
    intro _ found
    cases found

end Yulang.GeneralDepthTwoTerminalPlan300
