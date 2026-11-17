import Yulang.GeneralDictionaryMixedGap206Refresh234
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryMixedGap206Frame234
open GeneralDictionaryDefaultGap206Source (roles registry root declaration declaration_checked checked source model)
open GeneralDictionaryMixedGap206Snapshot234 (snapshot context)
open GeneralDictionaryMixedGap206Refresh234 (refreshed model_retained)
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
noncomputable abbrev packet : GeneralNominalSaturationState.Packet roles :=
  ⟨registry,context,GeneralNominalDemandMerging.pointSite root,declaration,declaration_checked,[(1,1)]⟩
noncomputable abbrev plan : Plan roles := ⟨packet,rootSite snapshot.seed root,rfl⟩

theorem raw_sites : refreshed.core.erased.current.sites = [GeneralNominalDemandMerging.pointSite root] :=
  GeneralDictionaryVersionedGap206AfterSelected234.raw_sites

theorem centers : refreshed.core.sites = [rootSite snapshot.seed root] :=
  GeneralDictionaryVersionedGap206AfterSelected234.centers

theorem query : GeneralNominalInspection.queries snapshot context.interpretation declaration = [.scalar .int] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation]

theorem report_exact : GeneralNominalRecursiveCandidates.report context declaration [(1,1)] =
    { inspected := [((1 : Fin 3),(1 : Fin 3))], checked := [((1 : Fin 3),(1 : Fin 3)),((1 : Fin 3),(1 : Fin 3))] } := by
  unfold GeneralNominalRecursiveCandidates.report
  rw [query]
  simp [GeneralNominalRecursiveInspection.inspectMany,GeneralNominalRecursiveInspection.inspect,
    GeneralNominalRecursiveInspection.Report.visit,GeneralNominalRecursiveInspection.Report.append]

theorem bindings_empty : packet.bindings = [] := by
  change GeneralNominalRecursiveInspection.bindings snapshot (GeneralNominalRecursiveCandidates.report context declaration [(1,1)]) = []
  rw [report_exact]; rfl

theorem scalar (assignment) (valid : GeneralNominalState.Models snapshot assignment) :
    Equivalent (assignment 1).1 (.base .int) := valid.1.2.1 (1 : Fin 3) (.base .int) rfl

theorem head_schema : plan.headSchema = { tests := [(.source 1,.scalar .int)] } := by
  unfold Plan.headSchema
  rw [query]
  simp [GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,plan,rootSite,List.ofFn_succ]

theorem ordinary (assignment : Assignment) : GeneralNominalVersionedPlans231.Ordinary packet assignment := by
  unfold GeneralNominalVersionedPlans231.Ordinary
  rw [bindings_empty]
  refine ⟨?_,?_,?_⟩
  · simp [GeneralNominalAllocation.Compatible]
  · simp [GeneralNominalVersionedAllocation231.merges,Declaration.inputNames,normalizeArgs,normalize,
      variablesArgs,Pattern.variables]
  · change PresenceNormalForm.All CommonNominalFullCarrier.model assignment
      (GeneralNominalRecursiveInspection.selfChecks snapshot (GeneralNominalRecursiveCandidates.report context declaration [(1,1)]))
    rw [report_exact]
    simp [GeneralNominalRecursiveInspection.selfChecks,PresenceNormalForm.All]
    exact subtype_refl _

theorem head_models (assignment : Assignment) (valid : GeneralNominalState.Models snapshot assignment) :
    GeneralNominalVersionedPlans231.HeadModels packet assignment := by
  refine ⟨(GeneralNominalVersionedPlans231.private_models_iff ..).mpr ⟨valid,ordinary assignment⟩,?_⟩
  change GeneralNominalRecursiveInspection.ProjectionModels snapshot
    (GeneralNominalRecursiveCandidates.report context declaration [(1,1)]) assignment
  rw [report_exact]
  simp [GeneralNominalRecursiveInspection.ProjectionModels]

theorem fresh : GeneralNominalVersionedAllocation231.Fresh snapshot registry root.identity packet.bindings := by
  rw [bindings_empty]
  intro key member
  simp [GeneralNominalVersionedAllocation231.keys,GeneralNominalVersionedAllocation231.declarationKeys,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables] at member

theorem prepared : GeneralNominalVersionedCandidates231.Prepared registry context root declaration := by
  refine ⟨source.metadata,⟨(by intro index; constructor <;> (simp only [GeneralNominalState.sources,List.mem_append]; exact Or.inl (Or.inl (Or.inl (List.mem_ofFn.mpr ⟨(1 : Fin 3),rfl⟩))))),by intro output member; cases member⟩,[(1,1)],rfl,?_,?_,model,head_models model model_retained.1.1⟩
  · exact fresh
  · rw [report_exact]; exact ⟨rfl,rfl,rfl⟩

theorem frame : GeneralNominalVersionedEvidence231.Frame registry refreshed.core root 37 plan :=
  ⟨rfl,rfl,rfl,rfl,raw_sites ▸ List.mem_singleton_self _,centers ▸ List.mem_singleton_self _,List.mem_singleton_self _,rfl,rfl,prepared⟩

theorem children_empty : GeneralNominalVersionedFrame231.children packet = [] := by
  unfold GeneralNominalVersionedFrame231.children GeneralDictionaryEmissionPlans.children
    GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil]
  rfl

theorem emitted_empty : GeneralNominalVersionedPlans231.emittedSchema plan = ⟨[],false⟩ := by
  unfold GeneralNominalVersionedPlans231.emittedSchema GeneralNominalVersionedPlans231.emittedRequests
  simp only [GeneralCanonicalChildOrder.canonicalEmit,GeneralCanonicalChildOrder.canonicalDeclaration,
    GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil]
  rfl

theorem packet_holds (assignment : Assignment) (valid : Models refreshed assignment) :
    GeneralNominalVersionedPlans231.Holds plan assignment := by
  refine ⟨valid.1.1,⟨ordinary assignment,(head_models assignment valid.1.1).2,
    point_root_holds _ _ (fun _ => rfl) _,?_,?_,?_,?_⟩,?_⟩
  · intro name needed
    rcases needed with named | needed
    · simp [Declaration.inputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables] at named
    · obtain ⟨clause,member,_⟩ := needed; cases member
  · rw [head_schema]
    constructor
    · intro test member
      cases List.mem_singleton.mp member
      refine ⟨⟨_,.source _⟩,?_⟩
      intro actual seen; cases seen
      exact scalar assignment valid.1.1
    · intro entry member; cases member
  · rw [emitted_empty]; intro equation member; cases member
  · intro clause member; cases member
  · unfold GeneralNominalVersionedPlans231.Outputs
    rw [emitted_empty]; intro equation member; cases member

end Yulang.GeneralDictionaryMixedGap206Frame234
