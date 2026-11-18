import Yulang.GeneralRebaseSourceMeaning263
import Yulang.GeneralNominalCenteredHeadAllocMergeInstall
set_option backward.isDefEq.respectTransparency false
namespace Yulang.Cycle263SourceHeadsProbe
open GeneralNominalCenteredHeadAllocMergeSource
open GeneralNominalCenteredHeadAllocMergeInstall (uniform)
open GeneralNominalCenters GeneralNominalVersionedJournal232
open GeneralRebaseSourceRepresentatives263 (SourceHeads)

private theorem head (plan : Plan roles)
 (metadata : GeneralRebaseRegisteredPlan263.Metadata registry context plan) :
 GeneralNominalVersionedPlans231.SchemaHolds plan plan.headSchema uniform := by
 apply (GeneralRebaseHeadSupport263.head_iff plan uniform).mpr
 have visible := metadata.visible
 change plan.packet.declaration ∈ [declaration,GeneralNominalCenteredHeadAllocEncoding.declaration leaf] at visible
 rcases List.mem_cons.mp visible with same | same
 · have query : GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation plan.packet.declaration = [.scalar .int] := by
    unfold GeneralNominalInspection.queries
    rw [same,metadata.constructors,metadata.interpretation]
    exact GeneralNominalCenteredHeadAllocMergeInstall.query
   unfold Plan.SchemaHolds Plan.headSchema
   rw [query]
   simp only [GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,
     GeneralNominalMaterialization.Schema.append,List.append_nil]
   constructor
   · intro test member
     change test ∈ [(.source ((List.ofFn plan.input.center)[0]?.getD 0),.scalar .int)] at member
     have equal : test = (.source ((List.ofFn plan.input.center)[0]?.getD 0),.scalar .int) := List.mem_singleton.mp member
     cases equal
     refine ⟨⟨_,.source _⟩,?_⟩
     intro value observed
     cases observed
     exact GeneralDictionaryDefaultExpression209.equivalent_refl _
   · intro entry member
     change entry ∈ [] at member
     cases member
 · have same := List.mem_singleton.mp same
   have query : GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation plan.packet.declaration = [] := by
    unfold GeneralNominalInspection.queries
    rw [same]
    rfl
   unfold Plan.SchemaHolds Plan.headSchema
   rw [query]
   simp only [GeneralNominalMaterialization.schemas]
   constructor
   · intro test member
     change test ∈ [] at member
     cases member
   · intro entry member
     change entry ∈ [] at member
     cases member

abbrev versionedStart := GeneralNominalVersionedJournal232.initial context root

theorem formed : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial
 sourceRegistry root versionedStart := ⟨start,initial_source,rfl⟩

theorem all_future_heads : SourceHeads sourceRegistry root versionedStart uniform := by
 intro state path plan member
 exact head plan (GeneralRebaseRegisteredPlan263.metadata registry context root state path plan member)

theorem context_inhabited : ∃ assignment,
 GeneralRebaseSourceMeaning263.Context (fun _ => True) sourceRegistry root versionedStart assignment :=
 ⟨uniform,True.intro,all_future_heads⟩
theorem actual_base_context : GeneralRebaseSourceMeaning263.Context
 (GeneralNominalVersionedJournal232.Models versionedStart) sourceRegistry root versionedStart uniform := by
 refine ⟨?_,all_future_heads⟩
 apply (GeneralNominalVersionedJournal232.initial_models context root uniform).mpr
 exact ⟨GeneralNominalCenteredHeadAllocMergeInstall.source_uniform,
   fun _ => ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩⟩

#print axioms formed
#print axioms all_future_heads
#print axioms context_inhabited
#print axioms actual_base_context
end Yulang.Cycle263SourceHeadsProbe
