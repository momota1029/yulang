import Yulang.GeneralVersionedEndpointObstruction315
import Yulang.GeneralVersionedChildEndpointCut315

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 23000
set_option maxHeartbeats 18000000
/-! Isolate the one stale protected lower row on the real C307 path.
No facts about a child's judgment are used in the row contradiction. -/
namespace Yulang.GeneralVersionedEndpointBadRow315
open GeneralDictionaryJournalRefinement228Source (roles root width_two)
open GeneralDictionaryCompoundSource238 (registry sourceRegistry declaration child compiled_registry)
open GeneralDictionaryCompoundObstruction238 (oldPlan old_lower associated_value)
open GeneralDictionaryCompoundPoint238 (original_plan_retained)
open GeneralMixedCompoundUpperRefresh307 (upperState)
open GeneralMixedCompoundUpperChild307 (reachable)
open GeneralMixedCompoundUpperRoot307 (plan bindings_exact)
open GeneralVersionedEndpointObstructionHead315 (frame)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedPlans231 (Holds HeadModels variables emittedSchema)
open GeneralNominalCommonBridge (Assignment)
open GeneralVersionedEndpointEquationCut315 (whereRows)
open GeneralNominalMaterialization (Mode)
open GeneralNominalVersionedFrame231 (capture)
open GeneralVersionedEndpointLedger314 (Endpoint)
open GeneralVersionedEndpointCuts315 (occurs merged)
open CommonNominalFullCarrier
open GeneralFiniteTypedWrites312 (symmetric transitive)
open GeneralNominalVersionedJournalFrame236 (sources)

abbrev lowerRow : GeneralNominalCenteredHeadMatSchemas.Equation :=
  ⟨GeneralDictionaryCompoundModel238.names 0,.lower,.variant 0 (.variable 0)⟩

theorem where_member : lowerRow ∈ whereRows plan := by
  unfold whereRows GeneralVersionedRootWrites312.whereRequests
  simp only [GeneralCanonicalChildOrder.canonicalEmit,GeneralCanonicalChildOrder.canonicalDeclaration,
    GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_singleton]
  change lowerRow ∈ [lowerRow,⟨GeneralDictionaryCompoundModel238.names 1,.upper,.variant 0 (.variable 0)⟩]
  exact List.mem_cons_self

theorem endpoint : Endpoint plan lowerRow := by
  refine ⟨child,List.mem_singleton_self _,0,3,.variant 0 (.var 0),.inl rfl,rfl,?_,rfl,rfl,rfl⟩
  intro n no
  cases no

theorem previous : lowerRow ∈ (emittedSchema oldPlan).equations := by
  have f : GeneralNominalVersionedEvidence231.Frame
      (GeneralVersionedHistoryEvidence310.Compiled sourceRegistry) upperState.core root declaration.id plan := frame
  exact GeneralVersionedEndpointLedger314.previous_of_endpoint reachable f original_plan_retained rfl rfl endpoint

theorem protected_row : lowerRow.target ∈ sources upperState := by
  apply List.mem_append_left
  apply List.mem_append_right
  refine List.mem_flatMap.mpr ⟨oldPlan,original_plan_retained,?_⟩
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨lowerRow,previous,List.mem_cons_self⟩

theorem new_operand (m : Assignment) (head : HeadModels plan.packet m) :
    Equivalent (variables plan m .lower 0) (m 2).1 := by
  have eqns : merged plan.packet m :=
    ((GeneralNominalVersionedPlans231.private_models_iff ..).mp head.1).2.2.1
  have raw : occurs plan.packet 0 = [(2,2),(2,2)] := by rw [occurs,bindings_exact]; rfl
  have cut (a : Ty) :=
    GeneralVersionedEndpointCuts315.lower_cut plan.packet m 0 (by decide +kernel) eqns
      (by rw [raw]; decide +kernel) a
  simp only [raw,List.mem_cons,List.not_mem_nil,or_false,or_self,forall_eq] at cut
  change Equivalent (m ((capture plan.packet).inputs 0).1).1 (m 2).1
  exact ⟨(cut _).mpr (subtype_refl _),(cut _).mp (subtype_refl _)⟩

theorem old_operand (m : Assignment) (valid : Models upperState m) :
    Equivalent (variables oldPlan m .lower 0) GeneralDictionaryOptionalOutput229.value := by
  have historic := valid.2.1 oldPlan original_plan_retained
  exact transitive (old_lower m historic) (associated_value m historic)

theorem operands_differ (m : Assignment) (valid : Models upperState m) (head : HeadModels plan.packet m) :
    ¬ Equivalent (variables oldPlan m .lower 0) (variables plan m .lower 0) := by
  intro same
  have width := width_two m (valid.2.1 oldPlan original_plan_retained).1
  exact GeneralDictionaryOptionalOutput229.not_width
    (transitive (symmetric (old_operand m valid)) (transitive same (transitive (new_operand m head) width)))

theorem cannot_preserve (m : Assignment) (valid : Models upperState m) (head : HeadModels plan.packet m) :
    ¬ lowerRow.Holds (variables plan m) m := by
  intro new
  have old := (valid.2.1 oldPlan original_plan_retained).2.2 lowerRow previous
  change Equivalent (m lowerRow.target).1 (variant 0 (variables oldPlan m .lower 0)) at old
  change Equivalent (m lowerRow.target).1 (variant 0 (variables plan m .lower 0)) at new
  obtain ⟨ab,ba⟩ := transitive (symmetric old) new
  exact operands_differ m valid head
    ⟨(common_variant_iff ..).mp ab,(common_variant_iff ..).mp ba⟩

end Yulang.GeneralVersionedEndpointBadRow315
