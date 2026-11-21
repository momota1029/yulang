import Yulang.GeneralVersionedEndpointSourceKey315
import Yulang.GeneralVersionedEndpointBadRow315

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 18000000
/-! On the actual obstruction, the proposed single lower cell can coexist
with the historical cell. The existing compiler still emits the old
address: no new transition or class result is asserted by this test. -/
namespace Yulang.GeneralVersionedEndpointPatchCase315
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryCompoundSource238 (sourceRegistry registry declaration child)
open GeneralDictionaryCompoundObstruction238 (oldPlan)
open GeneralDictionaryCompoundPoint238 (original_plan_retained)
open GeneralDictionaryCompoundSites238 (childSite)
open GeneralMixedCompoundUpperRefresh307 (upperState)
open GeneralMixedCompoundUpperRoot307 (plan frame_plan)
open GeneralMixedCompoundUpperChild307 (reachable)
open GeneralVersionedEndpointObstruction315 (checked_source)
open GeneralVersionedEndpointObstructionSelect315 (selected class_effects)
open GeneralVersionedEndpointObstructionHead315 (valid head schema)
open GeneralVersionedEndpointBadRow315 (lowerRow previous operands_differ cannot_preserve)
open GeneralDictionaryCompoundPointModel238 (extended)
open GeneralVersionedEndpointAddress315 (atCell coherent)
open GeneralVersionedChildEndpointCut315 (BaseReady)
open GeneralVersionedRecursiveBridge310 (CurrentCandidate)
open GeneralNominalVersionedPlans231 (variables)
open GeneralNominalVersionedJournal232 (Effect)
open GeneralNominalCenteredHeadMatExpressions (value)
open CommonNominalFullCarrier

theorem narrowed_address_changes :
    atCell oldPlan .lower child.id 0 lowerRow.expression ≠
      atCell plan .lower child.id 0 lowerRow.expression := by
  intro collision
  have same := coherent (p := oldPlan) (q := plan) (side := .lower) (c := child.id) (d := child.id)
    (i := 0) (j := 0) (e := lowerRow.expression) rfl collision extended
  change variant 0 (variables oldPlan extended .lower 0) =
    variant 0 (variables plan extended .lower 0) at same
  have both : Equivalent (variant 0 (variables oldPlan extended .lower 0))
      (variant 0 (variables plan extended .lower 0)) := by
    rw [same]
    exact ⟨subtype_refl _,subtype_refl _⟩
  exact operands_differ extended valid head ⟨(common_variant_iff ..).mp both.1,(common_variant_iff ..).mp both.2⟩

theorem preserves_old_and_sets_new :
    ∃ e : Effect roles, CurrentCandidate sourceRegistry upperState root declaration.id [childSite.occurrence] e ∧
      ∃ model, BaseReady upperState e model ∧
        (model (atCell plan .lower child.id 0 lowerRow.expression)).1 =
          value (variables plan model) .lower lowerRow.expression ∧
        lowerRow.Holds (variables oldPlan model) model ∧
        ¬ lowerRow.Holds (variables plan model) model := by
  obtain ⟨e,g,s,o,k,c⟩ := GeneralNominalVersionedMixedSelectedEffect235.source_effect checked_source reachable selected
  have f := e.frame
  rw [g,s,o] at f
  have eq := frame_plan f
  have before : BaseReady upperState e extended := by
    refine ⟨valid,?_,?_,?_⟩
    · rw [eq]; exact head
    · rw [eq]; exact schema
    · change GeneralNominalVersionedEffects231.ClassEffects upperState.core e.plan.packet.site.occurrence e.plan extended
      rw [o,eq]; exact class_effects
  have patched := GeneralVersionedEndpointPatch315.sound_write reachable g s before
    .lower child.id 0 lowerRow.expression
  let model := GeneralVersionedHighJournal315.patch extended (atCell e.plan .lower child.id 0 lowerRow.expression)
    (value (variables e.plan extended) .lower lowerRow.expression)
  change BaseReady upperState e model ∧ _ at patched
  have modelHead : GeneralNominalVersionedPlans231.HeadModels plan.packet model := by
    rw [← eq]; exact patched.1.2.1
  refine ⟨e,⟨g,s,o,k,c⟩,model,patched.1,?_,
    (patched.1.1.2.1 oldPlan original_plan_retained).2.2 lowerRow previous,
    cannot_preserve model patched.1.1 modelHead⟩
  have port := patched.2
  rw [eq] at port
  dsimp only [model]
  rw [eq]
  exact port

end Yulang.GeneralVersionedEndpointPatchCase315
