import Yulang.GeneralLiveCompoundCulprit316
import Yulang.GeneralVersionedEndpointBatch315

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 42000000
/-! An allocator-only feasibility test on the actual counterexample. Growing
the dictionary compiler's child occurrence/commitment along this allocation
is deliberately not part of this theorem. -/
namespace Yulang.GeneralLiveCompoundProposedRepair316
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralLiveCompoundRegistry316 (registry sourceRegistry declaration otherChild leaf boundary_checked)
open GeneralLiveCompoundLeafInstall316 (after reachable after_model)
open GeneralLiveCompoundChildSite316 (child)
open GeneralLiveCompoundLeafProof316 (w)
open GeneralLiveCompoundPostFrames316 (rootPlan root_frame_plan leaf_evidence)
open GeneralLiveCompoundPostRootHead316 (head schema)
open GeneralLiveCompoundPostRootSelect316 (selected classes)
open GeneralVersionedEndpointBadRow315 (lowerRow)
open GeneralVersionedChildEndpointCut315 (BaseReady)
open GeneralVersionedRecursiveBridge310 (CurrentCandidate)
open GeneralNominalVersionedJournal232 (Effect)
open GeneralNominalVersionedPlans231 (variables emittedSchema)
open GeneralNominalCenteredHeadMatExpressions (value)
open GeneralVersionedEndpointAddress315 (atCell)
open GeneralLiveCompoundCulprit316 (only_lower where_rows)

theorem cursor : GeneralLiveCompoundRoot316.plan ∈ after.plans :=
  List.mem_cons_of_mem _ (List.mem_cons_self ..)

theorem old_lower_row : lowerRow ∈ (emittedSchema GeneralLiveCompoundRoot316.plan).equations := by
  rw [GeneralLiveCompoundInstall316.schema_eq,GeneralDictionaryCompoundVersionedPacket238.emitted_schema,
    GeneralDictionaryCompoundTotal238.emitted_schema]
  exact List.mem_cons_of_mem _ (List.mem_cons_self ..)

theorem choice_compatible : GeneralNominalCycleSteps.ChoiceCompatible after.core.erased.current rootPlan.packet := by
  intro prior member aliased
  change prior ∈ [GeneralLiveCompoundLeafHead316.packet,GeneralLiveCompoundRoot316.packet] at member
  rcases List.mem_cons.mp member with one | last
  · subst prior
    have same := GeneralLiveCompoundAdmin316.alias_eq GeneralLiveCompoundPost316.aliases_after aliased
    exact False.elim ((by decide +kernel : root.identity ≠ child.identity) same)
  · cases List.mem_singleton.mp last
    rfl

theorem feasible_without_rewriting_history :
    ∃ e : Effect roles, CurrentCandidate sourceRegistry after root declaration.id [child] e ∧
      ∃ m, BaseReady after e m ∧
        (m (atCell rootPlan .lower otherChild.id 0 lowerRow.expression)).1 =
          value (variables rootPlan m) .lower lowerRow.expression ∧
        lowerRow.Holds (variables GeneralLiveCompoundRoot316.plan m) m ∧
        GeneralNominalVersionedEvidence231.Evidence registry after.core m child (.node leaf.id []) ∧
        ¬ lowerRow.Holds (variables rootPlan m) m := by
  obtain ⟨e,g,s,o,k,c⟩ := GeneralNominalVersionedMixedSelectedEffect235.source_effect boundary_checked reachable selected
  have f := e.frame
  rw [g,s,o] at f
  have eq := root_frame_plan f
  have before : BaseReady after e w := by
    refine ⟨after_model,?_,?_,?_⟩
    · rw [eq]; exact head
    · rw [eq]; exact schema
    · change GeneralNominalVersionedEffects231.ClassEffects after.core e.plan.packet.site.occurrence e.plan w
      rw [o,eq]; exact classes
  have patched := GeneralVersionedEndpointPatch315.sound_write reachable g s before .lower otherChild.id 0 lowerRow.expression
  let m := GeneralVersionedHighJournal315.patch w (atCell e.plan .lower otherChild.id 0 lowerRow.expression)
    (value (variables e.plan w) .lower lowerRow.expression)
  change BaseReady after e m ∧ _ at patched
  have modelHead : GeneralNominalVersionedPlans231.HeadModels rootPlan.packet m := by rw [← eq]; exact patched.1.2.1
  have stale := (only_lower m patched.1.1 modelHead lowerRow (where_rows.symm ▸ List.mem_cons_self)).mpr rfl
  refine ⟨e,⟨g,s,o,k,c⟩,m,patched.1,?_,
    (patched.1.1.2.1 _ cursor).2.2 lowerRow old_lower_row,leaf_evidence patched.1.1,stale⟩
  have port := patched.2
  rw [eq] at port
  dsimp only [m]
  rw [eq]
  exact port

end Yulang.GeneralLiveCompoundProposedRepair316
