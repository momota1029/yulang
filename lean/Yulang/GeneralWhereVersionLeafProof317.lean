import Yulang.GeneralWhereVersionLeafHead317

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 31000
set_option maxHeartbeats 38000000
namespace Yulang.GeneralWhereVersionLeafProof317
open GeneralWhereVersionCase317 (site occ centers_preserved)
open GeneralWhereVersionCommit317 (corrected_site new_snapshot)
open GeneralWhereVersionWitness317 (ParentHolds)
open GeneralWhereVersionLeafHead317 (packet plan ordinary projections capture binder query)
open GeneralLiveCompoundRegistry316 (leaf)
open GeneralNominalVersionedPlans231
open GeneralNominalCenters
open GeneralNominalRecursiveInspection (Origin Observes)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

abbrev mid := GeneralMixedCompoundChildEquality307.mid
abbrev ref : Origin := .source mid
abbrev projection : Origin := .structural ref (.variant 0) 0

theorem mid_value (m : Assignment) (valid : ParentHolds m) :
    Equivalent (m mid).1 (variant 0 (m 2).1) := by
  have old := GeneralLiveCompoundPostFeedback316.old_valid m valid.1
  exact GeneralMixedCompoundChildEquality307.historical_child_center m
    (GeneralMixedCompoundUpperSupport307.child_history m old)

theorem head_schema : plan.headSchema =
    ⟨[⟨0,projection,.actual⟩],[(ref,.structural (.variant 0))],false⟩ := by
  unfold Plan.headSchema
  change GeneralNominalMaterialization.schemas
    (GeneralNominalInspection.queries GeneralWhereVersionSnapshot317.snap
      GeneralWhereVersionSnapshot317.context.interpretation leaf)
    (fun index => .source ((List.ofFn site.center)[index]?.getD 0)) .actual 0 = _
  rw [query]
  simp [GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,ref,projection,centers_preserved]

theorem observed (m : Assignment) (valid : ParentHolds m) : Observes m projection (m 2).1 :=
  .structural (.source _) (values := [(m 2).1]) rfl (mid_value m valid) rfl

theorem schema (m : Assignment) (valid : ParentHolds m) :
    SchemaHolds plan plan.headSchema m := by
  rw [head_schema]
  constructor
  · intro test member
    cases List.mem_singleton.mp member
    refine ⟨⟨_,.source _⟩,?_⟩
    intro _ seen
    cases seen
    exact ⟨[(m 2).1],rfl,mid_value m valid⟩
  · intro entry member
    cases List.mem_singleton.mp member
    change GeneralNominalOriginTerms.Same m projection (.source (GeneralNominalVersionedFrame231.binder plan 0))
    rw [binder]
    refine ⟨⟨_,observed m valid⟩,⟨_,.source _⟩,?_⟩
    intro x y hx hy
    cases hy
    exact GeneralLiveCompoundDepth316.variant_child
      (root := ref) (tag := 0)
      (by intro v seen; cases seen; exact mid_value m valid)
      (.structural (.variant 0)) (0 : Fin 1) hx

theorem emitted : emittedSchema plan = ⟨[],false⟩ := by
  unfold emittedSchema emittedRequests GeneralNominalMaterialization.rootRequests
  simp [GeneralCanonicalChildOrder.canonicalEmit,GeneralCanonicalChildOrder.canonicalDeclaration,
    GeneralCanonicalChildOrder.canonicalRequirements]
  rfl

theorem terminal : GeneralNominalVersionedFrame231.children packet = [] := by
  unfold GeneralNominalVersionedFrame231.children GeneralDictionaryEmissionPlans.children
    GeneralCanonicalChildOrder.canonicalEmit GeneralCanonicalChildOrder.canonicalDeclaration
    GeneralCanonicalChildOrder.canonicalRequirements GeneralDeclarationDemands.emitAll
  simp [List.mergeSort_nil]

theorem holds (m : Assignment) (valid : ParentHolds m) : Holds plan m := by
  refine ⟨new_snapshot m valid,⟨ordinary m valid,projections m,corrected_site m valid,?_,schema m valid,?_,?_⟩,?_⟩
  · intro name member
    rcases member with input | ⟨clause,present,_⟩
    · have eq : name = 0 := List.mem_singleton.mp input
      subst name
      rw [capture,binder]
      exact ⟨subtype_refl _,subtype_refl _⟩
    · cases present
  · rw [emitted]; intro _ absent; cases absent
  · intro _ absent; cases absent
  · unfold Outputs; rw [emitted]; intro _ absent; cases absent

end Yulang.GeneralWhereVersionLeafProof317
