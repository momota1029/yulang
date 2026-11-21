import Yulang.GeneralWherePhysicalChildRead319

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 33000
set_option maxHeartbeats 35000000
namespace Yulang.GeneralWherePhysicalChildModel319
open CommonNominalFullCarrier
open GeneralWherePhysicalCommit319 (final newChild models emission)
open GeneralWherePhysicalChildRead319 (plan packet binding actual_report query)
open GeneralWherePhysicalCurrentRead319 (child_bounds)
open GeneralWherePhysicalPatch319 (n)
open GeneralWherePhysicalActive319 (active ctx)
open GeneralWherePhysicalFresh319 (lowerSlot upperSlot oldTwo lower_id upper_id oldTwo_id)
open GeneralWhereOriginSingleCells318 (loNow hi sig)
open GeneralLiveCompoundRegistry316 (leaf otherChild)
open GeneralNominalCenters
open GeneralNominalRecursiveCandidates (report)
open GeneralNominalRecursiveInspection
open GeneralNominalVersionedPlans231 (Ordinary HeadModels SchemaHolds Holds Outputs)
open GeneralNominalVersionedFrame231 (capture binder)
open GeneralMixedCompoundChildEquality307 (mid)
open GeneralNominalCommonBridge (Assignment)

abbrev ref : Origin := .source mid
abbrev project : Origin := .structural ref (.variant 0) 0

theorem child_center : newChild.center (0 : Fin 1) = mid := rfl

theorem capture_at : (capture packet).inputs 0 = (2,2) := by
  change (GeneralNominalVersionedAllocation231.capture _ _ _ _ packet.bindings).inputs 0 = _
  rw [binding]
  rfl

theorem binder_at : binder plan 0 = 2 := by
  unfold binder
  change (if (0:Nat) ∈ leaf.outputNames then _ else if
    ((capture packet).inputs 0).1 = ((capture packet).inputs 0).2 then _ else _) = _
  simp [capture_at,show (0:Nat) ∉ leaf.outputNames from by decide]

theorem ports (m : Assignment) (valid : GeneralWhereVersionInstall317.Models final m) :
    Equivalent (m loNow).1 (variant 0 (m 2).1) ∧ Equivalent (m hi).1 (variant 0 (m 2).1) := by
  have raw : GeneralNominalState.Models active m := valid.1.1.1
  have l := GeneralNominalCommonBridge.rewrites_sound GeneralWherePhysicalActive319.lower_shape m raw.1
  have u := GeneralNominalCommonBridge.rewrites_sound GeneralWherePhysicalActive319.upper_shape m raw.1
  change Equivalent (m (active.base.source lowerSlot)).1 (variant 0 (m (active.base.source oldTwo)).1) at l
  change Equivalent (m (active.base.source upperSlot)).1 (variant 0 (m (active.base.source oldTwo)).1) at u
  rw [show active.base.source lowerSlot = loNow from lower_id,show active.base.source oldTwo = 2 from oldTwo_id] at l
  rw [show active.base.source upperSlot = hi from upper_id,show active.base.source oldTwo = 2 from oldTwo_id] at u
  exact ⟨l,u⟩

theorem projection (m : Assignment) : ProjectionModels active (GeneralNominalPacketSupport.report packet) m := by
  change ProjectionModels active (report ctx leaf [(lowerSlot,upperSlot)]) m
  rw [actual_report]
  refine ⟨(fun _ h => nomatch h),(fun _ h => nomatch h),?_,?_⟩
  · intro first present
    cases List.mem_singleton.mp present
    intro _ _ _ _ absent; cases absent
  · intro first present
    cases List.mem_singleton.mp present
    intro _ _ _ _ _ absent; cases absent

theorem ordinary (m : Assignment) (valid : GeneralWhereVersionInstall317.Models final m) :
    Ordinary packet m := by
  refine ⟨?_,?_,?_⟩
  · rw [binding]
    intro a ha b hb _
    cases List.mem_singleton.mp ha
    cases List.mem_singleton.mp hb
    exact subtype_refl _
  · unfold GeneralNominalVersionedAllocation231.merges
    rw [binding]
    exact PresenceNormalForm.all_nil _ _
  · change PresenceNormalForm.All CommonNominalFullCarrier.model m (selfChecks active (report ctx leaf _))
    rw [actual_report]
    intro atom member
    simp only [selfChecks,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
    have less : Subtype (m (active.base.source lowerSlot)).1 (m (active.base.source upperSlot)).1 := by
      rw [show active.base.source lowerSlot = loNow from lower_id,show active.base.source upperSlot = hi from upper_id]
      exact subtype_trans (ports m valid).1.1 (ports m valid).2.2
    rcases member with rfl|rfl|rfl
    · exact less
    · exact less
    · exact subtype_refl _

theorem head (m : Assignment) (valid : GeneralWhereVersionInstall317.Models final m) :
    HeadModels packet m :=
  ⟨(GeneralNominalVersionedPlans231.private_models_iff ..).mpr ⟨valid.1.1.1,ordinary m valid⟩,projection m⟩

theorem mid_value (m : Assignment) (valid : GeneralWhereVersionInstall317.Models final m) :
    Equivalent (m mid).1 (variant 0 (m 2).1) := by
  let parent := GeneralWherePhysicalCurrentRead319.plan
  have recorded : parent ∈ final.versionedWhere := List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have body := ((valid.2 parent recorded).1.childSemantics otherChild (List.mem_singleton_self _) sig).2
  rw [GeneralWherePhysicalCurrentModel319.exact_child sig] at body
  have value := body _ (List.mem_singleton_self _)
  change Equivalent (m mid).1 (variant 0 (GeneralNominalVersionedPlans231.variables parent m .actual 0)) at value
  have b : GeneralNominalVersionedPlans231.variables parent m .actual 0 = (m 2).1 := by
    change (m (binder parent 0)).1 = _
    rw [GeneralWherePhysicalCurrentModel319.binder_now 0 (.inl rfl)]
  rwa [b] at value

theorem site_holds (m : Assignment) (valid : GeneralWhereVersionInstall317.Models final m) :
    newChild.Holds m := by
  let parent := GeneralWherePhysicalCurrentRead319.plan
  have recorded : parent ∈ final.versionedWhere := List.mem_cons_of_mem _ (List.mem_singleton_self _)
  exact ((valid.2 parent recorded).1.childSemantics otherChild (List.mem_singleton_self _) sig).1

theorem head_schema : plan.headSchema =
    { tests := [(ref,.structural (.variant 0))]
      variables := [⟨0,project,.actual⟩] } := by
  unfold Plan.headSchema
  rw [query]
  simp [GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,ref,project,plan,child_center,List.ofFn_succ]

theorem observed (m : Assignment) (valid : GeneralWhereVersionInstall317.Models final m) :
    Observes m project (m 2).1 :=
  .structural (.source _) (values := [(m 2).1]) rfl (mid_value m valid) rfl

theorem schema (m : Assignment) (valid : GeneralWhereVersionInstall317.Models final m) :
    SchemaHolds plan plan.headSchema m := by
  rw [head_schema]
  constructor
  · intro test member
    cases List.mem_singleton.mp member
    refine ⟨⟨_,.source _⟩,?_⟩
    intro value seen
    cases seen
    exact ⟨[(m 2).1],rfl,mid_value m valid⟩
  · intro entry member
    cases List.mem_singleton.mp member
    change GeneralNominalOriginTerms.Same m project (.source (binder plan 0))
    rw [binder_at]
    refine ⟨⟨_,observed m valid⟩,⟨_,.source _⟩,?_⟩
    intro x y hx hy
    cases hy
    exact GeneralLiveCompoundDepth316.variant_child
      (root := ref) (tag := 0)
      (by intro v seen; cases seen; exact mid_value m valid)
      (.structural (.variant 0)) (0 : Fin 1) hx

theorem emitted : GeneralNominalVersionedPlans231.emittedSchema plan = ⟨[],false⟩ := by
  unfold GeneralNominalVersionedPlans231.emittedSchema GeneralNominalVersionedPlans231.emittedRequests
    GeneralNominalMaterialization.rootRequests
  simp [GeneralCanonicalChildOrder.canonicalEmit,GeneralCanonicalChildOrder.canonicalDeclaration,
    GeneralCanonicalChildOrder.canonicalRequirements]
  rfl

theorem held (m : Assignment) (valid : GeneralWhereVersionInstall317.Models final m) : Holds plan m := by
  refine ⟨valid.1.1.1,⟨ordinary m valid,projection m,site_holds m valid,?_,schema m valid,?_,?_⟩,?_⟩
  · intro name member
    rcases member with input | ⟨clause,present,_⟩
    · have eq : name = 0 := List.mem_singleton.mp input
      subst name
      rw [capture_at,binder_at]
      exact ⟨subtype_refl _,subtype_refl _⟩
    · cases present
  · rw [emitted]; intro _ absent; cases absent
  · intro _ absent; cases absent
  · unfold Outputs; rw [emitted]; intro _ absent; cases absent

end Yulang.GeneralWherePhysicalChildModel319
