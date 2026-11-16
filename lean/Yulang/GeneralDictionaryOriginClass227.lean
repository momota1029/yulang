import Yulang.GeneralDictionaryHistoricalBody227
import Yulang.GeneralDictionaryNameDelta227

/-! Class equations use semantic input-origin readback. Only new output names
add body reads to historical class extensions; all cross-target equalities
remain represented. Defaults and explicit overrides use the same lookup. -/
namespace Yulang.GeneralDictionaryOriginClass227
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadOutputs (requests EqualOutputs)
open GeneralNominalCenteredHeadMatEffects
open GeneralDictionaryHistoricalBody227 (bodySources body_iff)
open GeneralDictionaryClassDelta227 (newRequests affected mem_new mem_affected)
open GeneralDictionaryNameDelta227 (newNames mem_newNames newNames_new body_target)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralNominalRecursiveInspection (Finished)
open GeneralNominalQueryProvenance183 (headInspection)
variable {roles : Roles.RoleDecls}
variable {before after : GeneralNominalCenteredSteps.State roles} {focus : Occurrence roles} {plan : Plan roles}

noncomputable def classSources (state : GeneralNominalCenteredSteps.State roles)
    (focus : Occurrence roles) (plan : Plan roles) : List Nat :=
  (requests state focus).flatMap fun output =>
    output.target :: ((GeneralDictionaryAssociatedProvenance.lookup roles plan.packet.declaration output.name).toList.flatMap
      fun body => bodySources plan output.target body)

theorem class_iff (state : GeneralNominalCenteredSteps.State roles)
    (focus : Occurrence roles) (plan : Plan roles) {first last : Assignment}
    (finished : Finished (headInspection plan))
    (one : plan.SchemaHolds plan.headSchema first) (two : plan.SchemaHolds plan.headSchema last)
    (same : Agree (classSources state focus plan) first last) :
    ClassEffects state focus plan first ↔ ClassEffects state focus plan last := by
  have target output (member : output ∈ requests state focus) : first output.target = last output.target :=
    same _ (List.mem_flatMap.mpr ⟨output,member,List.mem_cons_self ..⟩)
  unfold ClassEffects
  apply and_congr
  · apply forall_congr'; intro output
    apply forall_congr'; intro member
    apply forall_congr'; intro body
    apply forall_congr'; intro found
    have supplied := (GeneralDictionaryAssociatedProvenance.lookup_exact roles plan.packet.declaration
      plan.packet.checked.identified.2.2.1 output.name body).mp found
    apply body_iff plan output.target body supplied finished one two
    intro name present
    exact same name (List.mem_flatMap.mpr ⟨output,member,List.mem_cons_of_mem _
      (List.mem_flatMap.mpr ⟨body,Option.mem_toList.mpr found,present⟩)⟩)
  · unfold EqualOutputs
    apply forall_congr'; intro a
    apply forall_congr'; intro aMember
    apply forall_congr'; intro b
    apply forall_congr'; intro bMember
    rw [target a aMember,target b bMember]

noncomputable def deltaSources (before after : GeneralNominalCenteredSteps.State roles)
    (focus : Occurrence roles) (plan : Plan roles) : List Nat :=
  (newNames before after focus).flatMap (fun output =>
    ((GeneralDictionaryAssociatedProvenance.lookup roles plan.packet.declaration output.name).toList.flatMap
      fun body => bodySources plan output.target body)) ++
    (affected before after focus).map (·.target)

theorem body_support (requested : output ∈ newNames before after focus)
    (found : GeneralDictionaryAssociatedProvenance.lookup roles plan.packet.declaration output.name = some body)
    (present : name ∈ bodySources plan output.target body) :
    name ∈ deltaSources before after focus plan :=
  List.mem_append_left _ (List.mem_flatMap.mpr ⟨output,requested,
    List.mem_flatMap.mpr ⟨body,Option.mem_toList.mpr found,present⟩⟩)

theorem target_support (requested : output ∈ requests after focus)
    (fresh : other ∈ newRequests before after focus) (sameName : output.name = other.name) :
    output.target ∈ deltaSources before after focus plan :=
  List.mem_append_right _ (List.mem_map.mpr ⟨output,
    mem_affected.mpr ⟨requested,other,fresh,sameName⟩,rfl⟩)

theorem equal_forward {first last : Assignment}
    (old : EqualOutputs before focus last)
    (same : Agree (deltaSources before after focus plan) first last)
    (valid : EqualOutputs after focus first) : EqualOutputs after focus last := by
  classical
  intro a one b two named
  by_cases oldA : a ∈ requests before focus
  · by_cases oldB : b ∈ requests before focus
    · exact old a oldA b oldB named
    · have fresh := mem_new.mpr ⟨two,oldB⟩
      have oneEq := same a.target (target_support one fresh named)
      have twoEq := same b.target (target_support two fresh rfl)
      rw [← oneEq,← twoEq]
      exact valid a one b two named
  · have fresh := mem_new.mpr ⟨one,oldA⟩
    have oneEq := same a.target (target_support one fresh rfl)
    have twoEq := same b.target (target_support two fresh named.symm)
    rw [← oneEq,← twoEq]
    exact valid a one b two named

/-- Readback and historical-name reuse apply together, not as independent
approximations of the effect predicate. -/
theorem relative_forward (subset : requests before focus ⊆ requests after focus)
    {first last : Assignment} (finished : Finished (headInspection plan))
    (headOne : plan.SchemaHolds plan.headSchema first) (headTwo : plan.SchemaHolds plan.headSchema last)
    (old : ClassEffects before focus plan last)
    (same : Agree (deltaSources before after focus plan) first last)
    (valid : ClassEffects after focus plan first) : ClassEffects after focus plan last := by
  classical
  have equal := equal_forward old.2 same valid.2
  refine ⟨?_,equal⟩
  intro output member body found
  by_cases named : ∃ prior ∈ requests before focus, prior.name = output.name
  · obtain ⟨prior,registered,names⟩ := named
    exact body_target (equal output member prior (subset registered) names.symm)
      (old.1 prior registered body (names.symm ▸ found))
  · have supplied := (GeneralDictionaryAssociatedProvenance.lookup_exact roles plan.packet.declaration
      plan.packet.checked.identified.2.2.1 output.name body).mp found
    exact (body_iff plan output.target body supplied finished headOne headTwo
      (fun n present => same n (body_support (mem_newNames.mpr ⟨member,named⟩) found present))).mp
      (valid.1 output member body found)

theorem relative_iff (subset : requests before focus ⊆ requests after focus)
    {first last : Assignment} (finished : Finished (headInspection plan))
    (headOne : plan.SchemaHolds plan.headSchema first) (headTwo : plan.SchemaHolds plan.headSchema last)
    (one : ClassEffects before focus plan first) (two : ClassEffects before focus plan last)
    (same : Agree (deltaSources before after focus plan) first last) :
    ClassEffects after focus plan first ↔ ClassEffects after focus plan last :=
  ⟨relative_forward subset finished headOne headTwo two same,
    relative_forward subset finished headTwo headOne one (fun n h => (same n h).symm)⟩

theorem delta_subset : deltaSources before after focus plan ⊆ classSources after focus plan := by
  intro name member
  rcases List.mem_append.mp member with body | target
  · obtain ⟨output,requested,within⟩ := List.mem_flatMap.mp body
    exact List.mem_flatMap.mpr ⟨output,(mem_newNames.mp requested).1,List.mem_cons_of_mem _ within⟩
  · obtain ⟨output,requested,rfl⟩ := List.mem_map.mp target
    exact List.mem_flatMap.mpr ⟨output,(mem_affected.mp requested).1,List.mem_cons_self ..⟩

theorem names_covered (covered : ∀ output ∈ requests after focus,
    ∃ prior ∈ requests before focus, prior.name = output.name) :
    deltaSources before after focus plan = (affected before after focus).map (·.target) := by
  classical
  have empty : newNames before after focus = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro output member
    have parts := mem_newNames.mp member
    exact parts.2 (covered output parts.1)
  simp [deltaSources,empty]

end Yulang.GeneralDictionaryOriginClass227
