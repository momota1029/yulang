import Yulang.GeneralDictionaryLiveDelta227

/-! Relative support of class effects: old bodies and old/old equal-output
pairs are supplied by the old journal. Only new requests and cross pairs read
an added support. No request, default body, or equality is discarded. -/
namespace Yulang.GeneralDictionaryClassDelta227
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadOutputs (requests EqualOutputs)
open GeneralNominalCenteredHeadMatEffects (ClassEffects BodyHolds)
open GeneralDictionaryDefault214ActualBodyFrame (bodySources body_iff classSources)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree)
variable {roles : Roles.RoleDecls}
variable {before after : GeneralNominalCenteredSteps.State roles} {focus : Occurrence roles} {plan : Plan roles}

noncomputable def newRequests (before after : GeneralNominalCenteredSteps.State roles)
    (focus : Occurrence roles) : List GeneralSourceState.Output := by
  classical
  exact (requests after focus).filter (fun output => output ∉ requests before focus)

theorem mem_new : output ∈ newRequests before after focus ↔
    output ∈ requests after focus ∧ output ∉ requests before focus := by
  classical
  simp [newRequests]

/-- Old targets are needed only for names shared with a new request. -/
noncomputable def affected (before after : GeneralNominalCenteredSteps.State roles)
    (focus : Occurrence roles) : List GeneralSourceState.Output := by
  classical
  exact (requests after focus).filter (fun output =>
    ∃ fresh ∈ newRequests before after focus, output.name = fresh.name)

theorem mem_affected : output ∈ affected before after focus ↔
    output ∈ requests after focus ∧
      ∃ fresh ∈ newRequests before after focus, output.name = fresh.name := by
  classical
  simp [affected]

noncomputable def deltaSources (before after : GeneralNominalCenteredSteps.State roles)
    (focus : Occurrence roles) (plan : Plan roles) : List Nat :=
  (newRequests before after focus).flatMap (fun output =>
    ((GeneralDictionaryAssociatedProvenance.lookup roles plan.packet.declaration output.name).toList.flatMap
      fun body => bodySources plan output.target body)) ++
    (affected before after focus).map (·.target)

theorem body_support (requested : output ∈ newRequests before after focus)
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

/-- Transport relative to old class validity on both assignments. This does
not assume current class validity or a same-assignment completion. -/
theorem class_forward (before after : GeneralNominalCenteredSteps.State roles)
    (focus : Occurrence roles) (plan : Plan roles) {first last : Assignment}
    (old : ClassEffects before focus plan last)
    (same : Agree (deltaSources before after focus plan) first last)
    (valid : ClassEffects after focus plan first) : ClassEffects after focus plan last := by
  classical
  constructor
  · intro output member body found
    by_cases previous : output ∈ requests before focus
    · exact old.1 output previous body found
    · exact (body_iff plan output.target body
        (fun name present => same name (body_support (mem_new.mpr ⟨member,previous⟩) found present))).mp
        (valid.1 output member body found)
  · intro a one b two named
    by_cases oldA : a ∈ requests before focus
    · by_cases oldB : b ∈ requests before focus
      · exact old.2 a oldA b oldB named
      · have fresh := mem_new.mpr ⟨two,oldB⟩
        have oneEq := same a.target (target_support one fresh named)
        have twoEq := same b.target (target_support two fresh rfl)
        rw [← oneEq,← twoEq]
        exact valid.2 a one b two named
    · have fresh := mem_new.mpr ⟨one,oldA⟩
      have oneEq := same a.target (target_support one fresh rfl)
      have twoEq := same b.target (target_support two fresh named.symm)
      rw [← oneEq,← twoEq]
      exact valid.2 a one b two named

theorem class_iff (before after : GeneralNominalCenteredSteps.State roles)
    (focus : Occurrence roles) (plan : Plan roles) {first last : Assignment}
    (one : ClassEffects before focus plan first) (two : ClassEffects before focus plan last)
    (same : Agree (deltaSources before after focus plan) first last) :
    ClassEffects after focus plan first ↔ ClassEffects after focus plan last :=
  ⟨class_forward before after focus plan two same,
    class_forward before after focus plan one (fun n h => (same n h).symm)⟩

theorem delta_subset (before after : GeneralNominalCenteredSteps.State roles)
    (focus : Occurrence roles) (plan : Plan roles) :
    deltaSources before after focus plan ⊆ classSources after focus plan := by
  intro name member
  rcases List.mem_append.mp member with body | target
  · obtain ⟨output,requested,within⟩ := List.mem_flatMap.mp body
    exact List.mem_flatMap.mpr ⟨output,(mem_new.mp requested).1,List.mem_cons_of_mem _ within⟩
  · obtain ⟨output,requested,rfl⟩ := List.mem_map.mp target
    exact List.mem_flatMap.mpr ⟨output,(mem_affected.mp requested).1,List.mem_cons_self ..⟩

/-- If the request sets are unchanged, no historical live support is added. -/
theorem no_new (same : ∀ output, output ∈ requests after focus → output ∈ requests before focus) :
    deltaSources before after focus plan = [] := by
  classical
  have empty : newRequests before after focus = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro output member
    have parts := mem_new.mp member
    exact parts.2 (same output parts.1)
  have affectedEmpty : affected before after focus = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro output member
    obtain ⟨_,fresh,present,_⟩ := mem_affected.mp member
    simp [empty] at present
  simp [deltaSources,empty,affectedEmpty]
end Yulang.GeneralDictionaryClassDelta227
