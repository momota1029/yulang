import Yulang.GeneralDictionaryClassDelta227

/-! Reuse existing body equations for newly requested outputs of the same name.
Only genuinely new output names add body reads; cross-target equalities remain. -/
namespace Yulang.GeneralDictionaryNameDelta227
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadOutputs (requests EqualOutputs)
open GeneralNominalCenteredHeadMatEffects
open GeneralDictionaryDefault214ActualBodyFrame (bodySources body_iff)
open GeneralDictionaryClassDelta227 (newRequests affected mem_new mem_affected)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree)
open CommonNominalFullCarrier
variable {roles : Roles.RoleDecls}
variable {before after : GeneralNominalCenteredSteps.State roles} {focus : Occurrence roles} {plan : Plan roles}

theorem body_target {model : Assignment} (same : Equivalent (model target).1 (model prior).1)
    (held : BodyHolds plan prior model body) : BodyHolds plan target model body := by
  cases compiled : compileBody plan body with
  | none => simpa only [BodyHolds,bodySchema,compiled] using held
  | some expression =>
      have old := (body_equation compiled).mp held
      exact (body_equation compiled).mpr ⟨subtype_trans same.1 old.1,subtype_trans old.2 same.2⟩

noncomputable def newNames (before after : GeneralNominalCenteredSteps.State roles)
    (focus : Occurrence roles) : List GeneralSourceState.Output := by
  classical
  exact (requests after focus).filter (fun output =>
    ¬ ∃ old ∈ requests before focus, old.name = output.name)

theorem mem_newNames : output ∈ newNames before after focus ↔
    output ∈ requests after focus ∧ ¬ ∃ old ∈ requests before focus, old.name = output.name := by
  classical
  simp [newNames]

theorem newNames_new (member : output ∈ newNames before after focus) :
    output ∈ newRequests before after focus := by
  have parts := mem_newNames.mp member
  exact mem_new.mpr ⟨parts.1,fun old => parts.2 ⟨output,old,rfl⟩⟩

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

theorem class_forward (subset : requests before focus ⊆ requests after focus)
    {first last : Assignment} (old : ClassEffects before focus plan last)
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
  · exact (body_iff plan output.target body
      (fun n present => same n (body_support (mem_newNames.mpr ⟨member,named⟩) found present))).mp
      (valid.1 output member body found)

theorem class_iff (subset : requests before focus ⊆ requests after focus)
    {first last : Assignment} (one : ClassEffects before focus plan first)
    (two : ClassEffects before focus plan last)
    (same : Agree (deltaSources before after focus plan) first last) :
    ClassEffects after focus plan first ↔ ClassEffects after focus plan last :=
  ⟨class_forward subset two same,class_forward subset one (fun n h => (same n h).symm)⟩

theorem delta_subset : deltaSources before after focus plan ⊆
    GeneralDictionaryClassDelta227.deltaSources before after focus plan := by
  intro name member
  rcases List.mem_append.mp member with body | target
  · obtain ⟨output,requested,within⟩ := List.mem_flatMap.mp body
    exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨output,newNames_new requested,within⟩)
  · exact List.mem_append_right _ target

/-- No repeated body reads are needed if every resulting output name was
already represented. This applies equally to explicit, default and override. -/
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
end Yulang.GeneralDictionaryNameDelta227
