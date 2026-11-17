import Yulang.GeneralDictionaryOriginClass227

/-! Exact local provenance of non-output allocation namespaces in semantic
body/class support. Such a source must already be an input center or requested
output target; no full-trace freshness or historic ownership is inferred. -/
namespace Yulang.GeneralDictionaryBodyProvenance227
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralDictionaryHistoricalBody227 (headRoots bodySources)
open GeneralDictionaryAssociatedProvenance (Body)
open GeneralNominalCenteredHeadMatEffects
open GeneralNominalCenteredModelExtension (originSource)
variable {roles : Roles.RoleDecls} {plan : Plan roles}

def externalSources (plan : Plan roles) : List Nat :=
  List.ofFn plan.input.center ++ [0] ++ plan.packet.declaration.outputNames.map plan.binder

theorem head_roots_subset (plan : Plan roles) :
    headRoots plan ⊆ List.ofFn plan.input.center ++ [0] := by
  intro name member
  obtain ⟨entry,present,rfl⟩ := List.mem_map.mp member
  exact (GeneralDictionaryDefault214ActualSupport.head_roots plan).2 entry present

/-- Covers explicit, default and override without a supplies or compilation
success premise. Failed compilation has empty default body support. -/
theorem body_subset (plan : Plan roles) (target : Nat) (body : Body) :
    bodySources plan target body ⊆ target :: externalSources plan := by
  intro name member
  cases body with
  | explicit equation =>
    rcases List.mem_cons.mp member with equal | rest
    · exact List.mem_cons.mpr (Or.inl equal)
    · rcases List.mem_append.mp rest with origin | output
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ (head_roots_subset plan origin))
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ output)
  | default role outputName term =>
    change name ∈ GeneralDictionaryDefaultModeEffects213.bodySources plan target _ at member
    unfold GeneralDictionaryDefaultModeEffects213.bodySources GeneralDictionaryDefaultModeSupport213.schemaSources bodySchema at member
    cases compiled : compileBody plan (.default role outputName term) with
    | none => simp [compiled] at member
    | some expression =>
      simp only [compiled,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.mem_cons] at member
      rcases member with equal | read
      · exact List.mem_cons.mpr (Or.inl equal)
      · rw [GeneralDictionaryDefaultModeSupport213.actual_reads] at read
        obtain ⟨index,_,equal⟩ := List.mem_map.mp read
        change (List.ofFn plan.input.center)[index]?.getD 0 = name at equal
        apply List.mem_cons_of_mem
        apply List.mem_append_left
        cases found : (List.ofFn plan.input.center)[index]? with
        | none =>
          simp only [found,Option.getD_none] at equal
          rw [← equal]
          exact List.mem_append_right _ (List.mem_singleton_self _)
        | some identity =>
          simp only [found,Option.getD_some] at equal
          rw [← equal]
          exact List.mem_append_left _ (List.mem_of_getElem? found)

theorem fresh_ne_zero :
    fresh seed invocation declaration purpose owner position ≠ 0 := by
  have above := GeneralNominalIdentities.source_above_seed seed
    (invocation,declaration,purpose,owner,position)
  change seed < fresh seed invocation declaration purpose owner position at above
  omega

/-- Output binders use purpose2, even when an input name also appears in an
arbitrary unverified plan. This uses the actual binder conditional. -/
theorem output_separate (plan : Plan roles) (different : purpose ≠ 2)
    (declared : name ∈ plan.packet.declaration.outputNames) :
    fresh plan.packet.context.state.seed invocation declaration purpose owner position ≠ plan.binder name := by
  have equal : plan.binder name = fresh plan.packet.context.state.seed plan.packet.site.occurrence.identity
      plan.packet.declaration.id 2 name 0 := by
    simp only [Plan.binder,declared,ite_true]
    rfl
  rw [equal]
  exact GeneralNominalCenteredAllocation.fresh_namespaces different

theorem external_provenance (plan : Plan roles) (different : purpose ≠ 2)
    (member : fresh plan.packet.context.state.seed invocation declaration purpose owner position ∈ externalSources plan) :
    fresh plan.packet.context.state.seed invocation declaration purpose owner position ∈ List.ofFn plan.input.center := by
  rcases List.mem_append.mp member with origin | output
  · rcases List.mem_append.mp origin with center | zero
    · exact center
    · exact False.elim (fresh_ne_zero (List.mem_singleton.mp zero))
  · obtain ⟨name,declared,equal⟩ := List.mem_map.mp output
    exact False.elim (output_separate plan different declared equal.symm)

theorem body_provenance (plan : Plan roles) (target : Nat) (body : Body) (different : purpose ≠ 2)
    (member : fresh plan.packet.context.state.seed invocation declaration purpose owner position ∈ bodySources plan target body) :
    fresh plan.packet.context.state.seed invocation declaration purpose owner position = target ∨
      fresh plan.packet.context.state.seed invocation declaration purpose owner position ∈ List.ofFn plan.input.center := by
  rcases List.mem_cons.mp (body_subset plan target body member) with equal | external
  · exact Or.inl equal
  · exact Or.inr (external_provenance plan different external)

open GeneralNominalCenteredHeadOutputs (requests)

theorem class_provenance (state : GeneralNominalCenteredSteps.State roles) (focus : Occurrence roles)
    (plan : Plan roles) (different : purpose ≠ 2)
    (member : fresh plan.packet.context.state.seed invocation declaration purpose owner position ∈
      GeneralDictionaryOriginClass227.classSources state focus plan) :
    (∃ output ∈ requests state focus,
      fresh plan.packet.context.state.seed invocation declaration purpose owner position = output.target) ∨
      fresh plan.packet.context.state.seed invocation declaration purpose owner position ∈ List.ofFn plan.input.center := by
  obtain ⟨output,requested,within⟩ := List.mem_flatMap.mp member
  rcases List.mem_cons.mp within with target | body
  · exact Or.inl ⟨output,requested,target⟩
  · obtain ⟨body,_,present⟩ := List.mem_flatMap.mp body
    rcases body_provenance plan output.target body different present with target | center
    · exact Or.inl ⟨output,requested,target⟩
    · exact Or.inr center

theorem delta_provenance (before after : GeneralNominalCenteredSteps.State roles) (focus : Occurrence roles)
    (plan : Plan roles) (different : purpose ≠ 2)
    (member : fresh plan.packet.context.state.seed invocation declaration purpose owner position ∈
      GeneralDictionaryOriginClass227.deltaSources before after focus plan) :
    (∃ output ∈ requests after focus,
      fresh plan.packet.context.state.seed invocation declaration purpose owner position = output.target) ∨
      fresh plan.packet.context.state.seed invocation declaration purpose owner position ∈ List.ofFn plan.input.center :=
  class_provenance after focus plan different (GeneralDictionaryOriginClass227.delta_subset member)

/-- Specialized public interface for the two allocated merge namespaces. -/
theorem merge_body_provenance (plan : Plan roles) (target : Nat) (body : Body)
    (mergePurpose : purpose = 0 ∨ purpose = 1)
    (member : fresh plan.packet.context.state.seed invocation declaration purpose owner position ∈ bodySources plan target body) :
    fresh plan.packet.context.state.seed invocation declaration purpose owner position = target ∨
      fresh plan.packet.context.state.seed invocation declaration purpose owner position ∈ List.ofFn plan.input.center :=
  body_provenance plan target body (by omega) member

end Yulang.GeneralDictionaryBodyProvenance227
