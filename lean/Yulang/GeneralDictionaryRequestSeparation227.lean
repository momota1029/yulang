import Yulang.GeneralDictionaryBodyProvenance227
import Yulang.GeneralDictionaryDefault214ActualSites

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryRequestSeparation227
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralDictionaryDefaultDepth208
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

theorem child_target_separate (plan : Plan roles) (clause : Clause)
    (signature : clause.Signature roles) (two : purpose ≠ 2) (five : purpose ≠ 5)
    (member : output ∈ (plan.childSite clause signature).occurrence.demand.outputs) :
    fresh plan.packet.context.state.seed invocation declaration purpose owner position ≠ output.target := by
  obtain ⟨equation,_,rfl⟩ := (GeneralDeclarationDemands.child_outputs_exact _ _ signature _ _ output).mp member
  dsimp only
  unfold GeneralDeclarationDemands.outputTarget
  split
  · split
    · exact GeneralNominalCenteredAllocation.fresh_namespaces two
    · exact GeneralNominalCenteredAllocation.fresh_namespaces five
  · exact GeneralNominalCenteredAllocation.fresh_namespaces five

/-- Actual reachable raw-site output targets avoid namespaces other than 2/5.
No finite-depth premise is used. -/
theorem raw_target_separate
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (two : purpose ≠ 2) (five : purpose ≠ 5) :
    ∀ site ∈ state.core.erased.current.sites, ∀ output ∈ site.occurrence.demand.outputs,
      fresh context.state.seed invocation declaration purpose owner position ≠ output.target := by
  induction path with
  | refl =>
      intro site member output within
      cases List.mem_singleton.mp member
      intro collision
      have below := source.below_seed _ (source.linked.2 output within)
      have above := GeneralNominalIdentities.source_above_seed context.state.seed
        (invocation,declaration,purpose,owner,position)
      change context.state.seed < fresh context.state.seed invocation declaration purpose owner position at above
      omega
  | @tail before after path step ih =>
      obtain ⟨focus,generated,action⟩ := step
      cases action with
      | administrative action =>
          cases action with
          | enqueue linked absent =>
              obtain ⟨site,member,same⟩ := GeneralDictionaryDefaultTrace208.generated_registered
                (GeneralDictionaryDefaultTrace208.registered_trace path) generated
              exact False.elim (absent site member same)
          | refresh | reobserve | equate => exact ih
      | refresh | merge => exact ih
      | install effect enabled novel =>
          intro site member output within
          rcases List.mem_append.mp member with old | added
          · exact ih site old output within
          · obtain ⟨center,emitted,rfl⟩ := List.mem_map.mp added
            obtain ⟨clause,_,rfl⟩ := List.mem_map.mp emitted
            have seed : effect.plan.packet.context.state.seed = context.state.seed :=
              (congrArg (fun c : GeneralNominalCandidates.Context => c.state.seed)
                (frame enabled).context_eq).trans (configuration_trace path).1
            simpa only [seed] using child_target_separate effect.plan clause.val
              (effect.plan.packet.checked.signature.2.2.2 clause.val clause.property) two five within

open GeneralNominalCenteredHeadOutputs (requests)

theorem request_separate
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (two : purpose ≠ 2) (five : purpose ≠ 5)
    (member : output ∈ requests state.core focus) :
    fresh context.state.seed invocation declaration purpose owner position ≠ output.target := by
  obtain ⟨site,present,_,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
  exact raw_target_separate source path two five site present output within

/-- Under a registered historical plan, the fresh merge namespace can enter
class support only through positional input centers, never a requested target. -/
theorem class_reads_center
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (plan : Plan roles) (registered : plan ∈ state.core.plans)
    (two : purpose ≠ 2) (five : purpose ≠ 5)
    (member : fresh context.state.seed invocation declaration purpose owner position ∈
      GeneralDictionaryOriginClass227.classSources state.core focus plan) :
    fresh context.state.seed invocation declaration purpose owner position ∈ List.ofFn plan.input.center := by
  have seed := GeneralDictionaryDefault214ActualSites.plan_seed path plan registered
  rw [← seed] at member ⊢
  rcases GeneralDictionaryBodyProvenance227.class_provenance state.core focus plan two member with target | center
  · obtain ⟨output,requested,equal⟩ := target
    rw [seed] at equal
    exact False.elim (request_separate source path two five requested equal)
  · exact center

theorem delta_reads_center
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (plan : Plan roles) (registered : plan ∈ state.core.plans)
    (two : purpose ≠ 2) (five : purpose ≠ 5)
    (member : fresh context.state.seed invocation declaration purpose owner position ∈
      GeneralDictionaryOriginClass227.deltaSources before state.core focus plan) :
    fresh context.state.seed invocation declaration purpose owner position ∈ List.ofFn plan.input.center :=
  class_reads_center source path plan registered two five
    (GeneralDictionaryOriginClass227.delta_subset member)

theorem body_reads_center
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (plan : Plan roles) (registered : plan ∈ state.core.plans)
    (two : purpose ≠ 2) (five : purpose ≠ 5)
    (requested : output ∈ requests state.core focus)
    (member : fresh context.state.seed invocation declaration purpose owner position ∈
      GeneralDictionaryHistoricalBody227.bodySources plan output.target body) :
    fresh context.state.seed invocation declaration purpose owner position ∈ List.ofFn plan.input.center := by
  have seed := GeneralDictionaryDefault214ActualSites.plan_seed path plan registered
  rw [← seed] at member ⊢
  rcases GeneralDictionaryBodyProvenance227.body_provenance plan output.target body two member with target | center
  · rw [seed] at target
    exact False.elim (request_separate source path two five requested target)
  · exact center

/-- The actual allocated lower and upper merge names satisfy the general
namespace exclusions. This is provenance, not historical center disjointness. -/
theorem merge_delta_reads_center
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (plan : Plan roles) (registered : plan ∈ state.core.plans)
    (mergePurpose : purpose = 0 ∨ purpose = 1)
    (member : fresh context.state.seed invocation declaration purpose owner position ∈
      GeneralDictionaryOriginClass227.deltaSources before state.core focus plan) :
    fresh context.state.seed invocation declaration purpose owner position ∈ List.ofFn plan.input.center :=
  delta_reads_center source path plan registered (by omega) (by omega) member

end Yulang.GeneralDictionaryRequestSeparation227
