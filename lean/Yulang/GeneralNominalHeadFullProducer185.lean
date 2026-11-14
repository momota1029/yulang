import Yulang.GeneralNominalHeadFullOverlap185

/-! Every purpose-eight support overlap, including live and snapshot output
schemas, identifies an actually registered core plan and binder. -/
namespace Yulang.GeneralNominalHeadFullProducer185
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalHeadLedgerFrame182
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

theorem wf_full_producer
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (member : fresh state.core.erased.current.context.state.seed invocation declaration 8 owner position ∈ fullSources state) :
    ∃ plan ∈ state.core.plans, ∃ name,
      plan.binder name = fresh state.core.erased.current.context.state.seed invocation declaration 8 owner position := by
  have core (present : fresh state.core.erased.current.context.state.seed invocation declaration 8 owner position ∈
      GeneralNominalModeLedger181.fullSources state.core) :
      ∃ plan ∈ state.core.plans, ∃ name,
        plan.binder name = fresh state.core.erased.current.context.state.seed invocation declaration 8 owner position := by
    obtain ⟨_,plan,registered,_,_,entry,_,_,equal,_⟩ := GeneralNominalHeadCoreOverlap185.wf_overlap_actual reachable present
    exact ⟨plan,registered,entry.name,equal⟩
  rcases List.mem_append.mp member with present | present
  · exact core present
  · obtain ⟨effect,registered,present⟩ := List.mem_flatMap.mp present
    rcases List.mem_append.mp present with held | live
    · rcases List.mem_append.mp held with head | snapshot
      · exact core (GeneralNominalHeadEffectCore185.effect_head_in_core reachable effect registered head)
      · obtain ⟨entry,_,_,equal⟩ :=
          (GeneralNominalHeadEffectReadback185.wf_snapshot_overlap_iff reachable effect registered (by omega)).mp snapshot
        exact ⟨effect.plan,GeneralNominalHeadEffectCore185.effect_plan_registered reachable effect registered,entry.name,equal.symm⟩
    · obtain ⟨entry,_,_,equal⟩ :=
        (GeneralNominalHeadEffectReadback185.wf_live_overlap_iff reachable effect registered (by omega)).mp live
      exact ⟨effect.plan,GeneralNominalHeadEffectCore185.effect_plan_registered reachable effect registered,entry.name,equal.symm⟩

end Yulang.GeneralNominalHeadFullProducer185
