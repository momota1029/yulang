import Yulang.GeneralNominalHeadCoreOverlap185
import Yulang.GeneralNominalHeadEffectCore185
import Yulang.GeneralNominalHeadEffectReadback185

/-! Every purpose-eight name in the complete actual WF model footprint has a
single historical origin uniformly read back by every model. Candidate-origin
agreement with that witness is a distinct obligation. -/
namespace Yulang.GeneralNominalHeadFullOverlap185
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalHeadLedgerFrame182
open GeneralNominalRecursiveInspection (Origin)
open GeneralNominalOriginTerms (Same)
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

theorem wf_full_overlap_readback
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (member : fresh state.core.erased.current.context.state.seed invocation declaration 8 owner position ∈ fullSources state) :
    ∃ origin : Origin, ∀ model : Assignment, Models state model →
      Same model origin (.source (fresh state.core.erased.current.context.state.seed invocation declaration 8 owner position)) := by
  have core (present : fresh state.core.erased.current.context.state.seed invocation declaration 8 owner position ∈
      GeneralNominalModeLedger181.fullSources state.core) :
      ∃ origin : Origin, ∀ model : Assignment, Models state model →
        Same model origin (.source (fresh state.core.erased.current.context.state.seed invocation declaration 8 owner position)) := by
    obtain ⟨origin,witness⟩ := GeneralNominalHeadCoreOverlap185.wf_overlap_actual reachable present
    exact ⟨origin,fun _ valid => GeneralNominalSupportProvenance182.actual_same valid.1 witness⟩
  rcases List.mem_append.mp member with present | present
  · exact core present
  · obtain ⟨effect,registered,present⟩ := List.mem_flatMap.mp present
    rcases List.mem_append.mp present with held | live
    · rcases List.mem_append.mp held with head | snapshot
      · exact core (GeneralNominalHeadEffectCore185.effect_head_in_core reachable effect registered head)
      · obtain ⟨entry,_,_,_,readback⟩ :=
          GeneralNominalHeadEffectReadback185.wf_snapshot_overlap_readback reachable effect registered (by omega) snapshot
        exact ⟨entry.origin,readback⟩
    · obtain ⟨entry,_,_,_,readback⟩ :=
        GeneralNominalHeadEffectReadback185.wf_live_overlap_readback reachable effect registered (by omega) live
      exact ⟨entry.origin,readback⟩

def BinderNames (state : State roles) (names : Fin count → Nat) : Prop :=
  ∀ index, ∃ invocation declaration owner position,
    names index = fresh state.core.erased.current.context.state.seed invocation declaration 8 owner position

theorem wf_historical_witnesses
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (names : Fin count → Nat) (allocated : BinderNames state names) :
    ∃ historical : Fin count → Origin, ∀ index, names index ∈ fullSources state →
      ∀ model : Assignment, Models state model → Same model (historical index) (.source (names index)) := by
  classical
  have witnessed index : ∃ origin, names index ∈ fullSources state →
      ∀ model : Assignment, Models state model → Same model origin (.source (names index)) := by
    by_cases member : names index ∈ fullSources state
    · obtain ⟨invocation,declaration,owner,position,equal⟩ := allocated index
      obtain ⟨origin,readback⟩ := wf_full_overlap_readback reachable (equal ▸ member)
      exact ⟨origin,fun _ model valid => equal.symm ▸ readback model valid⟩
    · exact ⟨.source (names index),fun impossible => False.elim (member impossible)⟩
  exact ⟨fun index => Classical.choose (witnessed index),fun index => Classical.choose_spec (witnessed index)⟩

end Yulang.GeneralNominalHeadFullOverlap185
