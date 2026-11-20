import Yulang.GeneralMixedIndexedDiagnosticLocal305
import Yulang.GeneralNominalVersionedObservationTransport233

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralMixedReindexObserver305
open GeneralDeclarations GeneralSourceDictionaries CommonRoleOutermostResolver
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedObservationTransport233 (refresh_forward_raw refresh_backward_raw)
open GeneralNominalReportContext305 (EquivalentContexts model_iff)
open GeneralMixedIndexedFrame305 (IndexedView)
open GeneralMixedDiagnosticSlice304 (Semantics)
open GeneralNominalVersionedMergedConflict232 (HistoryModels ClassEquations)
open GeneralMixedDiagnosticHead304 (boundary8)
open GeneralDeferredLadderOperationalView304 (View requests_iff alias_forward classes_iff)
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {s : State roles} {target : GeneralNominalRecursiveCandidates.Context}

theorem models_iff (same : EquivalentContexts s.core.erased.current.context target) (m : Assignment) :
    Models s m ↔ Models (refresh s target) m :=
  ⟨fun old => refresh_forward_raw old ((model_iff same m).mp old.1.1),
   fun new => refresh_backward_raw new ((model_iff same m).mpr new.1.1)⟩

def indexed (same : EquivalentContexts s.core.erased.current.context target) :
    IndexedView s (refresh s target) :=
  ⟨⟨rfl,rfl,rfl,models_iff same⟩,rfl,same⟩

theorem history_iff (s : State roles) (target : GeneralNominalRecursiveCandidates.Context) (m : Assignment) :
    HistoryModels s m ↔ HistoryModels (refresh s target) m := Iff.rfl

theorem class_forward (s t : State roles) (raw : View s t)
    (legacy : s.legacy.effects = t.legacy.effects) (versioned : s.effects = t.effects)
    (root : Occurrence roles) (m : Assignment) (found : ClassEquations s root m) :
    ClassEquations t root m := by
  constructor
  · constructor
    · intro a ma b mb eq
      exact found.1.1 a ((requests_iff raw root a).mpr ma) b ((requests_iff raw root b).mpr mb) eq
    · intro e listed alias
      exact (GeneralNominalVersionedEffects231.class_effects_iff ..).mp
        ((classes_iff raw e.plan e.plan.packet.site.occurrence m).mp
          ((GeneralNominalVersionedEffects231.class_effects_iff ..).mpr
            (found.1.2 e (legacy.symm ▸ listed) (alias_forward raw.symm alias))))
  · intro e listed alias
    exact (classes_iff raw e.plan e.plan.packet.site.occurrence m).mp
      (found.2 e (versioned.symm ▸ listed) (alias_forward raw.symm alias))

theorem semantics (same : EquivalentContexts s.core.erased.current.context target) :
    Semantics s (refresh s target) := by
  let raw := (indexed same).raw
  exact ⟨history_iff s target,fun o m _ =>
    ⟨class_forward s _ raw rfl rfl o m,class_forward _ s raw.symm rfl rfl o m⟩⟩

theorem local_iff (same : EquivalentContexts s.core.erased.current.context target)
    (r : Registry) (root : Occurrence roles) (front : Frontier (Occurrence roles)) :
    B4TargetV8.Local (boundary8 roles) r s root front ↔
      B4TargetV8.Local (boundary8 roles) r (refresh s target) root front :=
  GeneralMixedIndexedDiagnosticLocal305.local_iff (indexed same) (semantics same) r root front

theorem recursive_iff (same : EquivalentContexts s.core.erased.current.context target)
    (r : Registry) (root : Occurrence roles) (tree : Tree) :
    Resolves (B4TargetV8.Local (boundary8 roles) r s) root tree ↔
      Resolves (B4TargetV8.Local (boundary8 roles) r (refresh s target)) root tree :=
  GeneralMixedIndexedDiagnosticLocal305.recursive_iff (indexed same) (semantics same) r root tree

/-- This observer retargeting is not a strict raw refresh event. -/
theorem no_strict_observation (same : EquivalentContexts s.core.erased.current.context target) (source : Nat) :
    ¬ (¬ GeneralNominalState.Known s.core.erased.current.context.state source ∧
      GeneralNominalState.Known target.state source) :=
  fun ⟨unknown,known⟩ => unknown (same.backward.known source known)

end Yulang.GeneralMixedReindexObserver305
