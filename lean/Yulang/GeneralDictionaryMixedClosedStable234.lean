import Yulang.GeneralDictionaryMixedClosedEvidence234
import Yulang.GeneralNominalVersionedMixedRefreshEquality234
import Yulang.GeneralDictionaryVersionedSecondEquality233
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
namespace Yulang.GeneralDictionaryMixedClosedStable234
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryMixedClosedStep234 (next)
open GeneralDictionaryMixedClosedPlan234 (plan children_empty)
open GeneralDictionaryMixedClosedFrame234 (raw_sites centers frame)
open GeneralDictionaryMixedClosedSnapshot234 (pointDesc)
open GeneralDictionaryVersionedBothModel233 (extended)
open GeneralNominalVersionedMixedKernel234
open GeneralNominalVersionedMixedTerminalStable234
open GeneralNominalVersionedJournal232

 theorem valid : Models next extended :=
  (GeneralDictionaryMixedClosedStep234.models_iff _).mpr GeneralDictionaryVersionedSecondInstall233.installed_model

theorem headless : HeadlessUnknown next := by
  refine ⟨extended,valid,?_⟩
  intro identity member unknown test held
  obtain ⟨index,rfl⟩ := GeneralDictionaryVersionedSecondEquality233.supported
    (GeneralDictionaryMixedClosedRefresh234.certificate.support identity member)
  rw [GeneralDictionaryVersionedSecondEquality233.index_model] at held
  cases index with
  | zero => exact unknown ⟨(0 : Fin 8),rfl,Or.inr ⟨pointDesc,rfl⟩⟩
  | one => exact unknown ⟨(1 : Fin 8),rfl,Or.inr ⟨pointDesc,rfl⟩⟩
  | two => exact unknown ⟨(2 : Fin 8),rfl,Or.inl (by intro h; cases h)⟩
  | oldUpper => exact unknown ⟨(5 : Fin 8),rfl,Or.inl (by intro h; cases h)⟩
  | newLower => exact unknown ⟨(6 : Fin 8),rfl,Or.inl (by intro h; cases h)⟩
  | newUpper => exact unknown ⟨(7 : Fin 8),rfl,Or.inl (by intro h; cases h)⟩
  | three => exact GeneralDictionaryGroundCopy218Refresh.top_no_head test held
  | four | oldLower => exact GeneralDictionaryOptionalOutput229.no_test test held

theorem point_closed : GeneralNominalReobservationSteps.PointClosed next.core.erased.current.context.state := by
  change GeneralNominalReobservationSteps.PointClosed GeneralDictionaryMixedClosedSnapshot234.extendedSnapshot
  intro slot descriptor found
  change (if slot = 0 ∨ slot = 1 then some pointDesc else none) = some descriptor at found
  split at found
  · cases Option.some.inj found
    intro parameter member
    change parameter ∈ [.type (2,2),.type (2,2)] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> rfl
  · cases found

theorem equality_closed : EqualityClosed next :=
  GeneralNominalVersionedMixedRefreshEquality234.old_equality_closed
    GeneralDictionaryMixedClosedRefresh234.certificate GeneralDictionaryVersionedSecondEquality233.equality_closed

theorem edges_empty : next.core.erased.current.edges = [] :=
  GeneralDictionaryVersionedSecondStable233.edges_empty

theorem committed : Committed next plan := by
  constructor
  · intro model holds
    have packet := GeneralDictionaryMixedClosedEvidence234.packet holds
    exact ⟨packet,GeneralDictionaryMixedClosedFrame234.class_effects packet⟩
  · intro child member
    rw [children_empty] at member
    cases member

theorem no_install (effect : Effect roles) (enabled : Installable registry next effect)
    (same : effect.plan.packet.site.occurrence = root) : Committed next effect.plan := by
  have framed := effect.frame
  rw [enabled.registry_eq,enabled.snapshot_eq,same] at framed
  have equal : effect.plan = plan := GeneralNominalVersionedFrameFunctional232.frame_plan_unique rfl raw_sites centers
    framed (frame (GeneralDictionaryMixedClosedEvidence234.packet valid))
  rw [equal]
  exact committed

theorem stable : Stable registry next root :=
  GeneralNominalVersionedMixedTerminalStable234.stable raw_sites centers edges_empty point_closed headless equality_closed no_install

theorem halted : ∀ after, ¬ Step registry root next after := by
  rintro after ⟨focus,generated,action⟩
  exact stable focus generated after action

theorem source_stable : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Stable sourceRegistry next root := stable

end Yulang.GeneralDictionaryMixedClosedStable234
