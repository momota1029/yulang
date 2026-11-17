import Yulang.GeneralNominalVersionedMixedPlanLedger235
import Yulang.GeneralNominalVersionedReplayEffects232
/-! Real historical replay exclusion on actual source traces. Ordinary context
extensions, reservation growth and allocation growth alone cannot make a
recorded plan novel again. Global observation/version finiteness is separate. -/
namespace Yulang.GeneralNominalVersionedMixedReplay237
open GeneralNominalCenters GeneralNominalVersionedJournal232
open GeneralNominalVersionedMixedKernel234
open GeneralNominalVersionedTransport231
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {state : State roles}
variable (reserved : List Nat) (atoms : List (PresenceNormalForm.Atom Nat))
  (allocated : List GeneralNominalIdentities.Origin)

theorem extended_committed (plan : Plan roles)
    (old : Committed state plan)
    (current : (extendedPlan reserved atoms allocated plan).packet.context = state.core.erased.current.context) :
    Committed state (extendedPlan reserved atoms allocated plan) := by
  constructor
  · intro model valid
    have previous := old.1 model valid
    have raw := valid.1.1
    rw [← current] at raw
    have added : PresenceNormalForm.All CommonNominalFullCarrier.model model atoms :=
      ((GeneralDictionaryOrdinaryTransport.models_extended ..).mp raw).2
    refine ⟨(holds_iff reserved atoms allocated plan model).mpr ⟨previous.1,added⟩,?_⟩
    exact (GeneralNominalVersionedReplayEffects232.class_effects_iff reserved atoms allocated
      state.core plan.packet.site.occurrence plan model).mpr previous.2
  · intro child member
    change child ∈ GeneralNominalVersionedFrame231.children (extendedPacket reserved atoms allocated plan.packet) at member
    rw [children_eq] at member
    exact old.2 child member

theorem recorded_committed
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
    (member : plan ∈ state.plans)
    (current : (extendedPlan reserved atoms allocated plan).packet.context = state.core.erased.current.context) :
    Committed state (extendedPlan reserved atoms allocated plan) :=
  extended_committed reserved atoms allocated plan
    (GeneralNominalVersionedMixedPlanLedger235.reachable_plan_committed path member) current

theorem no_recorded_reinstall (effect : Effect roles)
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
    (member : plan ∈ state.plans)
    (current : (extendedPlan reserved atoms allocated plan).packet.context = state.core.erased.current.context)
    (same : effect.plan = extendedPlan reserved atoms allocated plan) :
    ¬ (¬ Committed state effect.plan) := by
  rw [same]
  exact fun novel => novel (recorded_committed reserved atoms allocated path member current)

/-- Every genuinely novel current candidate differs from every ordinary replay
of every recorded plan. No model-existence premise is needed for this exclusion. -/
theorem novel_not_replay
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
    (novel : ¬ Committed state candidate)
    (current : candidate.packet.context = state.core.erased.current.context)
    (member : plan ∈ state.plans) : candidate ≠ extendedPlan reserved atoms allocated plan := by
  rintro rfl
  exact novel (recorded_committed reserved atoms allocated path member current)
end Yulang.GeneralNominalVersionedMixedReplay237
