import Yulang.GeneralPresenceObservedPlan245
namespace Yulang.GeneralPresenceCommonObserved245
open Core.PresenceGeneration
open GeneralPresenceModelCongruence245 GeneralPresenceQueryTransport245
open GeneralPresenceOwnerTable244 GeneralPresenceRebasePlan245 GeneralPresenceObservedPlan245

structure Specification where
 depth : Nat
 rank : Nat
 environment : CommonNominalFullDemand.Environment Common.Row
 observation : CommonNominalFullDemand.Observation Common.Row
 rowCondition : Common.Row → Prop

def inspect (spec : Specification) (value : Comp CommonNominalFullCarrier.model) : Prop :=
 Probe value.1 spec.depth spec.rank spec.environment spec.observation ∧ spec.rowCondition value.2

theorem inspect_stable (specs : Tag → Specification) :
 Stable CommonNominalFullCarrier.model (fun tag => inspect (specs tag)) := by
 intro tag first last same
 have typed : Probe first.1 (specs tag).depth (specs tag).rank (specs tag).environment (specs tag).observation ↔
   Probe last.1 (specs tag).depth (specs tag).rank (specs tag).environment (specs tag).observation :=
   (CommonNominalFullDemand.producerEq_iff_probe _ _).mp
     ⟨same.1.1 (specs tag).depth,same.1.2 (specs tag).depth⟩ _ _ _
 exact and_congr typed (by rw [same.2])

variable {Name Owner Tag : Type} [DecidableEq Name] [DecidableEq Owner]

/-- Arbitrary finite tagged demand queries, including exact row predicates,
can be retained while private table definitions are changed. The caller must
actually transport every covered query and certify every intermediate rebase. -/
theorem common_observed_plan (specs : Tag → Specification) (sharedNames : Name → Prop)
 (boundary : Name → Comp CommonNominalFullCarrier.model) (state : State Name Owner)
 (plan : List (Edit Name Owner)) (safe : SafePlan sharedNames state plan)
 (bundle : List (Tag × CompTerm Name)) :
 Outcome CommonNominalFullCarrier.model (fun tag => inspect (specs tag)) sharedNames boundary state bundle ↔
 Outcome CommonNominalFullCarrier.model (fun tag => inspect (specs tag)) sharedNames boundary
   (runObserved state bundle plan).1 (runObserved state bundle plan).2 :=
 plan_observed _ GeneralPresenceCommonLaws245.common_laws _ (inspect_stable specs) sharedNames boundary state plan safe bundle
end Yulang.GeneralPresenceCommonObserved245
