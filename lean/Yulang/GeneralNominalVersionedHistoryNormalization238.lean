import Yulang.GeneralNominalAcyclicNormalization238
import Yulang.GeneralNominalRawCongruence238
import Yulang.GeneralNominalVersionedHistoryEquations237
set_option backward.isDefEq.respectTransparency false
/-! Existing historical models make aggregate normalization semantics-preserving.
This is not a proof that a prospective new packet preserves those models. -/
namespace Yulang.GeneralNominalVersionedHistoryNormalization238
open GeneralNominalVersionedJournal232
open GeneralNominalVersionedMixedSeedLedger237 (entries Recorded)
open GeneralNominalVersionedHistoryEquations237 (solution)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalAssignmentCongruence238 (Same)
variable {roles : Roles.RoleDecls} {state : State roles} {base : Assignment}

theorem historical_equations (valid : Models state base) :
 ∀ entry ∈ entries state, PresenceNormalForm.All CommonNominalFullCarrier.model base
 (GeneralNominalAllocation.equations entry.1 entry.2) := by
 intro entry member
 obtain ⟨plan,present,member⟩ := List.mem_flatMap.mp member
 exact (GeneralNominalVersionedAggregateEntries236.holds_iff plan.packet.context.state plan.packet.registry
   plan.packet.site.occurrence.identity plan.packet.declaration plan.packet.bindings base).mp
   (GeneralNominalVersionedAggregateReuse236.recorded_merges valid present) entry member

theorem equivalent (recorded : Recorded state) (valid : Models state base) :
 Same (solution state base) base :=
 GeneralNominalAcyclicNormalization238.preserves _ base
   (GeneralNominalVersionedHistoryEquations237.coherent recorded)
   (GeneralNominalVersionedHistoryEquations237.descending state) (historical_equations valid)

theorem source_equivalent
 (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
 (valid : Models state base) : Same (solution state base) base :=
 equivalent (GeneralNominalVersionedMixedSeedLedger237.reachable path) valid

theorem raw_models (recorded : Recorded state) (valid : Models state base) :
 GeneralNominalState.Models state.core.erased.current.context.state (solution state base) :=
 (GeneralNominalRawCongruence238.models_iff _ (equivalent recorded valid)).mpr valid.1.1

theorem ordinary_iff (recorded : Recorded state) (valid : Models state base)
 (atoms : List (PresenceNormalForm.Atom Nat)) :
 PresenceNormalForm.All CommonNominalFullCarrier.model (solution state base) atoms ↔
 PresenceNormalForm.All CommonNominalFullCarrier.model base atoms :=
 GeneralNominalAssignmentCongruence238.all_iff (equivalent recorded valid) atoms

theorem source_raw_models
 (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
 (valid : Models state base) : GeneralNominalState.Models state.core.erased.current.context.state (solution state base) :=
 raw_models (GeneralNominalVersionedMixedSeedLedger237.reachable path) valid
end Yulang.GeneralNominalVersionedHistoryNormalization238
