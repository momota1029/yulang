import Yulang.GeneralRebaseSourceCenters263
#print axioms Yulang.GeneralRebaseRegisteredPlan263.metadata
#print axioms Yulang.GeneralRebaseRegisteredPlan263.source_layout
#print axioms Yulang.GeneralRebaseRegisteredSites263.inputs
#print axioms Yulang.GeneralRebaseRegisteredSites263.origin
#print axioms Yulang.GeneralRebaseRegisteredSites263.emitted_above_root
#print axioms Yulang.GeneralRebaseSourceCenters263.centers_from_heads
#print axioms Yulang.GeneralRebaseSourceCenters263.source_compatible_from_heads
#print axioms Yulang.GeneralRebaseHeadSupport263.from_heads

open Yulang
example (state : GeneralNominalVersionedJournal232.State roles)
 (assignment : GeneralNominalCommonBridge.Assignment) :
 GeneralRebaseSourceCenters263.Heads state assignment ↔
 ∀ plan ∈ state.plans, GeneralNominalVersionedPlans231.SchemaHolds plan plan.headSchema assignment := Iff.rfl
