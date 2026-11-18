import Yulang.GeneralRebaseTwoOwnerRegression263
open Yulang
open GeneralRebaseTwoOwnerRegression263

example : first.owner ≠ last.owner := owners_distinct
example : GeneralRebaseMultiRun263.run owners representative pool inspect select start = .ok finish := run_success
example : GeneralRebaseBudget258.Runs observe 2 start finish := exactly_two_writes
example : GeneralRebaseScheduler259.next observe finish = .ok none := terminal
example (base : GeneralNominalCommonBridge.Assignment → Prop) (assignment) :
 GeneralRebaseOwnerTable263.Models base owners representative finish assignment ↔
 base assignment ∧
 GeneralNominalVersionedEffects231.ClassEffects (GeneralNominalCenteredHeadAllocMergeState.stage []).core first.root first.plan assignment ∧
 GeneralNominalVersionedEffects231.ClassEffects (GeneralNominalCenteredHeadAllocMergeState.stage []).core last.root last.plan assignment :=
 models_exact base assignment

#print axioms owners_distinct
#print axioms first_requests
#print axioms last_requests
#print axioms checked_trace
#print axioms run_success
#print axioms exactly_two_writes
#print axioms event_trace
#print axioms models_exact
