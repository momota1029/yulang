import Yulang.GeneralRebaseUniversalRegression263
open Yulang GeneralRebaseUniversalRegression263
open GeneralRebaseTwoOwnerRegression263 (owners first)
open GeneralRebaseSelectedRegression262 (unused)
example : GeneralRebaseUniversalObserver263.run owners pool inspect select start = .ok finish := run_success
example : GeneralRebaseBudget258.Runs observe 2 start finish := exactly_two_writes
example : GeneralRebaseScheduler259.next observe finish = .ok none := terminal
example : GeneralRebaseUniversalBasis263.bodyKey first.owner unused ∈ finish.remaining := reserved_retained
example : finish ≠ GeneralRebaseStep258.done (GeneralRebaseUniversalBasis263.basis owners pool) := terminal_not_done
example : (GeneralRebaseBodyTable261.schema GeneralRebaseTwoOwnerRegression263.firstPlan unused).unknown = true := unused_unknown
example :
 (∀ state ∈ [start,middle], GeneralRebaseUniversalObserver263.validate owners pool inspect select state = .ok ()) ∧
 GeneralRebaseUniversalObserver263.validate owners pool inspect select finish = .ok () :=
 GeneralRebaseValidatedDriver263.states_valid _ _ checked_trace
#print axioms run_success
#print axioms exactly_two_writes
#print axioms checked_trace
#print axioms reserved_retained
#print axioms terminal_not_done
#print axioms unused_unknown
