import Yulang.GeneralRebaseRowPhaseSimulation288
import Yulang.GeneralRebaseRowLeafLocality288

#print axioms Yulang.GeneralRebaseRowLedgerPhase288.hasDescriptor_exact
#print axioms Yulang.GeneralRebaseRowLedgerPhase288.phase_cannot_certify_membership
#print axioms Yulang.GeneralRebaseRowPhaseSimulation288.forward
#print axioms Yulang.GeneralRebaseRowPhaseSimulation288.backward
#print axioms Yulang.GeneralRebaseRowPhaseSimulation288.exact_observer
#print axioms Yulang.GeneralRebaseRowPhaseSimulation288.all_models_same
#print axioms Yulang.GeneralRebaseRowPhaseSimulation288.all_output_views_same
#print axioms Yulang.GeneralRebaseRowPhaseSimulation288.enabledness_requires_more_than_models_and_outputs

open Yulang.GeneralRebaseRowLedgerPhase288 in
example : (List.ofFn (fun i : Fin 3 => next ([.rawStop,.ready,.finished][i.val]'i.isLt))) =
    [none,some .finished,none] := rfl
