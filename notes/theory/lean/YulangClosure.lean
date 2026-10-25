import YulangClosure.Contracts
import YulangClosure.CoreComposition
import YulangClosure.ControlComposition
import YulangClosure.CoreExecution
import YulangClosure.CoreControlBridge
import YulangClosure.PaperTypeSubstitution

#print axioms YulangClosure.finite_prefix_composition
#print axioms YulangClosure.run_at_every_time
#print axioms YulangClosure.saved_reusable
#print axioms YulangClosure.SourceProblem.native_success_elaborates

#print axioms YulangClosure.Control.control_preservation
#print axioms YulangClosure.Control.progress
#print axioms YulangClosure.Control.resume_reusable
#print axioms YulangClosure.Control.prefix_fail_absorbing
#print axioms YulangClosure.Control.finite_trace_safety
#print axioms YulangClosure.Control.finite_prefix_control

#print axioms YulangClosure.Original.substituteRaw_composition
#print axioms YulangClosure.Original.substComp_typed
#print axioms YulangClosure.Original.single_raw
#print axioms YulangClosure.Original.raw_step_lifts
#print axioms YulangClosure.Original.raw_finite_safety

#print axioms YulangClosure.Original.principal_preservation
#print axioms YulangClosure.Original.closed_bottom

#print axioms YulangClosure.CoreControlBridge.successor_coverage
#print axioms YulangClosure.CoreControlBridge.machine_finite_coverage
#print axioms YulangClosure.CoreControlBridge.finite_closed_safety

#print axioms YulangClosure.PaperTypes.subst_id
#print axioms YulangClosure.PaperTypes.subst_comp
#print axioms YulangClosure.PaperTypes.OperationInstance.subst_comp
