# Independent review: selection validator and generic finite driver

Reviewed coordinator commit ec09234d9: GeneralRebaseMultiSelection263,
GeneralRebaseValidatedDriver263, GeneralRebaseValidatedOutcome263. No source changes.
All three independently strict rebuilt into a separate cache; prior dependencies
were reused. Source SHA256 and results: driver-independent-build.txt.
Reproduction: rebuild-driver-review.py. Probe exit0; seven axiom audits show only
standard propext, Classical.choice and Quot.sound. No whole-repository build.

No correctness or quantifier-scope defect found.

Selection.ofPlan encodes both root identity and declaration identity and stores that
Plan's actual root. An arbitrary Selection is a broader input type and does not itself
certify this linkage. `registered` in this module maps *centered* source.plans, not the
versioned journal state.plans. The coordinator's source wrapper must use the latter
explicitly, as agreed; the two lists must not be conflated.

MultiSelection.check processes the complete currently selected list before allowing
scheduler execution. check_exact is an iff with readiness of all selected entries,
not just the first progressing one. error_selected recovers the actual selected entry
and its exact ClassCheck diagnostic. No check of unselected candidate-pool entries is
introduced. Root/Plan/owner validity, Frame, Generated or source reachability are not
proved merely by constructing a Selection or passing this body-translation check.

ValidatedDriver is generic over an arbitrary supplied validator. Its own theorem
means validate returned ok at every actual pre-write state and at the terminal state.
It implies all-selected Ready only when validate is instantiated with MultiSelection.check
and its check_exact theorem. The generic driver does not secretly assert that arbitrary
validators check semantic obligations.

Trace.next retains the actual scheduler.next equation and exact before/middle state;
its tail begins at that middle state. The state list contains pre-write states, while
terminal validation is stored separately in Trace.done. successful_trace/trace_success
are both proved. to_runs, ordinary_settle, certificate correctly derive underlying
finite writes, budget and quiescence. Each recursion uses actual next_step and strictly
decreasing remaining.length; it does not assume progress of old source execution.

Outcome.error_path traces a failed run to a finite-rebase reachable diagnostic state.
At.outside includes successful validation at that state plus the exact scheduler error;
At.validation includes the validator's exact error. no_outside correctly requires the
explicit Closed observer premise and leaves validation failure possible. outcome is
success OR an internal validation diagnostic, with effective-write count bounded by
initial remaining length. It neither assumes universal validation success nor claims
source acceptance, satisfiability, old-Step simulation or runtime complexity.

The independent concrete probe uses one fact, a validator that succeeds before the
write and fails at the empty terminal state, and a closed observer. The checked run
really returns validation error7 after the one write. This verifies that terminal
validation is not skipped and that closure does not incorrectly guarantee success.
The test concerns pure finite execution only, not external side effects.
