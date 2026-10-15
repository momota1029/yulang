# Private native receiving residual experiment

Date: 2026-10-15
Status: bounded native experiment implemented and independently reviewed;
generalized residual transport and production adoption OPEN
Branch: `research/simple-sub-intrusion`
Source baseline: `cdfdb58bb244fecf0c895a6a1d65b2bdee06548c`

## Exact gate and implementation

The [independently reviewed finite source theorem](../theory/2026-10-15-native-receiving-residual-prototype.md)
supplies A0–A7 for one complete original receiving-call assembly. This gate
implements its private native consumer in `yu-solver::candidate_receiver` under
`shadow-apply-candidate`. `solve_receiving_residual_experiment` returns an opaque
private native graph observation; it never exports a generic relay scheme.

Validation checks the complete two-definition inventory, actual resolved module
call, direct operation provider, retained Computation formal, original parameter
Name, total first operation arm with discarded continuation and pure value arm.
This proves one invocation, not merely one incoming reference. Unsupported
assemblies leave this experiment unavailable without changing ordinary solve.

The original module use is connected through its ordinary occurrence/cause.
The experiment executes original schedules once, without modifying SCC or
intrusion membership and without capture/FreshUse publication. It holds the
original Catch scrutinee slot-51 inclusion before propagation, then reads actual
native lower contributions. Only a member of the exact source-owned operation
view covered by A0–A7 is suppressed. Other terminals forward through the native
effect constraint consumer; unresolved tails/rows leave the attempt unavailable.
The original scrutinee, raw continuation routes and independent arm edges remain.

`result_families` reads the actual canonical Catch-result graph, following lower
rows and Support/AnnotationMember/Contribution operands. It does not derive an
answer from the selected source or outcome labels. Equal operation spellings
with distinct resolved families remain distinct.

## Review, repair and verification

M2, two reviewers. `callback_feasibility_review` checked source qualification,
unique invocation, pre-admission timing, original provenance and private graph
ownership with no blocking/major findings. `residual_contract_review` approved
test expectations before writing and found the initial operand-count accessor
insufficient to establish actual family-specific output. One batched repair
added `result_families` and fixed grouped-scrutinee slot-51 ownership. Both delta
reviews passed without findings at source hash
`a93070f0f3273bb637bccba980834a3da4d7eb12fe47a691d3610262dacf067f`.
Formatting only then produced integrated hash
`07359413a922b407a32a9d408d870a28f53eedf24f54986753ff7a6030c79611`.

Primary verification used two build jobs, a 300-second timeout and one test
thread for the four native experiment tests:

- Isolated `cargo check -p yu-solver --features shadow-apply-candidate`: passed,
  no warnings.
- Isolated `cargo test -p yu-solver --features shadow-apply-candidate candidate_receiver::tests -- --test-threads=1`:
  4 passed; other test targets filtered out.
- Integrated `cargo test -p yu-solver --features shadow-apply-candidate --lib candidate_receiver::tests -- --test-threads=1`:
  4 passed after formatting and integration.

The cases observe actual signal absence, actual write presence, grouped source
ownership and five unavailable private envelopes while retaining ordinary
candidate admission. They do not prove generalized hygiene from examples.
The sibling command
`cargo test -p yu-solver --features shadow-apply-candidate --test candidate_computation_laziness --test candidate_operation_catch --test candidate_catch_value_source -- --test-threads=2`
passes all 24 cases (6 + 12 + 6). No benchmark or timing experiment ran (zero samples).
No workspace-wide solver suite ran.

The experiment scans its bounded source inventory and deduplicates native lower
dependencies under the existing private work limit. Ordinary solver dispatch
gains no traversal/storage cost. Implementation was isolated in
`/tmp/yulang-receiving-residual-prototype`; only the three exact code paths were
integrated into the working branch.

## Remaining original scope

The runtime receiver machine, generalized/captured residual dependency,
multiple callers, mixed providers, resumptions and latent typed transport remain
open. This private monomorphic route establishes no equivalence with ordinary
generalized inference. Callback B, complete Call, soundness/principality and
production cutover retain their original owners and scope.
