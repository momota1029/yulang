# Independent review: selected-root validation and quadratic write budget

Reviewer: alias/Plan-transport subagent, not author of the five reviewed modules.
Review and fresh focused build: 2026-11-18 19:02–19:03 UTC.

Files: GeneralRebaseSelectedCheck262, SelectedSettle262, SelectedMeaning262,
SelectedRegression262, and QuadraticBudget262.

## Verification

No correctness defect found in the stated scope. All five modules freshly compiled
in lean/.lake/cycle262-selected-review with --trust=0 -DwarningAsError=true, exit0.
43 explicitly written declarations were axiom-printed in a standalone probe,
exit0. Source hashes remained unchanged through completion. Dependencies were
reused via symlinks; this is not an independent rebuild of the whole dependency
closure or all generated declarations.

Evidence: rebuild-selected-review.py, selected-independent-build.txt,
selected-review-source-sha256.json, SelectedReviewProbe.lean,
selected-independent-audit.txt.

## SelectedCheck262

checkRoots validates the entire supplied roots list against each root's actual
observed Plan and actual snapshot requests. It does not validate every Cartesian
candidate-pool output. It also does not limit validation to the one root whose
proposal the scheduler will choose for the next nontrivial write: all roots in
roots state are checked first, including roots later skipped as no-ops.

check_exact is the exact conjunction of each listed root's body translation
readiness. error_selected points to a root from that same list and reproduces its
underlying ClassCheck failure. actual_ready connects this to the preexisting
actual-snapshot Ready predicate. Missing bodies and unknown translation are
internal failures, not proofs that the source program is rejected.

## SelectedSettle262

run first validates the current roots, then invokes the existing checked finite
scheduler. It either returns selected/outside failure, succeeds at a terminal
state, or recurses only after a nontrivial write that strictly shortens remaining.

Trace retains exactly the pre-write states in order, each round's ReadyRoots,
and the scheduler transition. Its done constructor also includes terminal
ReadyRoots and an actual .ok none scheduler result. Thus final readiness is not
inferred merely from the absence of further novel facts.

successful_trace, states_ready, terminal and certificate derive readiness only
for actually visited rounds and the final state, from a successful run. No global
all-pool or all-state readiness assumption is concealed. Conversely trace_success
reconstructs the run result; ordinary_settle projects successful validated runs
to the underlying scheduler.

The runner is total but may return an internal error. The certificates are
conditional on .ok; they do not claim arbitrary selected lists always pass.

## SelectedMeaning262

from_checked extracts the event witness from the SAME checked intermediate states
and scheduler writes, not from an unrelated run with the same endpoints. Each
recorded event contains its exact snapshot/root/Plan and receives Ready from that
round. certificate combines this witness with simultaneous-assignment semantics
from PlannedTrace262. The state/event histories are chosen outside forall
assignment, and event count equals nontrivial-write count.

source_certificate chooses the finite pool from source formation before any base,
reference Plan, owner, observer or Plan schedule. Its pointwise source-reachability
premise discharges pool coverage. Structural Compatible remains explicit. The
successful-run assumption supplies selected/final Ready, not source reachability,
Frames, packet validity, or Evidence. Consecutive inspected snapshots need not
form one source execution. No source-driver construction or Step simulation follows.

## SelectedRegression262

- unused_missing / old_layout_failure reproduce the old all-pool checker rejecting
  an unused missing-body candidate.
- unused_not_checked shows the new runner ignores that candidate when roots=[].
  This is a valid operational difference but an intentionally empty-selection
  regression. A further nonempty-selected-root example would demonstrate the
  practical benefit more strongly; suggested to the coordinator.
- selected_missing / selected_failure intentionally pair the child's demand with
  the parent's wrong Plan and prove an internal missing-body error. They are not
  source-language rejection or a source-produced wrong-Plan theorem.
- run_good proves a successful selected checked write with Ready.
- success_not_satisfiability pairs that exact success with the already proved empty
  model set for the retained historical constraints. Translation readiness is not
  satisfiability; this distinction is represented faithfully.

## QuadraticBudget262

Each request contributes at most one body equation (including missing/unknown
bodies, which contribute zero). The same-name pair table is a filtered Cartesian
product with at most N² entries. Both lists retain multiplicity; no dedup or Ready
premise is used. facts_bound therefore proves at most N+N² actual list entries.

run_bound combines the finite-state canonical sublist relation with strict write
progress. It holds from any valid finite state and for any supplied observer,
not just an initial state or selected checker. It bounds NONTRIVIAL rebase writes.
It does not bound alias-search time, readiness checks, no-op proposal scans,
ordinary source Step count, memory, or whole compiler asymptotic complexity.

No reviewed theorem claims those larger conclusions. No code changes were made.

## Addendum: failure provenance and nonempty unused-candidate regression

Reviewed GeneralRebaseSelectedFailure262 and GeneralRebaseSelectedUnused262 at
2026-11-18 19:05–19:06 UTC. Both freshly compiled in a separate
cycle262-selected-followup cache, strict kernel checks exit0. A standalone probe
axiom-printed all13 explicitly written declarations, exit0, only standard axioms.
Source hashes remained unchanged. Evidence: rebuild-selected-followup.py,
selected-followup-build.txt, selected-followup-audit.txt,
selected-followup-source-sha256.json and SelectedFollowupProbe.lean.

No correctness defect found.

SelectedFailure262.error_path identifies a genuine finite rebase-write prefix
ending at the diagnostic state. At distinguishes the selected-check failure from
an outside-basis scheduler failure; the latter retains successful selected-root
validation at that state. selected_provenance identifies a root actually selected
at the diagnostic state and reproduces its exact ClassCheck failure. The prefix
length is bounded by the initial remaining list. The exposed Runs witness does
not retain all prefix readiness data (the execution did check them); no stronger
checked-prefix certificate is claimed. These remain internal diagnostics, not
language rejection or source-Step simulation.

SelectedUnused262 resolves the earlier review's empty-selection limitation.
It uses the nonempty actual [focus] list and the exact existing requests, while
retaining an extra unknown unused candidate in the same finite pool. supported
shows the actual proposal is a subset of that basis. next_exact and next_written
show the scheduler either has no novel write or writes once and then stops;
run_exact constructs precisely those zero/one-write checked traces for ANY valid
finite state. It does not require the whole state to equal done.

unused_pair_outside proves the unused candidate's pair key is not in that actual
proposal; unused_pair_retained proves that key remains in the result specifically
when execution starts from initial. nonempty_success combines this retention with
successful actual selected processing. Thus successful stopping and Ready do not
mean every overapproximating candidate fact has been written. This is intentional,
not dropped source work: the retained candidate was not an actual request.

No code modifications were made. This completes the assigned review; no further
implementation or extension was performed.
