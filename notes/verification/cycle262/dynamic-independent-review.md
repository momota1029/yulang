# Independent review: dynamic source observer and exact snapshot trace

2026-11-18 UTC. Read-only review of `GeneralRebaseDynamicSource262`,
`GeneralRebaseSourceObserver262`, `GeneralRebaseDynamicTrace262` and the called finite
request-pool/actual-write interfaces. No reviewed source file was changed.

## Result

No proof or quantifier-scope defect found. The exact claims are finite rebase
completion and fixed-Plan effect preservation for an explicitly supplied observer.
They are not a complete compiler, an old-Step simulation, a changing-Plan invariant,
or a whole-language termination theorem. The source docstrings state these limits.

## Source-derived pool scope

`source_observer`, `source_step_models`, and `source_certificate` require the actual
mixed source boundary Initial proposition for sourceRegistry, root and start.
They use `mixed_finite_requests` to derive one fixed finite Output list. The pool's
existential is outside the universal quantifiers over plan, owner, inspector and
roots; it is not chosen separately for each step or each assignment. No Absorbed
hypothesis is smuggled into the new interface.

The generic DynamicSource results have the explicit stronger-looking premise
`∀ state, Covered (inspect state) pool`. The source wrapper actually discharges it
from the user's supplied inspector's reachability proof; it does not just rename
an assumed coverage certificate. The requirement covers all finite rebase states,
not merely the particular executed path. This may be stronger than necessary, but
is visible and sufficient, and no weaker unconditional compiler claim is made.

## What inspect reachability does and does not imply

Each `inspect state` must be reachable from the same source start under the old
mixed source boundary Step. The premise does NOT require successive inspected
snapshots to form a contiguous or forward-moving old-Step trace. An inspector can
choose two unrelated branches or return an earlier reachable snapshot. This is
permitted by the theorem and does not invalidate its candidate coverage or finite
new-Step measure. It is an important limitation when describing the result: the
observer is provided as an input, not constructed as a simulator of the old Step.

Roots are also supplied as a function of the current rebase state. They need not
be Generated or have a Frame/Good/Supported proof in that inspected snapshot.
The claims concern the exact requests selected by actual Alias classes and the
corresponding ClassEffects constraint formulas, not validity of every selected
packet or readiness of every request. Neither satisfiability nor a dictionary
certificate follows merely from settle returning `.ok`.

The Plan remains one fixed value throughout, including its capture-based fact
meaning. The source snapshot may vary, but the code does not update the Plan to
match it, establish plan.context correspondence, or transport a changed capture's
interpretation across prior facts. These remain separate proof obligations.

## Exact trace provenance and model quantifiers

Dynamic Trace.next records the event literally as `(inspect before, root)` where
root is a member of `roots before`. The same before state is used to build the
actual request list and write, and the tail begins at the resulting middle state.
Thus events cannot silently substitute some later snapshot or merely assert that
a root occurred at an unspecified time. from_runs and to_runs provide both
directions between such witnesses and actual finite rebase Runs.

models_exact uses one given trace and proves its equation for every assignment.
certificate constructs after/history/trace before introducing the assignment
quantifier. The final statement is initial Models conjoined with the ClassEffects
of every recorded snapshot/root event, under the fixed Plan. This is exact for
one history simultaneously across assignments; it does not prove model existence.
The accumulated constraints retain old snapshot effects, rather than replacing
history with only the final snapshot's requests.

source_certificate combines completion, position-sensitive event history, budget,
quiescence and the all-assignment model equation using the same source-derived pool.
It is the right combined interface when a caller needs both termination and semantics;
separate existential theorems need not be manually matched by an assumed pool equality.

## Independent focused verification

Three reviewed modules were rebuilt in dependency order into a separate cache using
Lean4.35.0, `--trust=0 -DwarningAsError=true`. Their earlier dependencies were reused
(including the independently rebuilt frontier layer), not rebuilt from scratch.
All three exit0. SHA256 source versions and full output are in
`dynamic-independent-build.txt`; reproduction script is `rebuild-dynamic-review.py`.

`DynamicReviewProbe.lean` separately checks ten selected axiom lists, prints the full
source_certificate/step_actual types, and proves that two arbitrary assignments
share the same after/history/Trace witness. Probe exit0; only standard propext,
Classical.choice and Quot.sound appear. No runtime benchmark, Yulang2 run or
whole-repository build was performed.
