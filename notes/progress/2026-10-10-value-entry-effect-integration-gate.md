# Bare Value entry effect constraint integration gate

Date: 2026-10-10
Branch: `research/simple-sub-intrusion`
Baseline: `7bb417ea45a651071ff87da7f7d38d81a2a93879`
Status: bounded source-owner repair integrated; focused regression and review gates complete
Authority: current inference objective, charter §§17–18, 21–24,
source-result-synthesis choice §2 and active legacy withdrawal
Mode: M2; semantic and regression review; measurement budget zero

## Actual defect and reference

A primary-owned scratch executable linked current compiled candidate libraries
and parsed/lowered four actual source fixtures. `ignore 1` had no conflict;
unused, identity and alias Value functions applied to `tick::next()` each
reported a forbidden operation-interface effect. Scratch source/output:
`/tmp/yulang-call-entry-effect-probe-7bb417/`. One compiler and one probe process
ran; these are not timing measurements or semantic proof.

The current source lambda publishes a closed-empty argument-effect port, while
Apply supplies the whole argument's evaluation effect to that port. Ordinary
Function comparison therefore requires an effectful argument to be pure. This
conflicts with the approved Value entry even when the formal is unused.
Pure local parameter lookup does not authorize that admission restriction.

Frozen Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1` distinguishes entry
value consumption from computation retention. Its propagation pure marker
routes argument effects to invocation output, rather than rejecting them.
The active successor must generate that flow at the source owner, without
restoring a port-shape conditional in generic propagation.

## Confirmed bounded correction

On the existing candidate graph/effect route, allocate entry row `e` and
invocation row `r` at the formal's actual source level, then construct:

```text
e <= r
bodyE <= r
Function(A-negative, e-negative, r-positive, R-positive)
```

Normal Apply decomposition derives argument evaluation flow through entry into
invocation. Parameter lookup and lambda construction stay pure. Use checked
fresh-effect construction, source-lambda-owned occurrences slots 3/4 and normal
store admission/provenance/propagation before Function publication at slot 2.
Existing pure construction facts slots 0/1 remain distinct. Candidate recipe
counters account for three generated lambda facts; historical routes retain one.

No raw bound insertion, level-zero anchoring, non-generic marking, body-effect
patch, skipped Function constraint or downstream conflict suppression is allowed.
Graph capture/freshening/extrusion/intrusion must transport these ordinary rows
and their relation, verified against actual source use and transaction rollback.
Incremental cost: two rows and two effect edges per candidate bare lambda.

## Verification and boundary

Require actual unused/identity/alias/captured and higher-order use, independent
fresh instances, local/recursive transport, later concrete flow, precise result
and invocation fibers, pure parameter/lambda construction, unchanged value
mismatch rejection, partial-admission failure/rollback/retry and historical
default/closed controls. Freeze before independent semantic and regression
reviews, batch accepted repairs, converge with no major/blocking finding.

This is a source inference constraint correction, not native execution or
complete Call certification. Whole-binding annotation publication and operation
signatures still need genuine provider-entry role evidence; source roles cannot
be recovered from empty ports, solved rows or latent shapes. Omitted annotation
and signature effect defaults keep their existing owning contract. Full role
comparison, native request consumers, negative attachment/filter construction,
independent public publication and target `yulang3` replacement remain required.

## Review and regression adjudication

Initial semantic/regression review found no production defect. Both found that
the new invocation oracle omitted Support allowed/tail and same-level upper
bound incidence; regression review also required pure-sibling isolation, exact
result fibers and source purity. One fresh batched test repair addressed these
findings. Fresh semantic and regression delta reviewers found no finding.

A later focused run of both historical candidate graph Call tests failed their
shared EmptyEffect argument-port assertion. Pre-write spec review confirms this
was an incidental old constructor shape, not a lasting entry contract: charter
§21 requires effectful Value argument admission even when unused. Replace only
that assertion with a symbolic negative Effect row, distinct entry/invocation
rows and directed entry-to-invocation reachability. Preserve all old capture,
demand, result, no-Empty-upper and freshness assertions and the pinned historical
observation in `2026-10-10-candidate-graph-call-review.md`. This explicitly records
the causal reason before writing the changed expectation.

The bounded formal-filter research checkpoint `9d7967c3a` is separate. Independent
source review found a missing Oracle bound-insertion filter erasure; research
repair is active. It is not production authority or effect-hygiene certification.

## Closure evidence

Fresh conformance delta review of the historical observer update found no
findings; both `--lib candidate_graph_call` tests pass with all other old
assertions retained. In total 62 distinct focused tests pass. Owning
all-target/all-feature, default and all-feature workspace checks pass without
warnings. Production code is unchanged after those checks; the final delta
changes only the independently approved test expectation. Measurement budget
consumed is zero. Native execution, full semantic certification and provider
entry-role transport remain outside this bounded gate.
