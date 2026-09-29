# F5c guarded-cycle in-flight progress observer plan — 2026-09-29

## Question and authority

The exact `GuardedCycle/D=32/K=32` retained-sidecar capture timed out at 180
seconds before a row was emitted. Its 393,216-byte sidecar contained 6,143
complete records plus a 56-byte fragment and is not replayable. The last 12
monitor samples showed the sidecar flat while process RSS rose from about 1.89
GB to 1.98 GB. This does not identify the memory owner or the solver's work
progress.

The source audit found that `record_reentry` scans the active path, copies
trace hops into new vectors, and retains guarded paths until the component
success or rollback cleanup. The 2,048 distinct uncacheable-state assertion is
checked after the solve; it does not bound repeated reentry copies or work.
The observed RSS is consistent with retained reentry paths and ongoing solver
work, but that is inference only.

The read-only architect review confirmed a fixed-size
`cfg(all(test, feature = "f5c_resource_probe"))` in-flight observer fits F5 §§26/34 and no-cap
§4 if it changes no production behavior, public counter meaning, row output,
sidecar encoding, or solver result. The read-only performance review rejected
logging from `F5cDraftWorkMeter::charge`, because it is called from many inner
loops. The approved local plan samples only at existing generalization
task-pop boundaries, using geometric work-count milestones; output is bounded
to at most 64 records across the entire run, including all roots/components.
Use run-wide emitted-count state and disarm after record 64; local work
thresholds may reset with a new generalizer. Normal Cargo/test lines do not
count toward this progress-record cap. Each record reads current scalar counts for
work, retained `Reentries`, `ReentryPaths` lane capacity/bytes, current path,
active/frame depth, and the local worklist capacity. It scans no vector and
does not alter the 64-byte replay sidecar. If a single task is long, the next
sample is delayed until the next task boundary; absence of a line during that
interval is not evidence of no work.

Mode M1: test-only measurement instrumentation with one `performance_auditor`
review, which found the bounded boundary-sampling approach acceptable and
warned against a hook inside `charge`. Primary budget approval covers only the
single 120-second capture and conditional 60-second replay below; it does not
authorize a repeat.

Implementation review: the observer is confined to
`cfg(all(test, feature = "f5c_resource_probe"))`. The task-pop hook is after
the existing work-meter charge and pop. It reads only scalar fields and emits
at next-power-of-two cumulative work milestones; one thread-local state spans
all roots/components and disarms after 64 records. The RAII guard clears it on
return or unwind. A focused post-write `performance_auditor` review found no
blocking issue: there is one TLS lookup per task pop in probe builds, fixed
scalar reads and bounded formatting on at most 64 milestones, and no added
production-path work, traversal, clone, sidecar field, or counter change. The
compile-only feature build and `git diff --check` passed. No ignored workload
has run for this gate.

## Measurement budget

This is a separate diagnostic plan; the earlier 180-second attempt is consumed
and will not be retried under its plan. After the test-only observer is
implemented and receives focused post-write performance review, run at most
one exact `GuardedCycle/D=32/K=32` progress capture. Use 120 seconds plus a
10-second TERM grace. A complete row and sidecar may be followed by one offline
replay process capped at 60 seconds plus a 10-second grace. Total maximum: two
process invocations and 200 seconds including both grace periods. No warm-up,
repetition, or retry.

Use 8-GiB `MemAvailable` and free-disk floors, with one-second process-group
RSS/availability/disk/log/sidecar sampling and the existing supervisor's
sidecar/log multiplier check. Keep the full-event environment variable unset.
Use unique run artifacts. Before any new process, inspect the active branch and
host floors again.

Run ID: `20260929-guarded-progress-d32k32-01`. Exact invocations after the
progress entrypoint is implemented and reviewed:

```text
python3 tools/run_f5c_resource_process.py --timeout-seconds 120 --log /tmp/f5c-guarded-progress-d32k32-01.log --monitor /tmp/f5c-guarded-progress-d32k32-01.monitor.jsonl --summary /tmp/f5c-guarded-progress-d32k32-01.summary.json --sidecar /tmp/f5c-guarded-progress-d32k32-01.events -- env -u F5C_FULL_WALKER_EVENTS cargo test -p yu-solver --lib --features f5c_resource_probe f5c_guarded_cycle_32_32_progress_capture --offline -j 2 -- --ignored --nocapture --test-threads=1
python3 tools/run_f5c_resource_process.py --timeout-seconds 60 --log /tmp/f5c-guarded-progress-d32k32-01-replay.log --monitor /tmp/f5c-guarded-progress-d32k32-01-replay.monitor.jsonl --summary /tmp/f5c-guarded-progress-d32k32-01-replay.summary.json --sidecar /tmp/f5c-guarded-progress-d32k32-01.events --existing-sidecar -- python3 tools/check_f5c_resource_matrix.py --guarded-cycle-32-32 /tmp/f5c-guarded-progress-d32k32-01.log
```

Stop on timeout, nonzero exit, process survivor, or host floor breach. The
observer enforces its run-wide 64-record cap in code. After completion or
timeout, validate progress-line shape/count from the captured log; malformed
or more than 64 progress lines rejects the run, and no replay follows. The
supervisor does not parse progress records while the solver runs, so its
120-second wall limit contains that check. Preserve artifacts and do not retry
or select another tuple. If the run completes, replay only after complete
row/count/checksum/sidecar-length checks. Report milestone work deltas against
reentry count, retained
path capacity/bytes, active path/frame depths, RSS, elapsed time, and
sidecar bytes. Do not infer an allocator owner or total-work bound from RSS
alone.

The process is useful only to distinguish whether sampled work and retained
`ReentryPaths` capacity continue to rise while serialization remains low. It
does not establish a semantic mismatch, prove an all-input complexity order,
or authorize a larger timeout, a K=4,000 diagnostic, or matrix rows. Any next
solver process needs a separate reviewed budget after this evidence is
adjudicated.

## Attempt outcome

The observer was implemented in `f5c_generalization.rs` and the ignored
entrypoint added in `tests/f5c_resource_probe.rs`. Focused compile-only
verification passed:

```text
RUSTC_WRAPPER= cargo test -p yu-solver --features f5c_resource_probe --offline -j 2 --no-run
git diff --check
```

The post-write `performance_auditor` review found the bounded task-pop hook
acceptable. Its one TLS lookup per task pop exists only in test+feature builds;
each record reads fixed scalars and formatting is limited to 64 records. A
delta review of the first-record separator repair was also clean.

The authorized progress capture ran once and timed out at 120 seconds. The
supervisor exited with status -15 at 121.335 seconds after TERM; one process
invocation and 121.335 seconds were consumed, and no replay invocation ran.
There was no completed row, so the sidecar is incomplete and not replayable.
The monitor recorded 125 samples, 1,290,932,224-byte peak process-group RSS,
29,548,920,832-byte minimum `MemAvailable`, and 665,915,027,456-byte minimum
free disk. Neither 8-GiB floor was breached. Peak log and sidecar sizes were
4,632 and 51,412,992 bytes.

The captured log contains 26 sequential progress records, from work=2 through
work=134,217,817. Reentries rose from zero to 634,860; retained
`ReentryPaths` capacity rose from zero to 41,862,272 slots (1,004,694,528
bytes). The first record was concatenated to libtest's unfinished `test ...`
prefix, so the capture does not pass the plan's standalone-line validation.
The implementation now starts the first record on a fresh line; its
compile-only check and focused performance delta review passed. The single-run
budget is consumed, so the formatting repair was not exercised by another
capture. The observer data and RSS do not prove allocator ownership or a total
work bound. No timeout retry, larger tuple, or matrix row is authorized by
this plan.

## Source adjudication

A read-only `architect` audit connected the measured growth to the current
path-expanded algorithm. For a completed predicate walk of the exact
`guarded_cycle(D,K)` builder, with no cyclic-cone summary admissions, each
cycle step offers argument and result branches. The first wrap to the starting
row therefore has `2^K` path occurrences. The opposite-polarity half continues
for a second lap; the audit derives `2^(K-1)(K+3)` guarded captures for a
completed walk. This is a source derivation for this fixture and implementation
under those assumptions, not a semantic lower bound for all equivalent
algorithms. At K=32, the first-wrap count alone is 4,294,967,296, so the
634,860 captures in the timed-out run are only a prefix. Each recorded trace
copies and retains its path; the 1.00-GB lane observation is consistent with
that growth. The 134-million work-meter value also includes other operations
and cannot be attributed entirely to reentry copying.

The fixed-point owner loop scans the growing reentry list and expands each
distinct owner at most once, in positive then negative polarity. R filtering
tests owner traces in insertion order under changing candidate masks and later
selects the first surviving trace; a single preselected trace per owner would
not preserve this general contract. A persistent prefix DAG could share path
storage while still enumerating every occurrence, but would not remove the
`2^K` traversal count. Avoiding occurrence enumeration would require symbolic
traversal and a proof for root/polarity namespaces, owner discovery, first
survivor under every R mask, Q/R ordinals, output/counters, and rollback. No
such proof or authority exists. The reviewed occurrence-preserving candidate
explicitly chose per-occurrence expansion to preserve incidence and counter
order; the no-cap addendum leaves `guarded_cycle` total-work order open and
requires separate approval for trace sharing or counter reinterpretation.

No semantic contradiction is established by this measurement. If retaining
the existing occurrence/counter contract is selected, K=32 guarded-cycle
growth must be treated as an expensive path-sensitive case with no total-work
bound. Any design that skips occurrences or changes counter/trace semantics
needs a narrow reviewed addendum and explicit user approval before code.

The same source audit gives a conditional raw-walker bound. For root `r`, let
`u_r ≤ K` be the number of distinct cyclic reentry owners discovered. The
predicate makes one positive walk; `build_inner_work` then makes one positive
and one negative walk for each newly discovered owner, so there are
`W_r = 1 + 2u_r ≤ 1 + 2K` walks. Conditional on each walk completing without
cyclic memo admission or early error, it records
`R_walk(K) = 2^(K-1)(K+3)` guarded traces. This gives the completed raw-walker
upper bound
`Σ_r R_r ≤ D(1+2K)2^(K-1)(K+3)`. At K=32, the first-wrap prefix of one walk
already has `2^32` occurrences. Each active scan and trace copy is O(K), so
raw scheduled/popped occurrences are O(D K² 2^K), while reentry scan/copy and
retained trace-hop work can reach O(D K³ 2^K). These are source derivations
for the exact cycle builder under the stated assumptions, not semantic lower
bounds for other algorithms or a measured completion result.

This closes only the raw-walker/reentry terms. No-cap §3 still requires
separate dimensions for candidate masks and R rounds, replay, materialization,
normalization, and finalization before F5c production acceptance. The
immediate next gate is a read-only phase-owner audit of those remaining terms
for `guarded_cycle(D,K)`. No further process is authorized by this plan; any
new measurement needs its own bounded plan. A symbolic/lazy traversal that
skips path occurrences remains outside current authority and would require a
narrow reviewed addendum plus recorded user approval before implementation.

The follow-up phase-owner audit gives the remaining dimensions without
claiming a single D/K coefficient. Let `R` be retained guarded traces, `H` the
sum of trace-hop lengths, `B` the path-expanded boxed predicate/bound
occurrences, `C≤K` the current R candidates, and `q≤C+1` the fixed-point
rounds. Each round's replay/frontier work is separately `P_j`, `G_j`, and
`F_j`; generic trace filtering is O(q(R+H)). Materialization is O(M_in+M_out)
in visited source occurrences and emitted nodes/edges. One normalization pass
spans all D drafts and is O(N+W_desc+C_norm), using its actual finalized
nodes, descriptor words, and exact comparison count. The selector then uses
the recursive boxed callback finalizer, not the indexed finalizer: callback
construction is O(V+E+Q+R_b) in supplied nodes, edges, quantifiers, and bounds;
the current `yu-types` validator has a conservative
O(R_b(R_b+Q)+V(Q+R_b)) membership-scan bound before its bounded plan/commit
passes. Its recursion is also depth-sensitive. These are separate phase terms
and are not the reviewed indexed-finalizer guarantee.

The current row reports physical lane capacities/retained/peaks and family
totals, but not `H`, `B`, `N`, `W_desc`, `C_norm`, callback `V/E`, validation
membership probes, or phase work subtotals. A timed-out run has no completed
row/replay. Therefore the guarded-cycle full phase equation and empirical
reconciliation remain open; the raw-walker formula alone does not close
no-cap §3. The exact matrix code paths, dimensions, and missing row fields are
captured in this audit record. Any measurement intended to fill them needs a
new reviewed plan.

## Exponential-work design recommendation

The measured run establishes exponential path enumeration in the current
producer; it does not establish a lower bound for every equivalent compiler
algorithm. The current single-predicate formula predicts
`2^(K-1)(K+3)` guarded captures, and the D=32/K=32 prefix is consistent with
that growth. There is no proof that the final normalized scheme itself must
contain exponentially many distinct nodes.

Two distinct changes have different effects. Path-prefix interning can reduce
repeated copied hop storage when prefixes actually coincide, but still visits
and records every path occurrence; a binary prefix trie can remain Θ(R).
Symbolic/lazy ordered traversal could avoid enumerating occurrences if it can
merge equivalent states, but the state includes root, polarity, active-path
context, encounter rank, R candidate mask, and rollback epoch. Those contexts
or the required occurrence-preserving output may still be exponential. No
compact equivalence partition or output lower bound is proven.

Recommendation: investigate the second option with a read-only ordered-state
equivalence proof before any code. The proof must preserve owner discovery,
first surviving trace under every candidate mask, Q/R order, scheme/facts/
diagnostics, public causal counters, checked failure and rollback, and physical
lane accounting. If it skips old charged operations, the accounting schedule
needs explicit authority. The current F5 §§25/26/34 and no-cap §§3–4 do not
authorize silently changing those meanings. Any such implementation needs a
narrow reviewed addendum and explicit user approval first. Prefix interning
may be evaluated separately as a memory optimization, but it cannot resolve
the observed traversal count by itself.

The next gate is a read-only proof of whether the exact guarded builder's
retained normalized output has exponentially many distinct nodes and whether
an ordered symbolic state can answer earliest-surviving-trace queries without
visiting every occurrence. There is no demonstrated fundamental impossibility
yet. If no quotient survives those obligations, retain the current semantics
and ask for an explicit decision about revising the infeasible guarded-cycle
evidence gate; do not introduce a numeric cap.

The first feasibility pass proves an exponential lower bound only for the
current boxed implementation. Each cycle row has one Function endpoint per
polarity, the walker constructs a Function per expanded occurrence, and the
boxed sink cannot share these occurrences. Replay and binder substitution
rebuild every Function; normalizer flatten assigns a fresh node to each
occurrence and rebuilds a unique boxed `TrackedOne` tree. Descriptor ranking
does not hash-cons Functions. The first full binary lap therefore leaves at
least `2^K-1` Function occurrences in the current normalized boxed predicate;
callback finalization must traverse them. This shows why trace-prefix sharing
alone cannot fix current output cost, but it is not a lower bound for an
equivalent shared indexed graph.

For this exact fixture, reentry traces contain only Exact and Function hops,
so trace path survival is mask-independent; owner-bound survival and
reachability still depend on R masks. A compact first-witness query appears
possible because the earliest surviving trace for an eligible owner is its
first producer encounter. That remains a hypothesis for the full Q/R and
output contract. A generic state keyed by exact active-polarity history has
exponentially many contexts. Next prove the number of distinct normalized
subgraphs under the final Q/R assignment; only if that output can stay compact
does a symbolic producer addendum have a credible path to subexponential work.
No implementation is authorized by this audit.

## Adversarial lower-bound review

The earlier feasibility note left open whether a shared indexed DAG could
represent this exact output in O(K) nodes. A focused `compiler_referee` review
closed that question for the current F5 scheme shape. For `guarded_cycle(1,K)`
with K≥2 and successful exact output, the first lap has 2^(K−1) branch
sequences that return to row 0 in negative polarity. Repeating each sequence
on the second lap yields a reachable Function chain in the predicate. Its
PositiveFunction/NegativeFunction discriminator sequence records the first
lap polarity choices. At the first differing choice, the normalized ordered
Function descriptors differ, so hash-consing cannot merge these subgraphs.
Replay and substitution replace Variable leaves only; normalization retains
the Function constructors and ordered descendants. The normalized graph
therefore contains at least 2^(K−1) distinct reachable nodes per successful
root predicate. The finding depends on the exact F5 §§25/34 scheme-shape
contract and successful finalization; it is not a lower bound for every
Oracle-equivalent compressed representation.

The review did not establish which exact R owner survives, the Q ordinals,
the exact total node count, or sharing across root rotations. It also did not
prove the one-sided-variable sets empty; that is unnecessary to the lower
bound because replay/substitution preserve Function nodes and the selected
predicate reaches the ladder. No tests or workloads were run for this proof.

This supersedes the earlier hypothesis that a shared indexed DAG might give
O(K) nodes under unchanged F5 scheme shape. A compact prefix store or ordered
trace query cannot make the exact current normalized DAG subexponential. To
make this family practical at K=32 would require a representation that
compresses the exponential set of distinct Function subgraphs, with a new
contract for its consumers, or a change to observable scheme shape. The other
path is to retain the existing output-sensitive exponential behavior and
amend the guarded-cycle evidence gate; no numeric cap is authorized by either
path. This choice requires explicit user approval before changing an
Authoritative gate or scheme representation.
