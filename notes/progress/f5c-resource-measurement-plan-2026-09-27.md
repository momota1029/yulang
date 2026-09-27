# F5c candidate resource measurement plan

Status: The approved 10-invocation candidate capture campaign completed. The
source rings 2/4/8/16, paired boxed/flat seeded depths 8/32/64/256, and widths
8/32/64 all passed. Failure/rollback/retry cases and failed-reserve/retry now
also pass with physical capacity reconciled against lane and aggregate stats.
The final filtered test passed in 4.01 seconds, with 647,412 KiB maximum RSS.
The reserve failure retained 8 bytes at capacity 8 with one growth; bounded
retry retained 16 bytes at capacity 16 with two growths. A read-only
`spec_auditor` found no issue in the final capture evidence. Ten of ten
invocations are charged; cumulative §15 time is about 44.81 seconds and
combined §15+§44 about 99.91 seconds, within the 570s and 1,010s campaign
ceilings. No further capture is authorized under this plan. This closes the
listed repository-candidate capture evidence only; no numeric supported-input
boundary or production cutover is selected, and the separate §44 gate remains
open.

## Approved ninth-command continuation and outcome (2026-09-27)

The prior eight-command plan was exhausted. Exactly one ninth capture was
authorized: rerun only the failure/rollback/retry probe after the rollback-
release and counter-assertion repair. Do not repeat the already-passing scale
capture or add input dimensions. The earlier failure invocation emitted no
F5c sample, so this command was needed to obtain the missing failure evidence.
One attempt was sufficient under that approval.

The exact command uses Cargo's offline test profile, two build jobs, and one
test thread. Any test-binary rebuild is inside the same process limit:

```text
timeout --signal=TERM --kill-after=10s 180s /usr/bin/time -v env RUSTC_WRAPPER= cargo test -p yu-solver --lib f5c_candidate_resource_probe_failures --offline -j 2 -- --ignored --nocapture --test-threads=1
```

The command had a 180-second TERM timeout and at most 10 seconds of kill grace.
It charged one command and one measurement-process invocation, raising the
cumulative count from eight to nine. The latest measured §15 wall time before
it was about 37.63 seconds; the projected maximum was 227.63 seconds. The
combined §15+§44 maximum was 282.73 seconds. Both stayed below the existing
§15 570-second and combined 1,010-second campaign ceilings. The ninth invocation exceeds
§15's default eight-process budget. The `performance_auditor`'s written
justification was that the original failure invocation stopped before any
sample, the rollback release/assertion defect was fixed and covered by the
focused no-capture regression, and this filtered command obtained the remaining
failure/retry obligation without repeating scale work. The audit approved one
ninth invocation, and primary approval was recorded before execution. It was
below the separate 16-invocation / 20-minute threshold for explicit user
approval.

The command exited 101 at `f5c_normalization.rs:221` with
`bounded reserve retry: IdentityExhausted`. It emitted failure and retry
records for the post-transfer and batch-normalization routes, but no
`F5C_CANDIDATE_RESERVE` record. The exact log is
`/tmp/yulang-f5c-failures-postfix-20260927.log`. The failure was traced to the
probe's initial `vec![1u8]` capacity not being present in its defaulted
`NormalizationStats` ledger; the first failed-reserve observation therefore
could not reconcile the aggregate baseline, and the subsequent retry also
returned `IdentityExhausted`. The helper now creates its nonempty lane through
tracked reserve and checks pre-failure, failed-reserve, and retry transitions.
`spec_auditor` closed the baseline-witness finding. Formatting and
`cargo check -p yu-solver --tests --offline -j 2` passed. The post-fix reserve
probe remains unexecuted.

## Approved tenth-command capture and outcome (2026-09-27)

The ninth-command allowance is consumed. Exactly one tenth invocation was
authorized for the same filtered failure/rollback/retry probe to verify the
corrected failed-reserve baseline and obtain its missing lane sample. The test
reruns its four small two-member failure/retry cases before the reserve probe;
this adds no input size or dimension, and the earlier records remain available
in the ninth-command log. Do not rerun scale cases or retry this command if
any assertion fails.

```text
timeout --signal=TERM --kill-after=10s 180s /usr/bin/time -v env RUSTC_WRAPPER= cargo test -p yu-solver --lib f5c_candidate_resource_probe_failures --offline -j 2 -- --ignored --nocapture --test-threads=1
```

The timeout was 180 seconds plus at most 10 seconds of kill grace, including
the test-binary rebuild. This charged one command and one measurement process,
raising the total to ten invocations. Cumulative §15 time before the command
was about 40.80 seconds and combined §15+§44 was about 95.90 seconds. The
command completed in 4.01 seconds, bringing the totals to about 44.81 and
99.91 seconds. `/usr/bin/time -v` reported 647,412 KiB maximum RSS. Both totals
remain below the local 570-second and combined 1,010-second ceilings. Ten
exceeded the default eight-process budget. The `performance_auditor` provided
written justification: the ninth command captured route failure/retry cases
but stopped before the failed-reserve record because a test-only lane baseline
was missing; the baseline repair was independently reviewed, and one filtered
capture was the remaining evidence. The auditor approved one tenth invocation,
and primary approval was recorded before execution. This remains below the
separate 16-invocation / 20-minute user-approval threshold.

The command passed: one test passed, zero failed. Both expected route failures
reached `SourceDrafts`, emitted `post_transfer` and `batch_normalization`
failure samples, and were followed by fresh successful retries with scheme
parity. The failed-reserve record reports requested slots 9,223,372,036,854,
775,808 with physical and ledger capacity 8, retained bytes 8, and one growth.
The bounded retry reports requested slots 9,223,372,036,854,775,817 with
capacity 16, retained bytes 16, and two cumulative growths. The exact log is
`/tmp/yulang-f5c-failures-final-20260927.log`. A read-only `spec_auditor`
review found no issue in this capture scope. The result does not select the
numeric supported-input boundary, authorize production cutover, or close the
separate §44 resource and rollback gate. Primary disposition approved exactly
this one invocation; no further capture is authorized under this plan.

Authority: `notes/design/2026-09-25-f5c-flat-indexed-stack-independent-draft.md`
§§5 and 15; `notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md`
§36 structural-rank deduplication; `notes/design/2026-09-26-f5c-shared-walker-flat-sink-draft.md`
all-member accounting and rollback sections; `rules/performance.md`.

## Decision this campaign can inform

This campaign established repository-bounded logical-work and physical
capacity/retained/peak observations for the unselected F5c candidate's listed
input families. It does not choose a numeric supported-input boundary or
authorize production cutover.
No representative external Oracle corpus is available. The current source
collector also defers Lambda Function facts to F5d, so the deep structural
input below is explicitly a test-seeded solver graph, not a source-program
workload. Boxed execution is included for semantic/counter parity, not as a
complete physical-memory baseline: the separate F5b §6 callback-local vector
accounting issue remains open.

## Input families

The probe harness will be an ignored test in
`crates/yu-solver/src/tests/f5c_resource_probe.rs`, exercising the same
`InferenceSession::execute_scc_plan` candidate switch and indexed finalizer as
the all-member correctness tests.

1. **Accepted source SCC.** Use the existing two-member input
   `my left = right; my right = left` (2 definitions, 2 internal references,
   2-member SCC), then generated alias rings of 4, 8, and 16 definitions. Each
   generated ring is `my n0 = n1; ...; my n{N-1} = n0`; assert the collected
   maximum component size equals N before measuring. Report UTF-8 source bytes,
   definitions, internal references, and member count.
2. **Seeded structural depth.** Start from the existing two-member compound
   route fixture in `f5c_flat_walk_sink.rs`, which seeds live constraint rows
   with Function, Union/Intersection, and Q/R structure. Parameterize the
   positive Function result chain to depths 8, 32, 64, and 256. Run boxed and
   flat routes from equivalent sessions; compare final schemes and the four
   public normalization counters. Label these cases synthetic seeded-term
   scale points, not source-corpus inputs.
3. **Seeded normalization width.** Use the same fixture with 8, 32, and 64
   repeated exact lower endpoints to exercise duplicate-heavy normalization
   through the complete SCC candidate. At each predicate and recursive-lower
   union, require one `Int`, one representative for the repeated `Function`,
   and at most the fixture's one distinct `Quantified` lower member; reject
   duplicate child IDs or any other member kind. Compare boxed/flat schemes
   and public counters. These widths are diagnostic points, not a resource
   threshold.
4. **Failure, rollback, failed reserve, and retry.** In a separate ignored
   test, measure a two-member route with a post-transfer failure and a batch
   normalization failure. Capture each failure before transactional rollback,
   then execute an equivalent fresh session without injection and record the
   successful retry. Also exercise `Normalizer::reserve` with an unrepresentable
   request against a nonempty lane, record actual capacity after the failed
   reserve, then make a bounded successful reserve on the same lane and record
   retained capacity and growth. This directly covers failed-reserve
   reconciliation and retry retention. Late indexed-finalizer failure remains
   covered by its existing correctness test only: §5 returns no successful
   `yu-types` checkpoint and defines no new solver post-failure sample there.

The repository public-signature directory contains 16 cases, but 10
`main.yu` files are blank and the nonempty examples have not been verified as
meaningful standalone `ConstraintBatch` F5c inputs. They are excluded from
this campaign rather than treated as an ordinary workload. The prior §13
surface inventory remains repository-bounded evidence only.

## Observations and checkpoints

Add a bounded `cfg(test)` capture history owned by the session-side probe
observer, separate from the transactional independent ledger and its
checkpoint/restore. Capture after each successful `SourceDrafts`, `AllDrafts`,
`IndexedMapping`, `DraftMember`, and `SchemeInstall` boundary, with component
and member ordinals. Also capture explicit failure/event records immediately
before rollback, including transfer and normalization failures that occur
before `AllDrafts`. Do not label these event records as successful boundary
samples. For each applicable sample, record:

- current source, staged-draft, and indexed-mapping bytes;
- current and retained bytes plus observed peaks for the 5 memo lanes, all 98
  walker lanes, and all 27 physical normalizer/index/output lanes (13 base
  normalizer, 8 additional scratch, and 6 emitted-output lanes). The current
  independent ledger uses 28 indexed slots; `LANE_COUNT + 3` is an unused,
  zero-capacity/request/growth placeholder between the collect-scratch and
  later scratch slots. Print that placeholder separately and exclude it from
  physical lane totals;
- per-lane requested slots, capacity growths, actual capacity, retained bytes,
  and peak capacity/bytes;
- F5 semantic/session retained and peak values and current closed-type retained
  bytes; at successful `DraftMember` samples, include the `yu-types`
  checkpoint's retained-before, retained-after, and peak-during-call values;
- for the failed-reserve case, the requested slots and actual/retained lane
  capacity immediately after reserve failure and after the bounded retry;
- solve-wide `F5cDraftWorkMeter::get()`, SCC/member counts, shared-summary
  admissions/hits, and the four public normalization counters.

Keep the capture history outside the transactional ledger checkpoint so a
failure/event sample survives rollback. A failed indexed finalizer has no
successful `yu-types` checkpoint under §5, so it contributes no quantitative
failure sample in this campaign. Derive physical capacities from the
independent ledger's actual-capacity enumeration and successful `yu-types`
checkpoints; do not copy candidate observer counters into the independent
samples. The existing independent source/memo/walker/index ledgers remain the
comparison authority. Emit a compact record per sample plus one per-case
summary. Capacity is bounded per live solver session, not by a campaign-wide
history: the largest source case has 2 component boundaries plus 3 boundaries
for each of 16 members, or 50 records. A seeded two-member route has at most 8
records; an injected failure case has at most those 8 plus one pre-rollback
event record. Run each route sequentially, emit its samples, save only the
scheme/counter result needed for parity, and drop its session before starting
the next route. The standalone failed-reserve/retry case needs at most 2 local
records. Use a hard logical limit of 64 session records and 2 reserve records;
check the limit before every push so `Vec` cannot grow during capture. Reserve
the required capacity with `try_reserve_exact` before creating the measured
session. If reservation fails, stop the capture run and mark it incomplete
before executing the candidate; do not silently drop samples or continue with
partial history. Record the vector's actual capacity separately. No
capture-history allocation occurs in production code.

The test-only diagnostic vectors are outside F5c candidate lanes. Print their
actual `capacity * size_of::<entry>()` separately, including boundary samples,
normalizer physical samples, per-member output-length samples, and boundary
history. Use external process peak RSS as a second whole-test-process measure;
do not add that RSS to F5c lane totals or describe it as production RSS. The
campaign's process samples are deterministic resource captures, not timing
benchmarks.

## Environment, commands, and budget

- Host: Linux x86_64.
- Toolchain: `rustc 1.95.0 (59807616e 2026-04-14)`, Cargo 1.95.0.
- Build mode: Cargo's default test/debug profile, offline dependencies, one test
  thread. Clear `RUSTC_WRAPPER` so the process does not depend on sccache.
- Capture the complete source/scale families in one process. A stale test
  binary rebuilds as part of this command, and its compilation is included in
  the same 180-second bound:

  ```text
  timeout --signal=TERM --kill-after=10s 180s /usr/bin/time -v env RUSTC_WRAPPER= cargo test -p yu-solver --lib f5c_candidate_resource_probe_scale --offline -j 2 -- --ignored --nocapture --test-threads=1
  ```

- Capture failure/rollback/retry cases in one process:

  ```text
  timeout --signal=TERM --kill-after=10s 180s /usr/bin/time -v env RUSTC_WRAPPER= cargo test -p yu-solver --lib f5c_candidate_resource_probe_failures --offline -- --ignored --nocapture --test-threads=1
  ```

Campaign budget under the original plan: two initial scale invocations failed
before any F5c record.
After the five-command extension, a scale capture stopped at the boxed
depth-64 accounting failure. The next reviewed capture stopped at the
over-specific width probe assertion; its probe contract was corrected and
independently reviewed. Under the final reviewed cap-eight amendment, the full
scale capture passed all source rings, paired depths, and paired widths. The
conditional failure/rollback capture then stopped before emitting a sample at
the whole-counter rollback assertion. Eight of eight capture/build commands
are charged. The latest scale process took 3.57 seconds and peaked at 556,296
KiB RSS; the failed failure-capture process took 0.05 seconds and peaked at
35,836 KiB RSS. Cumulative §15 wall time is about 37.63 seconds and combined
§15+§44 about 92.73 seconds. No further capture is authorized under this plan;
remaining time did not override its stop rule or command cap. Correctness-only
tests remain outside the capture budget under `rules/testing.md`. The reviewed
ninth and tenth continuations subsequently completed the failure/retry and
failed-reserve/retry evidence. Total use is ten invocations, about 44.81
seconds for §15 and 99.91 seconds combined. No further capture is authorized
under the ten-invocation continuation.

## Failure handling and stop rules

- The first two scale attempts failed before any F5c record. One post-repair
  capture stopped on boxed depth-64 with a test-only accounting underflow; the
  corrected sampled-source baseline passes a focused boxed depth-64 correctness
  test. A reviewed scale recapture stopped at an over-specific width assertion;
  a focused test and independent review closed that probe-contract defect. The
  final scale capture passed all listed source/depth/width cases. Its contingent
  failure/rollback capture stopped before a sample at the rollback-counter
  assertion; static audit found nonzero current memo gauges after owner drop.
  That code gate is closed by releasing memo storage, restoring zero current
  gauges, preserving history, and adding a focused no-capture full
  counter/lane regression. The ninth run stopped before the reserve sample; the
  tracked-baseline repair was independently reviewed and the tenth run passed.
  It recorded physical/lane/aggregate reserve agreement at capacity 8 and retry
  growth to capacity 16. All ten invocations are consumed; no more run under
  this plan. Do not add input dimensions.
- Stop the campaign on any boxed/flat semantic or public-counter mismatch,
  independent-lane reconciliation failure, incomplete checkpoint sample,
  unexpected `IdentityExhausted` on the listed success cases, or missing
  rollback/retry restoration. Return to the owning code gate before further
  measurement.
- On expected injected route failures, require no visible schemes, restored
  transactional counters/memo state, preserved physical peaks through
  rollback, and a successful fresh retry. Record the exact last completed
  checkpoint and failure site. On failed reserve, record actual capacity after
  the reserve result before proceeding, then verify the retry's retained
  capacity/growth accounting.
- Each capture, including any required test-binary rebuild, has a 180-second
  TERM timeout plus at most 10 seconds kill grace. Stop if any bound is
  exceeded or the §15 local aggregate wall time reaches 570 seconds; also
  enforce the combined 1,010-second limit.
  These bounds include timeout grace and remain within §15's ten-minute
  ceiling. Do not infer a supported boundary from the largest successful
  point.
- Do not select numeric size/work limits, alter Oracle semantics, switch the
  production route, or claim F5c acceptance from these repository-bounded
  samples. Those remain later reviewed gates with the required user decision.
- This campaign reports `F5cDraftWorkMeter::get()` as the exact cumulative
  logical meter defined by §5, along with the current SCC/member and public
  normalization counters. It does not add per-R-round, per-owner-check,
  trace-hop, or reachability-frontier subtotals. Those §13 diagnostic
  dimensions remain explicitly unresolved and are not closed by these samples.
