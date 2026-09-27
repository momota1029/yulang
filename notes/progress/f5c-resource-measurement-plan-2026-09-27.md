# F5c candidate resource measurement plan

Status: Reviewed on 2026-09-27 by `spec_auditor`, `performance_auditor`, and
primary. The later lane-slot clarification passed a fresh exact-conformance
review and primary review; it changes no input, record cap, or time budget. On
2026-09-27, after the first scale command failed before producing samples, the
user approved one additional command invocation so both planned captures can
run once after the repair. The total command cap is three including the failed
attempt; a second scale invocation also failed before producing samples, so two
commands have now been used. The stop-on-further-failure rule prevents using
the nominal third slot. The historical `Values` peak-capacity repair passed
fresh specification and performance delta review and compile-only checks, but
the capture campaign remains stopped. Further measurement requires approval to
extend the total cap from three to five commands, allowing one repaired scale
capture and one failure capture. This amendment has not been approved. The
existing 570-second aggregate wall limit would remain in force. The plan
selects no numeric supported-input boundary and does not authorize production
cutover or F5c acceptance.

Authority: `notes/design/2026-09-25-f5c-flat-indexed-stack-independent-draft.md`
§§5 and 15; `notes/design/2026-09-26-f5c-shared-walker-flat-sink-draft.md`
all-member accounting and rollback sections; `rules/performance.md`.

## Decision this campaign can inform

This campaign will establish repository-bounded logical-work and physical
capacity/retained/peak observations for the unselected F5c candidate. It will
not choose a numeric supported-input boundary or authorize production cutover.
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
   through the complete SCC candidate. Assert the expected normalized result
   and boxed/flat public-counter parity. These widths are diagnostic points,
   not a resource threshold.
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
- Rebuild the ignored test binary after the reviewed lane-size repair. The
  original prebuild took 11.1 seconds; cap this rebuild at 160 seconds plus 10
  seconds kill grace to preserve the aggregate campaign bound:

  ```text
  timeout --signal=TERM --kill-after=10s 160s env RUSTC_WRAPPER= cargo test -p yu-solver --lib f5c_candidate_resource_probe --offline --no-run -j 2
  ```

- Capture the source/scale cases in one process:

  ```text
  timeout --signal=TERM --kill-after=10s 180s /usr/bin/time -v env RUSTC_WRAPPER= cargo test -p yu-solver --lib f5c_candidate_resource_probe_scale --offline -- --ignored --nocapture --test-threads=1
  ```

- Capture failure/rollback/retry cases in one process:

  ```text
  timeout --signal=TERM --kill-after=10s 180s /usr/bin/time -v env RUSTC_WRAPPER= cargo test -p yu-solver --lib f5c_candidate_resource_probe_failures --offline -- --ignored --nocapture --test-threads=1
  ```

Campaign budget: **3 capture-command invocations total** under the approved
plan. Two scale attempts have used two invocations and failed before any F5c
record: the first took 0.1 seconds; the second took 0.06 seconds. The original
prebuild took 11.1 seconds and the later prebuild took 5.62 seconds. Total
elapsed campaign command time is 16.88 seconds. The third invocation is unused
but barred by the stop-on-further-failure rule. To collect the repaired scale
and failure captures, a proposed extension would raise the cap to five total
invocations and require a fresh ignored-test-binary build capped at 160 seconds
plus 10 seconds grace, followed by two captures each capped at 180 seconds
plus 10 seconds grace. This would total at most 566.88 seconds, within the
existing **570-second (9 minutes 30 seconds)** aggregate wall limit. The
extension is not authorized yet; stop at the current cap and await the user's
decision. The proposed five invocations remain within §15's default maximum of
eight and ten minutes. Do not add repetitions or input dimensions.
Correctness-only tests remain outside the capture budget under
`rules/testing.md`.

## Failure handling and stop rules

- The first scale attempt and its reviewed rerun both failed before any F5c
  record. The user-approved total cap is three; two invocations were used. Stop
  on any further failure and do not use the remaining nominal slot under this
  plan. A repaired scale capture plus the failure capture require approval for
  two additional invocations before either command runs.
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
- If the user approves the proposed extension, each of its two captures has a
  180-second TERM timeout plus at most 10 seconds kill grace, and the required
  test-binary rebuild has a 160-second timeout plus 10 seconds grace. Stop if
  any bound is exceeded or aggregate campaign wall time reaches 570 seconds.
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
