# F5c candidate resource measurement plan

Status: Original plan and its budget amendments passed review by
`spec_auditor`, `performance_auditor`, and primary. The source-baseline
correction cleared the synthetic seeded-depth-64 boxed ledger failure. The
scale capture then stopped at a probe assertion that treated every Union as
having only two children. The fixture's predicate and recursive lower roots
legitimately retain different distinct children. The probe now checks one
`Int` and one repeated-endpoint `Function`, permits the fixture's one
`Quantified` lower member, and no longer counts repeated root visits as unique
Unions. A focused non-ignored test passed for boxed and flat routes with scheme
and counter parity; an independent `spec_auditor` review found no issue. The
stop rule barred the failure/rollback capture. The probe repair passed a
focused non-ignored boxed/flat parity test and fresh spec review. A new bounded
continuation passed fresh `spec_auditor` and `performance_auditor` review, and
primary approves exactly one full scale capture and, only if it passes, one
failure/rollback capture. The total command cap is eight, with six commands
already charged. Each remaining command is bounded at 180 seconds plus 10
seconds grace, including any test-binary rebuild in the scale command. The
1,010s combined §15+§44 ceiling and local 570s / 440s ceilings remain unchanged.
No numeric supported-input boundary or production cutover is selected.

Authority: `notes/design/2026-09-25-f5c-flat-indexed-stack-independent-draft.md`
§§5 and 15; `notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md`
§36 structural-rank deduplication; `notes/design/2026-09-26-f5c-shared-walker-flat-sink-draft.md`
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

Campaign budget: two initial scale invocations failed before any F5c record.
After the five-command extension, a rebuild and scale capture stopped at the
boxed depth-64 accounting failure. A later reviewed amendment allowed one
rebuild and scale recapture; that capture completed source rings through 16 and
paired depth points through 256, then stopped at the over-specific width probe
assertion. The probe correction passed focused boxed/flat correctness and
parity review. Six of seven commands are charged; cumulative §15 wall time is
about 34.01 seconds and combined §15+§44 about 89.11 seconds. This amendment
proposes one full scale capture (with any rebuild included in its timeout),
then the failure/rollback capture only if scale completes successfully. This
raises the cap to eight total commands, with six already used and two remaining.
Each has a 180-second timeout plus 10 seconds grace; together the remaining
maximum is 380 seconds. The projected §15 total is 414.01 of 570 seconds; the
combined total is 469.11 of 1,010 seconds. Correctness-only tests remain
outside the capture budget under `rules/testing.md`.

## Failure handling and stop rules

- The first two scale attempts failed before any F5c record. One post-repair
  capture stopped on boxed depth-64 with a test-only accounting underflow; the
  corrected sampled-source baseline passes a focused boxed depth-64 correctness
  test. A reviewed scale recapture then stopped at the over-specific seeded-
  width Union assertion; a focused correctness test and independent review
  closed that probe-contract defect. After this amendment passes fresh review,
  run one full scale capture. Run the failure/rollback capture only if scale
  completes without any stop condition. No additional retry or input dimension
  is authorized.
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
