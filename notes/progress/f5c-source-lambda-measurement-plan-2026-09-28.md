# F5c source Lambda candidate measurement plan

Status: Reviewed and authorized by the primary on 2026-09-28 for exactly one
dedicated capture process. Harness eligibility checks, the named non-capture
correctness test, and focused M2 code review are complete; accepted review
findings were repaired and both specification/performance deltas closed with
no open issue. The capture command is now ready but has not run. The earlier
§15 campaign remains complete and closed under its own plan; this is a fresh
campaign for source Lambda/Function inputs connected by the F5d source recipe
gate.

## Decision and scope

Measure repository-bounded logical work and physical capacity/retained/peak
values for source programs that the current collector admits as complete
one-parameter Lambda recipes. This closes the practical-source-input evidence
gap created when F5d connected those recipes to the F5c boxed and flat
candidate paths. It does not select a numeric supported-input boundary,
authorize production cutover, or certify an external Oracle workload.

The 241-byte and 274-byte stable-core examples remain excluded: their nested
Function/method shapes have not been shown eligible under the exact current
recipe. No larger source form, nested Lambda, effectful body, or unverified
fixture may be substituted during this campaign.

## Inputs and correctness witnesses

Run each successful input through boxed and flat sessions built from the same
source. Require equal canonical scheme tokens and equal values for all four
normalization counters. Capture resource records only from the flat session.
Before either route executes, require source collection to have no diagnostics
and assert the exact definition count, eligible Lambda recipe count, complete
body status, and resolved-use count. Also inspect the planned SCC partition:
the name-body example has two singleton SCCs and one dependency edge; each
recursive ring has one SCC of size `N` and `N` internal resolved uses.

| Family | Exact source / generator | UTF-8 bytes | Definitions | Maximum SCC members | Purpose |
| --- | --- | ---: | ---: | ---: | --- |
| Identity Lambda | `my f x = x` | 10 | 1 | 1 | Quantified Function path |
| Constant Lambda | `my k x = 42` | 11 | 1 | 1 | Closed pure Function path |
| Resolved module-name body | `my n = 42; my f x = n` | 21 | 2 | 1 | Name-body recipe with one dependency edge |
| Productive self recursion | `my f x = f` | 10 | 1 | 1 | Recursive Function graph |
| Productive Function SCC ring | For each `N` in 2, 4, 8, 16, generate `my n{i} x = n{(i+1) mod N}` for `i = 0..N-1`, joined by `; ` | 26, 54, 110, 234 | N | N | Function-bearing recursive SCC scale |

The ring generator must assert the listed byte length, `N` definitions, `N`
complete Lambda recipes, `N` total resolved uses, one SCC containing all `N`
definitions, `N` internal uses, and productive recursive Function schemes.
The identity, constant, name-body, and self-recursive cases have respectively
1, 1, 1, and 1 complete Lambda recipes; their total resolved-use counts are
0, 0, 1, and 1. The name-body dependency must cross its two singleton SCCs.
Update the probe helper to perform these eligibility checks immediately before
creating the candidate session, so the capture itself cannot rely only on an
earlier correctness run.

Before the dedicated capture command, add and run the focused non-capture
correctness test `f5c_source_lambda_function_correctness`. It must run boxed
and flat sessions for all eight successful inputs, compare canonical schemes
and all four normalization counters, and verify that each recursive input
produces a productive recursive Function scheme. This checks the generated
4/8/16-member rings, which the existing F5d test does not cover.

## Failure, rollback, and retry

On the two-member Function ring, run one flat candidate with batch-normalizer
failure injected after zero completed members. Capture the failure event
before rollback, verify there is no published scheme, and retain the physical
high-water record. Then use a fresh session for a successful flat retry and a
boxed parity reference. The retry must match the boxed schemes and all four
normalization counters. The failure record must identify
`batch_normalization`, have no successful-boundary label of its own, and name
`SourceDrafts` as its last completed boundary. No additional failure injection
or reserve-failure dimension is part of this campaign; the existing separate
§15 failure/rollback capture remains the evidence for those cases.

## Observations and reconciliation

Use the existing `F5cCandidateCapture` observer and independent resource
ledger. At each component ordinal, capture successful `SourceDrafts` and
`AllDrafts` records. For each member ordinal, capture successful
`IndexedMapping`, `DraftMember`, and `SchemeInstall` records. Preserve the
distinction between those boundaries and the pre-rollback failure event. A
successful input with `C` SCCs and `D` definitions must emit exactly `2C + 3D`
records; the 16-member single-SCC ring therefore emits 50 records. The
two-definition name-body input emits 10. The failed two-member ring emits one
successful `SourceDrafts` record and one separate failure event, with no later
successful boundary. Each sample must include source/staged/indexed bytes;
actual capacity, retained bytes,
requests, growths, and peak capacity/bytes for the five memo lanes, all 98
walker lanes, and all physical normalization/index/output lanes; semantic and
session retained/peak values; closed-type retained bytes and successful
`DraftMember` checkpoint values; the solve-wide F5c draft-work meter, SCC and
member counters, shared-summary admissions/hits, and four normalization
counters. Keep the history bounded by the existing 64-record-per-session
limit and stop if the observer cannot reserve or retain every record.

Repair the source-probe summary labels before capture: it currently prints
`max_scc_members` as if it were both total definitions and internal references.
The summary must report `source_bytes` and `max_scc_members` only unless the
other values are independently counted from the batch. Do not derive any
numeric threshold from the largest passing ring. The `yu-types` lane-event
snapshot added on 2026-09-28 is compiled only in `yu-types`' own unit-test
target, not as a dependency of this `yu-solver` probe; still retain its
test-only O(E) storage in the earlier gate record, not as candidate-probe
physical bytes.

## Environment, command, and stop conditions

Environment: `rustc 1.95.0`, Cargo `1.95.0`, `x86_64-unknown-linux-gnu`,
offline Cargo test profile, two build jobs, and one test thread. The timed
process includes any test-binary rebuild. Run exactly one dedicated capture
process:

```text
timeout --signal=TERM --kill-after=10s 180s /usr/bin/time -v env RUSTC_WRAPPER= cargo test -p yu-solver --lib f5c_candidate_resource_probe_source_functions --offline -j 2 -- --ignored --nocapture --test-threads=1
```

Budget: one capture process; one command; 180 seconds before TERM and at most
10 seconds of kill grace (190 seconds total maximum). The peak RSS from
`/usr/bin/time` covers the whole process, including any rebuild and both
boxed/flat parity routes; use the independent lane records for candidate
resource attribution. This is within the
ordinary eight-process / ten-minute measurement budget. This is a deterministic
work and capacity capture, not a timing benchmark; no warm-up or repeated
timing samples are needed. Record elapsed time, peak RSS, exact test count,
input bytes, and all emitted capture rows.

Stop at the first collection error, missing/ineligible Lambda recipe, SCC-size
mismatch, scheme/counter mismatch, failed physical reconciliation, missing or
mislabelled failure sample, capture-limit/reservation failure, unexpected
diagnostic, or timeout. Preserve partial output and mark the campaign
incomplete; do not rerun or add an input dimension without a newly reviewed
plan. The plan review gate is closed, but the capture command remains gated on
implementing and reviewing its harness prerequisites.

Authority: `notes/design/2026-09-25-f5c-flat-indexed-stack-independent-draft.md`
§15; the F5d source recipe and Lambda tests in `crates/yu-solver/src/lib.rs`;
`notes/progress/f5c-resource-measurement-plan-2026-09-27.md` (closed prior
campaign); `rules/performance.md`; and the prior 2026-09-28 M2 review record
for the test-only `yu-types` lane-event snapshot.
