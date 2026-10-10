# Whole Function result-row source route

Date: 2026-10-10. Status: frozen, unreviewed, non-authoritative research.
Producer: `/root/bridge_result_type_route`. Claim class: one bounded executable
source characterization with an interrupted ordinary schedule; no theorem,
global impossibility, restoration-R closure or production implementation claim.
Primary-pinned baseline: `dc551aab55963802dcb506eef097907b3b098833`.
Exclusive write lease: this note; no scratch files were written.

Objective/method: test whether an explicit whole Lambda Function annotation can
share bridge's scoped result tail X and close the actual positive-extrusion
owner pair `(C,S)` while leaving `(T',T)` outside that SCC. A successful R
witness would additionally need unchanged-owner restoration, a named omitted
ordered fiber pair and failed full-use replay/diagnostic rescue.

Authority: contextual-attachment-admission design §§3.1–5; existing attachment
member grouping, annotation polarity, constructor lineage and recorded
parent/copy intrusion retain their selected meaning. Rules research-lab,
design-authority and git-concurrency and the yulang-proofs skill were read.
The constructive proof remains the primary/prover lane's responsibility.

## Exact single source and observed obstruction

```yulang
act E
my left (f:int -> ['r] int) g = { my bridge (consume:(int -> [E, 't] int) -> ['x] int): ((int -> [E, 't] int) -> ['x] int) -> [E, 'x] int = { my cb z = { my old = f 1; consume cb }; my feed = g bridge; consume cb }; bridge }
```

Existing grammar/fixtures were checked before launch: nested Function examples
in candidate_effect.rs:1568, the whole Function binding annotation at :1876,
and the TypeArrowTail/bracket-row parser owners. The make_session harness
parses this exact source, passes its empty-structural-recovery assertion,
lowers it and constructs its ordinary action schedule. The debugger replaces
only make_session's input bytes and prepared input registers; it supplies no
solver row, edge, transition or constraint. This is one distinct source root.

The formal action actually selects `Local(bridge ordinal0)` and allocates
`'t -> row23`, `'x -> row27`, both level2. The whole local annotation selects
the identical local identity at occurrence5, level2, boundary1, after Lambda1.
Its retained result view5 at byte131 has tail27; argument view3 at byte102
has tail23. Thus scoped sharing is observed, rather than inferred from spelling.
View4, the outer ordinary argument computation interface, has no tail.
Result Allowance5 is physically registered on older rows41 and53 and on its
annotation port69. This is a real Function-result check, not the previous
Function-versus-Int route.

The schedule does **not** reach the normal end-root observer at
candidate_effect.rs:1879. During this LocalAnnotation it panics at
candidate_context.rs:1846:

```text
assertion `left == right` failed: task retains its relation endpoints
left:  Effect { lower: EffectRow(27), upper: EffectRow(58) }
right: Effect { lower: EffectRow(27), upper: EffectRow(44) }
```

This is an observed endpoint consistency obstruction after actual SCC merges;
its root cause and repair are not established here. Zero errors in the observed
prefix do not establish zero-diagnostic successful root completion. The first
launch stopped at an observer bug (dereferencing an Arc as a raw pointer),
before the local annotation executed; a second launch of the **same source**
corrected that observer expression and exposed the compiler assertion. The
second Arc print displayed a handle only. A complete parsed CST/AST dump and
terminal HIR/local-route inventory were therefore not verified; no claim of
full AST verification is made.

## Same-snapshot physical evidence

Snapshot1 is at merge_candidate_rows entry, generation0, identity row
representatives, errors0. It contains 73 Effect rows, six views and 29 actual
Effect parent/copy records. Graph edges are actual owner-to-direct-lower and
owner-to-direct-upper bounds plus retained Support/Allowance-to-tail edges.
Parent provenance and capture incidence are not invented SCC edges.

| Role | Row / level | Physical retained keys at snapshot1 |
| --- | --- | --- |
| T | 23 /2 | lower56, upper61; Allowance0[23], Allowance3[23] |
| S | 25 /2 | lower30,55; upper62; Support0[23], Bottom; Allowance0[23] |
| X | 27 /2 | lower50; upper33,44 |
| R | 30 /1 | Allowance0[23], Allowance2[61] |
| negative X copy | 50 /1 | upper54,58; parent27, Negative,target1 |
| negative S copy | 55 /1 | Allowance1[56]; parent25, Negative,target1 |
| negative T copy | 56 /1 | Allowance1[56], Allowance3[23]; parent23, Negative,target1 |
| T' | 61 /1 | lower56; Allowance2[61]; parent23, Positive,target1 |
| C | 62 /1 | lower30,55; Support2[61], Bottom; Allowance2[61]; parent25, Positive,target1 |
| result checking port | 69 /2 | lower41,53; Bottom; Allowance5[27] |

Both qualifying-pair questions were tested at this same snapshot:

```text
reach(C62) = {23,30,55,56,61,62}; S25 is absent.
S25 -> C62 is an actual upper-row edge: owner pair is NOT one SCC.
T'61 -> negative-copy56 -> Allowance3 -> T23;
T23 -> T'61 is an actual upper-row edge: tail pair IS one SCC.
```

The explicit repeated argument interface creates the tail return through its
view3. This candidate has the opposite pair classification from the requested
selective-owner seam. The authentic missing key `R30 - Allowance(w[X27])`
remains absent; the new Allowance5 receiver is41/53/69, not R30 or C62.

Later retained snapshots show negative X-copy50 merged into27 (generation1),
negative T-copy56 merged into23 and T23 lowered to1 (by generation2), and
further merges before the assertion. T'61 remains a distinct representative in
the last retained snapshot; sharing an SCC here is the membership condition,
not a claim that every qualifying pair completed merging. No selective owner
SCC or later restoration/omitted fiber/no-rescue witness was observed.

## Commands, independence, budget and omissions

Reproduction uses the existing frozen runner
`/tmp/yulang-bridge-return-annotation-selective-route-20261010/run.py` without
writing it: execute its prefix before `args=['timeout'` in Python memory,
replace only its `source=` line with the exact source above, and launch its
constructed GDB commands with stdout captured through a pipe. For the second
observation the action observer also prints `x['annotation']` without
dereferencing it. The binary is
`/tmp/yulang-source-hir-selective-scc-20261010/debug/deps/yu_solver-12ea9c1c0f03380a`;
the selected existing host test is
`candidate_effect::tests::formal_and_whole_annotation_share_tail_in_the_returned_effect_fiber`
with `--exact --test-threads=1`. It is an input host; its original assertions
and manual follow-up constraints are never reached. No new test was written.

The physical reachability observer reads real bounds and views, while its
graph interpretation shares the inspected candidate_intrusion contract. It
does not independently prove those source rules. There is no external Oracle,
independent semantic model, mutation campaign, randomized seed or source range:
coverage is exactly this one source and its observed action prefix. No source
minimization is claimed. Full source induction, successful publication,
rollback/retry, exact omega, all restoration fibers, later replay and diagnostic
rescue remain unverified.

Two GDB/existing-binary invocations, zero builds, one CPU affinity, 1.5GiB
address-space cap, CPU55s/launch, timeout45s/launch, outer timeout50s/launch.
Observed launch1: wall1.261940289s, user1.095628s, system0.161447s,
peak307408KiB, returncode1 (observer error).
Launch2: wall1.355992988s, user1.151223s, system0.202888s,
peak308164KiB, returncode1 (compiler assertion).
Total executable wall2.617933277s; no timeout or resource kill, no concurrent
heavy process, no performance samples. Static reading/report time was not
measured. The second raw capture exceeded its output budget and was truncated;
the exact decisive first snapshot, relevant rows/views, later representative
changes and panic were retained. Full intermediate trace coverage is not claimed.
Second stdout SHA-256:
`f059eaee5f8e8039ac21fc7222ddde94d5c24371e6e369c37fb7b0a49c61bd1f`.

All 26 dependency/artifact hashes listed in the frozen previous
bridge-return-annotation note matched before launch and on final recheck.
They include the existing binary
`7aee4053118d02e626d70695433018c356105e8e7663e3f9776b5d922c4a4ec3`,
candidate_context.rs
`3b219b51ed8aba6ffc85675fd1d500b901a6f63b31325a85a586d688eee3515a`,
and governing design
`717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc`.
The inspected production/dependency paths also had empty diff against the
primary-pinned baseline. No dependency was changed by this producer.

Recommended next action: primary assigns a separate bounded owner audit of
relation/task endpoint canonicalization across intrusion, using this exact
source and panic, before another whole-Function route variant. This requires
separate implementation authorization for any compiler edit. R remains OPEN.

Commit packet: exact leased path
`notes/progress/2026-10-10-bridge-result-type-route.md`; baseline
`dc551aab55963802dcb506eef097907b3b098833`; changed dependency hashes none;
frozen, unreviewed, research-only. Checks already run: static grammar/owner
reads, baseline-path diff, 26 frozen-hash checks before/final, two bounded
existing-binary GDB observations, same-snapshot physical pair tests. Proposed
one-line checkpoint: `research: record whole Function result-row route obstruction`.
Shared-record deltas intentionally left for primary/curator: authentic scoped
X reuse and result Allowance receivers, failed owner/successful tail SCC
membership in the same prefix, interrupted endpoint assertion, and unchanged
OPEN R. No shared task/index/authority/question-board edit or Git mutation.
