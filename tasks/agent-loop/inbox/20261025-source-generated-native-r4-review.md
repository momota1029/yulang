# Independent filename repair delta review — frozen revision 1

Sprint SOURCE-GENERATED-INTERACTION-20261025/r4-public-filename.
Reviewer `/root/isolated_native_review_01a17247`, parent session
`01a17247-73d1-7663-9c3b-ff5b5b9c2ef1`; requested gpt-6-astra/medium,
observed model/effort UNKNOWN. Primary authored the repair; reviewer supplied
its earlier diagnosis but did not edit the example or implement the repair.
This independent review certifies only the delta and evidence described below.

Exclusive checkout `/tmp/yulang-source-interaction-01a17247-20261025`, branch
`codex/source-interaction-01a17247-20261025`, baseline `0132d07ca`.
Sole write lease: this report. Original review remains immutable.

## Verdict

ACCEPT the one-line harness repair and the separately frozen r4 evidence.
The filename defect is resolved. Both valid-filename public executions now
complete: immediate returns `44\n`; escaping returns `56\n`, causing the
unchanged independent-capture target44 check to fail. There is no new concrete
repair defect in the reviewed delta. This acceptance is evidence intake, not
native immutable-extension correspondence or semantic approval.

The naive immutable native mapping remains BLOCKED at repeated pending-cell
publication as established for the default-evidence route in the original
review. Full native/paper immutable-extension/thm:safety and original Simple-sub
A/B obligations remain OPEN. Public 44/56 corroborates the observable distinction;
it does not independently authenticate private cell identities or establish
that the same compensation analysis covers every public dictionary/view setup.

## Exact delta and pins

Compared the complete current example against source_text in original ledger
build row4 using a textual diff. The sole change is example.rs:39:

```diff
- match yu_playground::execute(&source, case, "main", STEP_LIMIT, false) {
+ match yu_playground::execute(&source, &format!("{case}.yu"), "main", STEP_LIMIT, false) {
```

Thus source(), run_low(), both generated source programs, target44, selector
behavior, and mismatch/refusal exit behavior are unchanged. No native runtime
or inference semantic change is part of this repair. The temporary formatted
String is borrowed only for the synchronous execute call; no lasting reference
is retained by this API result.

Independently matched these byte hashes:

| Artifact | SHA-256 |
| --- | --- |
| r4 contract | `7503d09945b31a065c9747be0761af8c93b319d2798ff1fda6984d16414db193` |
| primary filename repair record | `d9c9ede29f56769c0957f1b529a67e85b0c90c540240d20a341a3ba9fa004f6b` |
| corrected example | `aea1caf0b88bbce6479050ebff4989cbc3afb784e50dad228a4af70bfa3df005` |
| new three-row r4 ledger | `d08e521d9527fa693389a28214df51d35a61a098e743b339966b2ecd95a488fa` |
| original eight-row ledger | `132cab00236c36c7072d5fdf11eccb86681fc6ebc2c34a6351887e89282a0b43` |
| original independent review | `ffb247950c6111a022883cbec8af545cac1dc71f7a848cd0a6d6d13aac765f6d` |
| current generated binary | `4968d4e9dd9bc99c5f7139dd669ab7a56d40abb42dd589558af873ecfa475fc4` |

The current lib.rs, runtime/program.rs and runtime/machine.rs also match the
original review's full source pins. The new build's binary output hash equals
both new run input hashes and the current on-disk binary. The old binary hash
is historical and was legitimately superseded; its mismatch with the current
binary is not a changed-old-ledger defect.

## Public route and receipt audit

Example.rs:39 still invokes ordinary yu_playground::execute, now with
immediate.yu or escaping.yu. lib.rs:207–215 delegates to execute_runtime;
lib.rs:271–275 prepares HIR/candidate/world/indexes, calls
RuntimeProgram::from_candidate_world, then execute_program. With selected main,
lib.rs:286–299 starts the source schedule and runs Machine to completion. The
new stdout's MATCH/BRIDGE_TARGET_MISMATCH branches require Ok(actual), whereas
preparation/runtime failure would take the distinct REJECTED branch. Thus both
new results are completed ordinary public execution, not refusal or substituted
low-route observation. Public step counts remain NOT_EXPOSED.

All three new ledger source_text snapshots exactly equal the corrected example;
all input_hashes equal input_hashes_after. Commands select only public mode for
the two cases. Source printing and the actual result branches are retained.
Timestamps show serial nonoverlapping build and run intervals; all timeout flags
are false.

| New row | Observation | Exit | Measured seconds |
| --- | --- | --- | --- |
| 1 | locked/offline/-j1 incremental build succeeds | 0 | 0.389175599 |
| 2 | immediate public MATCH, actual `44\n` | 0 | 0.752035511 |
| 3 | escaping public BRIDGE_TARGET_MISMATCH, actual `56\n`, target44 unchanged | 1 | 0.881236127 |

The escaping executable's nonzero status is the harness's expected mismatch
reporting behavior; the execute API returned a rendered value successfully.
No public source/candidate diagnostic inventory or private trace is emitted by
these calls, so no stronger internal acceptance/identity claim is inferred.
The incremental build retains existing yu-hir/yu-solver warnings (28 warning
lines including two crate summaries, also present in the original build); it
is not a warning-free build. No warning is attributable to this filename edit.

## History classification and remaining owner

Old rows6/8 remain invalid-filename preparation failures, located in the
original review at source_exports.rs:728/1064 and lib.rs:525–540. They neither
become successful historical runs nor establish valid-name source refusal.
The original report's valid-filename UNTESTED status is superseded only by the
new r4 results above. Old low rows5/7 remain44/126steps and56/128steps. There
were no new low executions. Cumulative accounting remains two builds and six
native attempts, with all earlier failures preserved.

SOURCE-GENERATED-NATIVE-CELL-1 stays with primary source/proof intake: supply
the native binder/environment/cell/value/capture/replay and receiving/dispatch
relation required by the immutable sourceFresh allocation theorem, including
old arena entries and second publication of pending cells. The new ordinary
results strengthen the bounded observable evidence, not that missing proof.
No theorem quantifiers, source domain, expected outputs or semantic authority
have changed. Any runtime change or broader correspondence claim requires its
own authorized work and fresh review.

## Resource and STOP

Additional grant150 active seconds, no renewal; prior review reservation300
seconds remains charged. Delta used read-only source/ledger/hash inspection and
one leased report write. No builds, tests, Lean, source execution, scratch,
formatter, Git mutation, descendant, or outstanding process. Original report
and both ledgers were not written. STOP after freezing this report; no pending
writes or descendant leases. Final hash and clock accompany delivery.
