# R48 independent compiler review

Status: **BLOCKED — actual scoped fixture cannot reach temporal inspection**.
Reviewer: `/root/r46_compiler_review`; sole author; no descendants.
Requested role: compiler_referee. Observed effective model/effort: UNKNOWN / UNKNOWN.
Only this review receipt is a permitted write. No compiler, Cargo, test, runtime
probe or Git command was run.

## BLOCKING R48-C1 — active-root Link cannot satisfy scoped Apply authentication

Exact trigger: `candidate_scheme.rs:2663–2677` constructs the existing recursive
fixture, calls `collect_candidate_mode_scoped(hir.clone(), true, true, true)`
and then `session.execute().unwrap()`. The fourth argument enables the scoped
experiment (`lib.rs:940–950`). This is the same q/helper constructor required
by the R48 contract; no alternative consumer or fixture is substituted here.

`candidate_source.rs:1090–1104` registers each parameterized initializer as an
active root until Install removes it. The loop initializer remains active
while its direct `loop x` and nested helper-body `loop y` are visited. At
`:1244–1249` each such Local Name emits `Action::Link`, rather than
`Action::Local`. The block worklist at `:1032–1041` processes bindings in source
order; the direct recursive Apply is before the helper use and the later
inspection. Apply construction at `:1292–1310` still retains a local-callee
witness for the exact recursive Name.

At `shadow_apply.rs:1772–1775`, admission of that scoped Apply unconditionally
calls `candidate_call::authenticate_scoped_apply`. The latter requires a
`local_route_by_occurrence` entry for that exact Name occurrence
(`candidate_call.rs:723–734`, specifically `:727`) and an installed scheme plus
an authentic `LocalFreshRoute`. `Action::Link` only admits a value link
(`candidate_source.rs:1669–1673`); it creates neither that occurrence-index
entry nor a FreshUse route. The sole publication site is
`GraphState::commit_local_use`, `candidate_scheme.rs:688–691`, reached through
Local reconstruction. A route for another occurrence cannot satisfy the lookup.

Consequently the direct active-root Apply admission returns an error before
both helper routes and their q/C/D temporal joins can be inspected; the test's
`session.execute().unwrap()` cannot establish the proposed positive evidence.
Even if an earlier independent failure occurs, it cannot rescue this missing
mandatory route. The same ownership mismatch applies to q itself.

This is a static reachability obstruction in the pinned candidate route, not an
observed runtime result, an inference counterexample or a request to change
source admission. It predates the R48 ledger additions, but directly prevents
the required R48 witness. Deferring reachability to an execution attempt is
insufficient once this mandatory guard is statically contradicted.

Violated contract: Fixed outcome requires the authentic actual q/helper route;
Resources and stop conditions require reporting the earliest execution/evidence
obstruction and prohibit a test when reachability is unsupported. Parent source
semantics and the test expectations cannot be changed to manufacture a witness.

Minimum closure within this contract: record the active-root Apply admission
obstruction and its source/authentication owners as the R48 stop result, retain
the ledger/proof as unexecuted candidates, and withhold the gated positive test.
Any later authority or constructor decision belongs to the primary; no source
change is proposed or authorized here.

Exact falsifier: identify an authentic execution owner on this same frozen path
that publishes a LocalFreshRoute for the exact active-root Name before Apply
admission, or show that the guard accepts its retained Link as sufficient.
A sibling/helper FreshUse, endpoint equality or fabricated map is insufficient.

## Separate ledger and conditional-proof audit

No additional BLOCKING, major or minor issue was established in the bounded
static ledger audit. This statement does not certify executable Rust or actual
fixture coverage, because C1 prevents the required consuming execution.

The inspected private-forest mutation set is identity extension
(`candidate_intrusion.rs:342–352`), merge assignment (`:672–689`), compression
(`:530–564`) and rollback restore/truncation (`:202–223`). The test hooks log
before the actual writes. On successful logging, these sites have no fallible
operation between the event and the corresponding assignment; identity pushes
and compression undo storage are pre-reserved. Writes followed by later errors
remain in the monotone log. Logging failure marks the history permanently
incomplete; rollback ignores the logging error to restore actual state while
the validator subsequently rejects that incomplete history. The log is outside
Undo, so rollback and commit do not erase the observed transition sequence.

`candidate_scheme.rs:1218–1221` snapshots the forest before immutable capture;
`:785–787` and `:1621` retain owner cursors. Replay at `:2250–2292` checks old
links, bounds, births and truncation. `:2317–2346` checks historical source cuts
and compares replayed complete arrays at inspection with live arrays. The join
at `:2408–2441` binds route and map references to retained owners; selection at
`:2447–2457` uses the signed endpoints at capture time instead of their final
class. These address the previous final-representative shortcut.

Lifetime remains a separate structural premise: the retained route and its
fresh image vector move from the actual Local frame only on successful commit;
rollback clears new frames/routes and restores existing cursors and live-storage
lengths (`lib.rs:9304–9312,9470–9490` and subsequent row-length restoration).
The conditional proof correctly requires that owner lineage and does not derive
allocation survival from a forest key or final representative alone. Its replay
induction is conditional on exhaustive mutation coverage, not on final-array
equality as a substitute for coverage.

Both q coordinates and both retained helper routes are demanded by the test
join, with indexed Parent/source-event/structural-comparison authentication.
The existing wrong-q, missing-event, coordinate/polarity, sibling-route/map,
wrong-comparison and forged-Parent controls remain in the frozen test text.
They are assertions, not executed negative-control evidence. R47's no-hit
invariant remains appropriate for each successfully prepared immediate helper
capture; its validity does not prove these helpers are reached by this scoped
fixture. No later-hit requirement was reintroduced.

New observation state/hooks are guarded by `cfg(test)`. Static inspection found
no intended change to production solver decisions or source behavior. No
non-test compilation, binary comparison, resource measurement or full
regression suite was performed. The unconditional row conversion refactor in
identity extension retains the same checked conversion before insertion.

The original inference/evaluator theorem and Simple-sub A/B remain **OPEN,
0 → 0**. No Desc, ordered D_q, source Call, evaluator, global transport or
production claim is certified.

## Frozen bytes and review scope

All five assignment pins matched recomputation. The supplied implementation
receipt hash names the progress report, whose hash matched; the implementation
inbox was separately hashed below. Source dependencies used for the admission
trace also matched their earlier pinned bytes. `candidate_call.rs` is the direct
authentication dependency additionally inspected at the same R46 source pin.
This review used source/control-flow evidence, not producer explanation or a
prior reviewer's result, to establish C1.

| Path | SHA-256 |
| --- | --- |
| `tasks/agent-loop/sprints/actual-route-temporal-transport-20261019-r48.md` | `e17bd3f602cb00cb600d6647432a18cc6df5d5ce8d5eb59a78eba52eb8dfbc5a` |
| `notes/theory/2026-10-19-r48-actual-route-transport.md` | `50f70a8a47faaac1cff670044faf4faafbf2a495d0a437bcab6bee1983095e13` |
| `notes/progress/2026-10-19-r48-actual-route-transport.md` | `dd9aa87b15835105ed6445c3106045d1b9a84447dfa2a8ab1bd7fc7f3a0eb884` |
| `tasks/agent-loop/inbox/20261019-r48-implementation.md` | `eba919cb09b3d15493783cd2c81c47c02ad5f5fa24318f92115eac87c24288df` |
| `crates/yu-solver/src/candidate_scheme.rs` | `d4ff8a9e98eb667a5eb85aff9c0feec1f0227e86257bb56892493ac1d04a9278` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `8a1f531be9fb5e5f160bf4f75c6eb98bbc35ce0a30acaf06424c531840504ba4` |
| `crates/yu-solver/src/candidate_source.rs` | `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c` |
| `crates/yu-solver/src/lib.rs` | `2300400e87d0a487225f207d414ac71fa4f21c6f80279fea4f793e43c7809aee` |
| `crates/yu-solver/src/shadow_apply.rs` | `d5e6b179fd4f6fbca579b0fa4d479d8bd11b520d774acbf27f414451c4691137` |
| `crates/yu-solver/src/candidate_call.rs` | `e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479` |
| `crates/yu-solver/tests/candidate_local_self_recursion.rs` | `47ced76fe8f0f136c42802b2376ca09f7cadec0fc8e5b1b3d4c6acc7bc613e55` |

Resource receipt: 300-second review ceiling respected; actual full elapsed time,
CPU and RSS not measured. First clock observation: 2026-10-18 16:24:11 UTC;
second observation: 16:24:47 UTC. These cover only part of the review.
Read-only inspection and SHA-256 recomputation only; no source/target edits,
Cargo/build/test/runtime, Git, external contact or descendants.

**WRITES_STOPPED; NO_DESCENDANTS**. Only this exact review path was written.
