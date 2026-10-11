# `run` lineage capture: completed-query seam blocker

Date: 2026-10-12
Status: repaired hook independently reviewed; build and one bounded capture completed; source-origin join remains open
Claim class: completed bounded runtime observation; source-to-output contribution join remains open
Exclusive Y3 lease: this file only
Y3 baseline: `c1041f8f4706e847bf709e36728211965be24980`
Oracle baseline: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Oracle worktree: `/home/momota1029/rust/yulang2-oracle-capture`

The initial no-run blocker below is historical and superseded by a later
primary-authorized two-file instrumentation seam. Its independent review
remains scoped to that initial blocker. The follow-up hook received two major
and one minor findings, was repaired and independently re-reviewed, and has
now been built and used for one bounded capture. Its result and remaining
source-coordinate limitation are recorded at the end.

## Objective and accepted dependencies

Follow the [source lineage audit](2026-10-12-run-origin-lineage-audit.md) with
one bounded observation capture: emit application ExprId, OriginId, demand
ConstraintRecordId, four Function port endpoints, result Effect and forwarding
record IDs; join selected bound ancestry; query the designated post-instantiation
outer Call output Effect. Preserve ordinary inference behavior and keep H and
complete Call OPEN.

The accepted input remains the explicit int variant in
[native negative residual derivation](../theory/2026-10-12-native-negative-residual-constructor-derivation.md)
§11, SHA-256 `73b4a2d12233b9b658188f3baa17edb04c14a89f94217198befca22db4af77d9`.
§11's successful P_sel capture is accepted; the particular concrete send's
origin, lineage and final output membership are unestablished. The original
str fixture and its timed-out default-prelude transcript are excluded.
Governing source/output distinction is §9.2; §11 does not equate final scheme
shape with source contribution survival. Authority and rules remain those
recorded in the preceding audit; no new semantic decision is made here.

The follow-up first named an absent Oracle tail path. The primary corrected
the exact private observation lease to
`crates/infer/src/lowering/expr/tail.rs`. It subsequently permitted an existing
final observation file, but named `crates/infer/src/source/mod.rs`, which is
also absent. The existing final source-label hook is actually
`crates/yulang/src/source/mod.rs`. No source file was modified under either
spelling. The missing path alone is not the substantive query blocker below.

## Concrete instrumentation blocker

The frozen five-file instrumentation has no application/result-Effect
handoff. Existing `tail.rs:535–688` locals can supply the initial source event,
but this is before completed global-use processing. In
`lowering/name_ref.rs:108–111`, a global reference enqueues
`AnalysisWork::ApplyRefResolution`; its actual use is resolved/instantiated by
the analysis owner. Querying at `make_source_app` observes the construction
phase and cannot be labeled the completed outer Call output query. Forcing
analysis work to drain there would change ordinary scheduling.

The existing final hook is
`crates/yulang/src/source/mod.rs:5590`, called at
`source_diagnostics_for_check:4505`. Both functions take immutable
`&infer::check::PolyCheckOutput`. `PolyCheckOutput` retains the session machine
through `lowering.session.infer` (`crates/infer/src/check.rs:20–24`), so the
actual completed owner exists. However:

- selected projection collection is infer-private and takes a mutable machine:
  `crates/infer/src/compact/surface.rs:173–188`,
  `compact_type_var_recording_merge_constraints_for_scheme`;
- that operation opens an authenticated projection round and can return an
  error/fallback; a trustworthy capture must retain its actual status;
- source-span explanation export is infer-private:
  `crates/infer/src/constraints/explain.rs:600–613`;
- raw public bound iteration (`constraints/machine/entry.rs:115` and
  `constraints/mod.rs:2409,2704`) is a different observation from the selected
  projection. It cannot silently replace the requested output query.

Private visibility by itself could be handled by an inherent observation helper
defined inside the authorized infer file. The decisive remaining seam is
**completed mutable access plus the retained designated output identity**:
the final hook's shared borrow cannot invoke the existing projection query;
the source application locals have already been consumed. No existing env
parameter in the five frozen hooks hands an application result Effect to a
completed output query. The hooks log generalized definition roots, Function
ports encountered by their collectors, finalized schemes and source labels.

Consequently, this packet stopped before editing/building. No early query was
misrepresented as final; no raw bound dump was substituted for projection;
no forced inference work, unsafe mutable access or extra inference admission
was introduced. There is no capture result or concrete numeric lineage join.

## Smallest next seam

Recommended next action: authorize a bounded **infer-owned completed-check
observer** with an explicit identity handoff from the application constructor,
and keep the external source-label hook unchanged. The completion owner is
`crates/infer/src/check.rs:167–178`: after `lower_loaded_files` has returned the
actual lowering/session and before `PolyCheckOutput` is returned. A deliberately
mutable local lowering can invoke a helper only under the research environment
gate, after ordinary inference and reporting have finished. This is a proposed
observation seam, not implemented or certified here.

The packet must specify the storage owner for source spans, session identity,
source application ExprId, origin/demand IDs and designated result Effect;
capture the two forwarding IDs while their handles coexist; and define bounded
selected-proof/ancestry export and query failure behavior. Keep semantic
generation, propagation, generalization and publication unchanged. Inspect
whether the projection query's permitted internal cache/failure effects are
compatible with the intended observation equivalence before execution.

The finalized `run` Function's return-effect port and the outer source Call's
result Effect are different designated observations. A capture that only
prints the former would repeat §11 and leave this packet's premise untouched.

## Checks, resources and omissions

Commands: bounded `rg`/`sed` source reads and `sha256sum` of direct owners and
the five frozen instrumentation files. Some initial search output was truncated
and guessed paths were absent; decisive query signatures and hook bodies were
then read directly. No exhaustive search claim is made.

Authorized upper limits: one serial offline locked build, 180 seconds/2 GiB;
one int inference execution, 120 seconds/2 GiB. Consumed: zero builds, zero
inference runs, zero tests, zero heavyweight processes. One leaf, no delegation
or Git mutation. Exact CPU/RSS were not measured. No seeds, enumeration ranges,
mutations, differential oracle or runtime equivalence experiment occurred.

The default-env no-log/no-query requirement was not tested for a new patch:
there is no new Oracle patch. Existing five-file instrumentation remains
byte-identical to the accepted §11 snapshot. This static obstruction shares
that Oracle source baseline and does not independently validate its semantics.

Frozen Oracle dependencies, SHA-256 (unchanged):

| Path | Hash |
| --- | --- |
| `crates/infer/src/lowering/expr/tail.rs` | `ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8` |
| `crates/infer/src/compact/surface.rs` | `af31f1e68654831f1d005a7070bc50367a34691cc55dadddadfe55bb5e207c6c` |
| `crates/infer/src/analysis/session/generalize.rs` | `4ea4821eb197ceecb82db9c8520458ea1b14f40f2d1e8e7b0c79566279e3e988` |
| `crates/infer/src/compact/collect/mod.rs` | `23dce0d501aac161b0bd4d702ba6eda65c45a38f23c53965b62b32537a084b7a` |
| `crates/infer/src/compact/collect/type_nodes.rs` | `405a1bf9b40a2dff55cbd20a22902f1acb244efb39578ebabac9f341954f1cf8` |
| `crates/yulang/src/source/mod.rs` | `de29d6bbcbe8a969f7bf77b852cae2c314de1d6158c6cdb7dec8b6022e06d059` |

Independent review: compiler-referee found no blocking, major or minor issue.
The review confirmed that the early source-app hook precedes global-use
resolution and the final immutable source hook cannot call the selected
mutable-machine projection query. It also confirmed `check_loaded_files` as a
plausible completed-query owner, while leaving query side effects and
observation equivalence for that next seam to establish. This review covers
the static blocker only; no capture was run.

Unverified: actual origin/demand/forwarding IDs, selected-record source ancestry,
actual use instantiation mapping, designated output projection and contribution
membership, observational equivalence, original fixture, H, complete Call,
soundness and principality.

## Commit packet

- Exact changed/leased Y3 path: `notes/progress/2026-10-12-run-origin-lineage-capture.md`.
- Exact separately leased Oracle paths: `crates/infer/src/lowering/expr/tail.rs`
  and `crates/infer/src/check.rs`, in the private capture worktree only.
- Baselines: Y3 `c1041f8f4706e847bf709e36728211965be24980`; Oracle
  `a58eefc31e22141574b6f20c6a5748151c6d79f1` plus existing §11 instrumentation.
- Changed dependency hashes: two Oracle paths, listed in the follow-up snapshot
  below. Five accepted §11 instrumentation dependencies were preserved.
- Status: frozen repair awaiting re-review; build failed under the virtual-address
  cap before this repair; inference capture did not run. Initial blocker review
  is preserved and is not approval of the new hook. All parent gates remain OPEN.
- Checks already run: static owner/signature/diff and hash reads; one authorized
  build failed. No tests, inference execution or second build.
- Proposed commit message: `research: record bounded run lineage instrumentation build failure`.
- Shared-record deltas intentionally left for primary/curator: preserve P_sel;
  record the failed build and absent runtime join; adjudicate memory enforcement
  before assigning a fresh build/capture packet. The Oracle patch remains
  private research instrumentation, not production implementation.

## Authorized follow-up and failed build (historical, superseded)

The primary subsequently granted the completed observer and identity handoff
explicitly, leasing exactly Oracle `crates/infer/src/lowering/expr/tail.rs` and
`crates/infer/src/check.rs`. This supersedes the earlier packet's two-path
feasibility blocker; it does not make the earlier static report false. The
existing int input was confirmed as `/tmp/yulang2-run-projection.yu`, whose
SHA-256 matches §11. The target was the existing
`/tmp/yulang2-oracle-projection-target`.

The initial private hook attempted the following. The resource/status claims
in this pre-review description are qualified by the findings and repair below:

- Under `YULANG_RESEARCH_RUN_LINEAGE=1`, clears thread-local event state at
  `check_loaded_files` entry, assigns a monotonically increasing thread-local
  scope, and records at most 64 source application events.
- At application construction, records actual source OriginId/boundary,
  ExprIds, callee/argument Value and Effect coordinates, demand record and four
  Function port handles, result Value/Effect, call Effect, and both forwarding
  endpoint/record tuples. `make_source_app` attaches the actual spans.
- The env-on forwarding branch reproduces the exact two original helper
  admissions, including their allocation order: evaluation upper, evaluation
  lower, first subtype; return upper, second subtype. Extra work consists of
  record lookup and event storage. No new semantic edge is admitted.
- After ordinary `lower_loaded_files` and summary creation, consumes events
  on the same thread with the same scope, then opens existing authenticated
  projection queries on the actual mutable machine for the selected `run`
  definition root and each recorded application's designated result Effect.
  Attempted to emit selected records, endpoint shapes, claim proofs, compact
  results and portable ancestry/source sites. It did not force analysis work.
- The direct projection query preserved its Result, but the separate compact
  wrapper erased failures into a default root. Compact status was therefore
  not reliable. Logging/export bounds did not cap all pre-export collections;
  TLS also lacked cleanup on lowering error. No complete-query-status or
  end-to-end resource-bound claim is made for that initial hook.

Default-environment argument, by static branch inspection: an absent research
environment variable makes `research_lineage_begin` return `None` before TLS
access; application recording/source-span handoff are skipped; the original
two forwarding helpers run; `research_lineage_finish(None)` returns before
logging, event storage or query. No new arena allocations, TLS event storage
or semantic operations are added on that path. This is a source argument,
not a successful compiled equivalence experiment. The new observer has not
established actual same-thread scope delivery, unchanged epochs/terminal state
or source-to-output membership at runtime.

One build was attempted with the exact command:

```sh
ulimit -v 2097152
/usr/bin/time -v timeout --signal=TERM --kill-after=5s 180s cargo build --locked --offline -p yulang -j1 --target-dir /tmp/yulang2-oracle-projection-target > /tmp/yulang2-oracle-projection-target/run-lineage-build.log 2>&1
```

Result: exit 101; `rustc-LLVM ERROR: out of memory`, allocation failure and
SIGABRT while compiling `infer`. Elapsed 20.82 seconds; user CPU 5.24 seconds,
system CPU 1.97 seconds; maximum RSS 1,318,788 KiB. The imposed `ulimit -v`
was a **virtual address-space cap**, not a resident-memory cap. LLVM failed
below 2 GiB measured RSS, so this result does not establish that compilation
requires more than 2 GiB resident memory. No Rust compiler diagnostic reported
a type error, but the build did not complete and is not successful compile
evidence. No background Cargo/rustc build was observed before launch.

The build emitted 106 warnings; §11's previous build emitted 105. The new
warning concerned fields logged solely through derived Debug. After the
failed build, that single log was repaired to access every field explicitly.
This warning repair is statically inspected and **uncompiled**; no second
build was run. The pre-repair tail hash was
`32cfd6f7f070eb1aabf6dc5cb2a2ade19729f85aa86bec1307b574ba7a71d8a7`.

No capture was executed against the stale existing executable. The authorized
single build budget is consumed; the 120-second inference budget is unused.
Recommended next action: adjudicate an appropriate resident-memory enforcement
method, review the frozen two-file hook, then issue a fresh bounded build and
capture packet. Do not reinterpret the failed build as a missing semantic
route or increase runtime probes before producing the new executable.

### Initial follow-up snapshot and remaining scope

| Dependency/output | Before SHA-256 | Pre-review SHA-256 |
| --- | --- | --- |
| Oracle `crates/infer/src/lowering/expr/tail.rs` | `ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8` | `8820424d75d2cbbc85c849bd289ef05547e38da3596a86201583b366dba344de` |
| Oracle `crates/infer/src/check.rs` | `48b0d354b6e31a7ed3515e2d8c4341badbb6d55e871751decda220b0bd33424f` | `b21682220cd0031c35e6ede4b4edbb4f2d3bc0c84d585e3320d6b4de5531c9dd` |
| Exact int input | `73b4a2d12233b9b658188f3baa17edb04c14a89f94217198befca22db4af77d9` | same |
| Failed-build log | absent | `7ff549ccae1e31cb7589da6f2680077117ef7859014f1a70152509d645128300` |

The five prior instrumented files remain unchanged from the earlier dependency
table. Observed Y3 HEAD moved to `15f427c38b921a34ed099e2c6fb34cfb7f254540`
through primary integration during this packet; its movement does not change
the pinned Oracle/input premise. No Y3 compiler, shared record, question,
manifest or lockfile was edited; no Git mutation was performed.

Unverified follow-up scope: successful build, warning repair compilation,
runtime observation equivalence, actual TLS scope delivery, source event IDs,
selected ancestry, completed output projection and every semantic theorem.
H and complete Call remain OPEN. This checkpoint preserves a failed bounded
attempt and a private observation patch; it supplies no runtime lineage join.

## Independent hook review and batched repair

The primary returned two major and one minor finding for one batched repair:

1. **Major — compact fallback erases failure.** The compact wrapper returns
   `(CompactRoot::default(), Vec::new())` on failure, and its separate diagnostic
   gate need not be enabled with LINEAGE. The observer could print that value
   as a compact result without the actual error.
2. **Major — pre-export collection limits were missing.** The root label
   collection, query-root/selected-parent vectors and accumulated anchors could
   grow before exporter or logging bounds applied.
3. **Minor — TLS cleanup was absent on early check error.** `lower_loaded_files?`
   could return before event state was deactivated and cleared.

Repair within the same two Oracle paths:

- Removed the compact wrapper call entirely and emit `compact_not_observed`
  with `reason=no_fallible_wrapper_in_lease`. Every crate-visible compact
  projection wrapper in `compact/surface.rs` erases Result; the actual
  fallible `CompactCollector` is private to `crate::compact`. No compact
  success, error, value or complete compact traversal is claimed after this
  repair. The direct selected-projection query still preserves its real
  `Result`; errors log `query_error ... fallback=none`, and collection-limit
  exits use `query_incomplete ... fallback=none`. Suppressing the unsafe
  compact observation removes the false-success route; it does **not** supply
  the requested missing fallible compact artifact. If that artifact is required,
  its exact owner is a fallible wrapper in `compact/surface.rs`, outside this
  lease. No duplicated collector or inferred empty root was introduced.
- Cap application events at 8, selected `run` roots at 4, query roots at 12
  and global ancestry anchors at 64, checking before push. Before opening
  each query, check the ordinary plus evidence lower-record count (the exact
  candidate set used by `VarBounds::projection_lower_records`) against 8,
  and reserve worst-case two anchors per candidate against the remaining
  global anchor budget. Check returned selected entries against 8 before
  retained-parent pushes. Cap every anchor append; stop the observer with
  an explicit incomplete marker when a limit is exceeded. Collector failure
  does not stop ordinary inference or silently truncate a successful capture.
- Introduce `ResearchLineageGuard`, returned only under the research gate.
  Its `Drop` deactivates TLS, clears events and resets incompleteness on normal
  return, `lower_loaded_files?` error and unwinding. `finish` borrows the guard
  instead of consuming its cleanup responsibility. A `PhantomData<Rc<()>>`
  makes the guard non-Send/non-Sync, preserving the same-thread requirement.
  Runtime thread/scope delivery is still unverified.

Remaining internal traversal/resource limits are explicit. The instrumented
query bounds its root/candidate/result vectors, but it does not impose a new
step/depth budget on the existing proof evaluator, support enumeration or
proof-cache work for an individual candidate. The label iterator may scan the
existing whole label table before finding matching roots. Endpoint shape
cloning, debug traversal of retained shapes and cloning source-path strings
use existing source structure; output byte caps are not a bound on all work
performed before formatting returns. Existing portable explanation/export
budgets apply to ancestry, but this packet does not prove an end-to-end process
time or memory bound from those limits. The process budgets remain the outer
enforcement mechanism. No extra compact traversal occurs in the repaired hook.

No build, run or test was performed for this repair. Static direct-owner reads,
scope/diff inspection, dependency hashes and scoped `git diff --check` were
the only checks. The prior build budget remains consumed; compilation and
warning status of the repaired code are unverified. Fresh independent
re-review is required before promoting repair status or executing the hook.

Repaired Oracle hashes:

| Path | Frozen SHA-256 |
| --- | --- |
| `crates/infer/src/lowering/expr/tail.rs` | `8e9aa1550addedaa910cbf2be2e388db4d3c1453ab269d4db9013824354c90e1` |
| `crates/infer/src/check.rs` | `f65c78283befa3164b1e314a43ac6cd2a964dd9acb0fc88ddb86644953d819f6` |

## Independent repair review

A fresh `compiler_referee` review found no major or minor findings in the
frozen repair. It confirmed that `compact_not_observed` closes the false-success
route without supplying compact-output evidence; the fallible compact owner
remains outside the lease. It checked the stated collection caps precede the
relevant pushes and that the TLS guard clears state on normal return, error and
unwinding while remaining on the same thread. The review did not compile or run
the patch and did not inspect the whole artifact. Per-candidate proof/cache
work and shape/path payload sizes remain outside the collection bounds, as
recorded above.

The exact reviewed Oracle hashes are the repaired hashes above. At the time of
this review, a fresh build and capture were still pending; that state is
superseded by the successful bounded run below. Runtime observation
equivalence, actual source/output membership, H and complete Call remain OPEN.

## Successful bounded build and capture

After the failed virtual-address-cap attempt, one fresh serial offline locked
build was run with a process-tree resident-memory monitor and a 6 GiB RSS cap.
It completed successfully in 37.12 seconds; peak process-group RSS was
1,549,127,680 bytes. The compiler emitted 105 warnings. This compiles the
repaired private observer at the frozen Oracle HEAD; it does not verify default
environment observational equivalence or Yulang3 behavior.

One execution of the existing int-variant input then completed successfully in
0.51 seconds under a 2 GiB RSS cap, with peak RSS 36,208,640 bytes. The input
hash remains `73b4a2d12233b9b658188f3baa17edb04c14a89f94217198befca22db4af77d9`.
The log hash is
`0abfbda6f1f1c2eb6ba933571c2a0372d391017795aceaf3649d067098418e8c`.
There was one completed check, four application events, five successful
selected-projection queries at `ConstraintEpoch(313)`, zero query errors and
zero incomplete-query markers. Each compact observation is explicitly
`compact_not_observed`; no compact scheme result or final membership is
claimed. The ancestry export completed for its selected anchors, but the
4096-byte `ancestry_roots` log line is truncated. Therefore the export's
selected-root completeness does not imply a complete textual root-to-anchor
mapping in the log.

The two structurally relevant application events are `ExprId(14)` and
`ExprId(15)`: the latter consumes the former's Value/Effect and is its source
parent. Their captured result Effects are `TypeVar(48)` and `TypeVar(51)`;
both were queried successfully. This remains a completed-query observation,
not proof that either application is the concrete line-64 send or that its
contribution survives the output scheme.

An independent read-only source-coordinate audit found that the loaded input
is 2,588 bytes and ends with `run: ev::send (1, 42)\n`, whose physical range is
`2566..2588` (the nested send application begins at `2571`). The captured
`ExprId(15)` and `ExprId(14)` source ranges are respectively `2673..2695` and
`2678..2695`, exactly 107 bytes later. No CLI prefix or file concatenation
accounts for this. The trace converts Rowan CST byte ranges directly; the
missing identity is that rendered CST token bytes equal the collected input
bytes. Yumark doc-comment emission is the first path needing inspection. The
107-byte correction is only a hypothesis, so these event IDs are not yet
authenticated to the exact physical source occurrence.

The next narrow step is an env-gated observation of the already loaded source
and CST root at the same parse, recording their lengths/digests and the final
expression subtree's kinds/text/ranges, then locating the first byte divergence.
Only after that source identity is established can a further owner lease join
the authentic application through actual use/provider/freshening and a named
Function/row event to output `O`. J64, exact contribution membership, H,
complete Call, Yulang3 correspondence, soundness, principality and F5
replacement remain OPEN. The independent hook review found no remaining major
or minor findings; it did not review the source-coordinate seam or close H.
