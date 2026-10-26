# Native Context expansion r4 — frozen producer handoff

Assignment: `native-context-expansion-r4`, handoff revision **1**.
Worker/sole author: `/root/context_expansion_r4`; primary: `/root`.
Role: generic supported proof leaf applying `.codex/agents/lean-prover.toml`
and `yulang-lean-proofs`, inherited model; effective runtime model/effort are
not independently exposed and are recorded as UNKNOWN. No descendants.
Baseline supplied by the primary: `37ec9da2aaca2d7b806887d06d9bbd8b0fc5439c`,
`yulang3`. No Git operation was performed.

The governing contract is the primary's live task packet. No separate tracked
sprint contract was supplied. Its constraints are retained in
`context-expansion-r4/packet.json`, SHA-256
`dfade7e583b5bb96e5e61345da8d93e04ff920af284a54c714441a7038f99507`.
No stale scheduling row was used to expand authority or reclaim a writer.

## Outcome and original scope

Outcome class: **kernel-checked constructive proof component**, source/native
readback still OPEN; independent review pending. This is a coherent research
checkpoint, not parent closure or production authority.

The original parent is `SourceProblem.InferenceSoundness` in
`notes/theory/lean/YulangClosure/Contracts.lean:127–130`, with the same supported
source domain, original lexical/event scopes and one shared source witness.
The immediate target is the full Context outgoing-clause portion of
`MERGE-EXPANSION-COVER-1` in Replay lifecycle section 6. Complete Call, effects,
Value and record cases, optional records, method selection, generalization,
the birth-level occurrence rule and native accepted-return correspondence
are preserved. No supported-source case is removed.

The former full Context graph premise is replaced by an executable parser and
complete callback/residual construction. The new graph installs that computed
body and consumes its exact child list. It cannot recover a convenient body
from the old extensional `ClosedAt`. It derives the original historical Replay
root, both skips and the full ordinary/incoming product against that installed
body graph.

**Original whole `MERGE-EXPANSION-COVER-1` and inference soundness remain OPEN.**
The unfinished native task is now the concrete committed frame/readback seam
in section 4 below, especially the prior-body owner of an already-discharged
relation and the interval between Context publication and Dispatch completion.
No source-qualified refutation or compiler defect is claimed.

## Exact leased outputs and frozen bytes

| Repository artifact | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/NativeContextExpansion.lean` | `9887bef34e51678cead77eaf84a2f9b47916987ea9cffaad5d4ef74d53de2ea8` |
| `notes/theory/2026-10-26-native-context-expansion-construction.md` | `0bddd394a8dc7d686b1708ef099808c8b24c1e217242eaa7d0df5c1f6e9bed95` |
| This handoff | Recorded without self-reference in `freeze.json`. |

No root import, existing proof/audit module, shared status/lease file,
configuration, native code, test expectation or sibling artifact was edited.
All generated/cache/snapshot files are exclusively under
`/workspace/scratch/f98087c7ac1a/context-expansion-r4`.

`inputs.json` records 31 exact governing, native, project and proof input
digests; SHA-256
`4c8d3c91f14c9f849f9565094bb25fccfc91ce0fc0284a39b7a2ef26ce9b6bd3`.
All were rechecked and copied to `inputs/`. The isolated import cone is
`NativeReplayCoverage` → `NativeMergeExpansion` → `NativeReplayCurrent` →
`NativeContextExpansion`; no changing sibling proof is an input. The final
module bytes equal `source16.lean` and the isolated project's checked module.

## 1. Constructed source cases and public roots

All names are under `YulangClosure.NativeContextExpansion`.

| Owner / roots | Constructed result |
| --- | --- |
| `scanStep`, `scan_run_computes`, `scan_computes_run`, `parsed_no_mixed`, `finish_pure_replay` | All six native Context constructors; identity; all three modes; decreasing IDs; exact weight/view validation; visited-mode and filter deduplication; lower-before-upper Replay; mixed/directed/pure residual distinctions. Fuel is the finite native scan length, not a new source limit. |
| `decompose_exact`, `every_filter_executed`, `empty_filters_keep_stored` | Complete ordered callback list, exact count, post-check Context, consumed iff no continuation, exact residual dispatch and publication guard. Empty-filter parsing does not overwrite stored Context. |
| `registered_filter_constructed`, `apply_bound_exact`, `placed_bound_pair` | Already-registered origin/replay branch distinct from physical insertion; exact identity check fibers and level-selected residual placement, including rigid-lower/row-upper. |
| `admit_payload`, `apply_children_admitted`, `whole_child_payload`, `full_body_child_payload` | Every actual emitted child, exact child-local Context/interner node, sources, transformer, canonical self-relation rejection and enqueue-success guard. All Support members, Support tail and Allowance tail remain present. |
| `value_context_exact`, `filtered_value_rejected`, `effect_demand_rejected` | Exact no-filter Value forwarding with arbitrary complete native endpoint data; whole optional demand preserved; filtered Value, nonzero Value transformer and Effect demand rejected. Value dispatch is not declared complete. |
| `body_factorization_transport`, `body_fibers_transport`, `held_merge`, `merge_invariant`, `identity_post_context` | Every installed check and residual transported; ordered weight/view/registered metadata and child lists preserved; carrier membership and original-parent paths; post-check map computed from body publications. |
| `construct_full_context`, `reachable_invariant`, `installed_all_depths` | Computed full body installed at the registered active owner; all child/fiber registrations and paths; retained/queued/active owner phases and erased return markers remain separate. |
| `historical_full_context`, `dependency_skip_full_context`, `old_old_full_context`, `full_product_context` | Original historical Replay member and both actual skips reach the same complete installed-body graph after concrete generator events and repeated merges. |

The module includes **50 named theorem roots**. `named-roots.json` lists all
50, and the complete inventory contains every full type and transitive axiom
set, including all private/generated declarations.

The main local theorem retains only the operational guards:

```text
Reachable t g;
key is registered and its expansion owner is active;
expand t availability levels g.core.q fuel key = some body
  -> install that body, with every child/fiber/path,
     and InstalledAt at every finite depth.
```

The historical theorem is:

```text
ReplayReachable t keyOf s;
s.replay.operations[operation]? = some batch;
batch[index]? = some pair
  -> forall depth, InstalledAt t s.graph depth (keyOf pair).
```

`ReplayReachable` is constructed from the exact generator, local parser/
callback computations, queue/activation/reuse/return and merge operations.
Neither root takes complete Context coverage, recursive child closure,
semantic truth, `LocalLaws`, or a completed-memo interpretation.

## 2. Interpretation boundaries that consumers must preserve

`InstalledAt` matches the stored body and therefore retains its actual full
factorization; it still admits explicit pending owners. Fibers remain row
obligations. Successful mismatch callbacks are retained as conflict leaves.
An installed body or return marker is not a successful-diagnostics certificate,
native acknowledgement or semantic solution. A new physical Replay occurrence
of the same key does not acquire an old acknowledgement.

The raw `Availability` fields are success projections for entry, parser,
admission/enqueue, origin, physical insertion/readback, Replay, mismatch
recording and publication. Its registered field reads the actual physical
Allowance presence. These must be erased from the same execution; arbitrary
true flags are not native execution evidence.

The new graph records publication after its successful Context/Dispatch
macro-step. Native publication occurs after all Context callbacks but before
residual Dispatch. That interval is deliberately not hidden behind a claimed
native trace theorem. Pending/failing dispatches and rollback must be handled
by the common execution readback before using the graph at native terminal cuts.

`nonzero_self_child_rejected` is a checked obstruction to dropping the child
admission guard. `empty_filters_keep_stored` refutes substituting every parsed
residual for stored Context. Neither is a source-qualified counterexample to
the original whole-language target.

## 3. Verification and complete census

All sixteen checks used the provisioned native Lake at
`/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake` and the
isolated project. Actual versions: Lake `5.0.0-src+eb6cafb (Lean version
4.35.0)`; Lean `4.35.0`, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. No dependency/toolchain install.
Every Lean process used one thread and `-M1024`; each complete focused call
had a 120-second deadline. `PYTHONDONTWRITEBYTECODE=1` and owned `TMPDIR` were
set. The initial sandboxed Lake detection failure is preserved; later checks
used the permitted process environment without changing the toolchain.

Call exits 01–16:
`1,1,1,1,1,1,1,1,0,0,1,0,0,1,0,0`.
All main-source snapshots and full logs are retained. Call 14's failed audit
source and calls 15/16's audit sources are separately retained. Call 15 is
kernel-successful but did not meet the unabridged generated-type requirement;
call 16 is the final complete audit. The default pretty-printer omission was
detected by inventory validation, not ignored.

Final census:

| Complete transitive axioms | Theorem constants | All declarations |
| --- | ---: | ---: |
| None | 196 | 632 |
| `propext` | 51 | 102 |
| `propext`, `Quot.sound` | 49 | 121 |
| Total | **296** | **855** |

All **50 named roots** occur in the 296 theorem constants. There are 16 private
declarations, including 12 private theorem constants. The other theorem
constants include generated eliminator/equality/matcher helpers. Every one of
the 855 declarations has a complete unabridged type and axiom record. No
`sorryAx`, project axiom, `Classical.choice`, native-evaluation assumption or
checker bypass occurs. The source search's nine `admit` matches are the
operational admission function and its consumers, not proof tactics.

| Evidence | SHA-256 |
| --- | --- |
| `declaration-inventory.json` | `2365c9cc4ad8ebc0ba23d4ebc5cf3221dd138112cb0e612866b69070e0c22815` |
| `census-summary.json` | `82a3ed982a16aa4e8c70fc03d660aa3f2218db5b93df7d6e78b0f99e2c1760f4` |
| `check16-origin-census.log` | `4beca862c3ff1945d2c37cec011b82424251e2c944d91b7ec28b46fe8ed78277` |
| `check16.json` | `a08f4570879f84142e7cf35123286f04497afe7fc173607e90f42f612ad948cf` |
| `project/AuditNativeContextExpansion.lean` | `1681ed990e951322b5305fb06e448b907d6d2cc7afb8052ecb77241db72a334b` |

Measured checker wall time sums to **66.622 seconds** across 16 calls; four
calls remain unspent from the 20-call bound. Final call: 2.249 seconds wall,
1.961 user + 0.232 system child CPU, 1,006,124 KiB observed child maximum RSS.
The initial reading interval predates the first scratch timestamp and is not
misrepresented as a measured full-stage duration. The 2700-second stage was
not extended. No full default build, native test, benchmark or external
installation was run; integration/default import verification belongs to the
primary. There is no remaining checker process.

## 4. Parent application and exact next owners

1. **CONTEXT-COMMITTED-READBACK** — common native history/frame owner:
   `lib.rs:14288–14420`, `candidate_context.rs:3799–3888,3456–3482`.
   Construct one readback of processing relation, canonical key, parser
   iterations, callback success and completed Effect Dispatch. For
   `discharged.contains` and current-generation duplicate suppression, locate
   the prior same full-key installed body or retain the active owner. Account
   for Context publication before Dispatch, partial callback failure and
   common transaction erasure. This is the first concrete missing application
   premise. A discharged/current bit alone is insufficient.
2. **REPLAY/MERGE-READBACK** — same history owner:
   authenticate fixed physical input pairs and complete `keyOf`, actual stored
   contexts/source union/transformer order, queue/operation occurrence births,
   copy prefix and representative absorption. Match `Step.merge` at the actual
   legal settlement cut, including work queued by an earlier merge. Reuse the
   computed complete Context bodies rather than reintroducing their coverage
   as a hypothesis.
3. **VALUE-DISPATCH** — indexed port/record owner:
   consume the unchanged `ValueRequest`, retaining all Function, tuple,
   record, variant and source adaptation cases. The local Value Context result
   is not their child-constructor theorem.
4. **TERMINAL-DIAGNOSTICS/ACK** — drain/ack owner:
   eliminate pending owners and conflict leaves using actual terminal events,
   then associate each physical Replay occurrence with its exact ordered ack
   and ReturnReady. Independent cursor/frame histories do not establish that
   joint projection.
5. **ROW/CONTEXT-SEMANTICS and SOURCE-INFERENCE** — semantic/source owners:
   interpret retained fibers and directed Contexts and supply the original
   shared source-scoped witness. The new graph is operational proof data,
   not a new definition of source typing or inferred safety.

The detailed native case table, source owners and falsifiers are in the paper.
No unchanged generic “prove soundness later” instruction replaces these owners.
The primary owns further allocation, fresh independent review, root imports,
central status synchronization and all commits/pushes.

## Freeze / writer state

Repository outputs are frozen for fresh nonauthor review. The final
`manifest.json`/`freeze.json` record this handoff's hash, every input and
compiled-output hash, resource receipts and scratch artifacts. The producer's
subsequent freeze message confirms **WRITES STOPPED** after generating those
two receipts. No descendant or checker remains. No file lease or review
authority is transferred merely by this producer report.
