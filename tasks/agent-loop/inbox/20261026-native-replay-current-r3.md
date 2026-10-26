# Native Replay current-disposition construction r3 — frozen handoff

Status: **WRITES STOPPED** after the freeze receipt described below.
Producer: `/root/native_current_r3`, inherited generic bounded proof leaf;
no registered-role runtime claim, no children, no independent self-review.
Baseline: `60e8684224a8a911a5627b845312750a192be777`, branch `yulang3`.
Scope: `MERGE-EXPANSION-COVER-1` recursive current-disposition construction;
original `SourceProblem.InferenceSoundness` and `NativeCorrespondence` unchanged.

## Deliverable and exact scope

The kernel-checked advance is a finite **current** graph for the Effect operand
and retained-bound part of the original gate. It derives its invariant from an
empty state and explicit local events; Replay generation automatically registers
children, and both skips now lead to all finite depths of that same graph.
Every merge transports exact bound carriers and original-parent paths while
retaining child edges, active back-references and earlier queued work.

The module does **not** prove accepted native return or full Context/Value
coverage. `CurrentAt` explicitly permits retained/queued/active frontiers.
`ClosedAt` removes those three alternatives but still permits concrete retained
row fibers; it is not semantic subtyping or a constructed source witness.
The graph's `returned` marker preserves an already installed body and is not
an acknowledgement certificate. No dependency, discharge or admission memo is
read as completion.

Written repository paths (only these leases):

- `notes/theory/lean/YulangClosure/NativeReplayCurrent.lean`
- `notes/theory/2026-10-26-native-replay-current-construction.md`
- `tasks/agent-loop/inbox/20261026-native-replay-current-r3.md` (this file)

All scratch work is under
`/workspace/scratch/f98087c7ac1a/native-current-r3/`, including `project/.lake`,
failed source snapshots, scripts, command/exit/resource receipts, logs,
full printed-type/axiom inventory and the freeze record. The project copies
six exact initial inputs; its final module imports only `NativeMergeExpansion`
and transitively `NativeReplayCoverage`. `NativeReplayAcknowledgement` was
consulted; no concurrent proof artifact is a dependency.

## Exact exported results and hypotheses

All names below are under `YulangClosure.NativeReplayCurrent`.

| Declaration | Exact input / conclusion |
| --- | --- |
| `reachable_accounted` | From `Reachable tables keyOf s`, constructed from empty by `Step`, derive generator origins, current graph invariant and membership of every historical child root. No invariant/coverage hypothesis is supplied. |
| `historical_child_current` | From that reachable trace and actual `getElem?` equations for an operation batch and child position, derive `∀ depth, CurrentAt tables s.graph depth (keyOf pair)`. |
| `dependency_skip_current`, `old_old_current` | From that trace and exact dependency or old/old product membership, derive the same all-depth current result. The first theorem also proves the ordinary dependency skip. |
| `fired_product_current` | From that trace, incoming/ordinary mode and membership in the current physical fiber product, derive all-depth currentness after the exact Replay step and automatic registration. |
| `merge_invariant`, `bound_current_merge` | The raw local premise is representative absorption `∀ r, qNew(qOld r)=qNew r`, with actual copy-input list/target/parent index/post-check table. Derive transport of all locally expanded/returned bodies, carrier membership, exact endpoint keys, unchanged sources/transformer and original-parent paths. No assumed child-transport law. |
| `concrete_operand_children` | Reachable state, active registered parent, representative idempotence, raw closed-weight/prefix-ID tables and the computed local operand output. Compute complete child keys and a valid step; prove child-local Context, inherited sources/transformer, reachable next state and all-depth parent currentness. No child-currentness hypothesis. |
| `row_residual_step` | Reachable state, active registered row-lower key, exact current pair, unequal endpoints, levels and actual residual Context ID. Compute the level-selected bound and construct its `Step.bound` and graph invariant. |
| `historical_child_closed` | Same trace and indexed child plus **explicit** `unfinished s.graph = []`; derive all finite `ClosedAt` depths. Native success has not been shown to imply that premise. |
| `missing_depth_has_frontier`, `historical_child_closed_or_frontier` | A failed finite closed depth has an installed-child-edge walk to a member of the computed unfinished list, of length strictly less than the depth. The public root yields closed-or-exact-frontier without assuming either. |
| `walk_merge`, `merge_queued`, `register_active_backreference` | Retain arbitrary finite walks, queued states and active owners across the indicated actual graph operations. No acyclicity or terminalization of cycles. |
| `localReturn_transport` | Transport a computed local Effect return or reflexive pair with transformer zero under representative absorption. Nonidentity scoped reflexivity is not admitted by this branch. |

Full printed types and every theorem's transitive axiom list, including all
private/generated constants, are in `theorem-inventory.json` and
`check11-origin-census.log`. There are 38 explicit source theorem statements;
the full audit includes 143 originating theorem constants among 333 declarations.

## Source constructors and consumers

The full mapping is in the construction note §6. Critical frozen owners:

- `candidate_context.rs:3992–4076`: linked Replay heads, both product quadrants,
  whole dependency suppression and successful operation creation.
- `lib.rs:15214–15250`, `candidate_effect.rs:513–519`,
  `candidate_context.rs:3025–3036,3361–3372,3456–3482`: exact operand enqueue,
  relation interning, child-local Context and inherited scoped payload.
- `candidate_effect.rs:1237–1305`: every Support member, Support tail,
  Contribution/AnnotationMember Allowance check and Allowance tail, local
  success, conflict and unavailable alternatives.
- `candidate_extrusion.rs:1147–1180`,
  `candidate_context.rs:3807–3811,3898–3936`: guarded reflexive return,
  selected residual storage and the exact retained bound constructor.
- `candidate_intrusion.rs:568–708`,
  `candidate_context.rs:4230–4254,4318–4331`: actual settlement, copy inputs,
  forest change and frozen-prefix canonicalization.
- `lib.rs:14288–14420,14881–14947`,
  `candidate_context.rs:2369–2462`: active/partial dispatch, diagnostics,
  ordered acknowledgements and actual ReturnReady. These remain source
  authentication/terminal consumers, not conclusions from the graph label.

Original roots/authority were read from `Contracts.lean`, the 2026-10-13
source-preservation statement §§1,3,5, the 2026-10-24 birth-level correction,
whole-proof closure and current replay/merge notes. This packet does not use a
new source legality, qualifier, semantic axiom, LocalLaws instance or runtime
metadata design.

## Exact remaining parent premise

`MERGE-EXPANSION-COVER-1` remains OPEN. Apply the existing historical child
origin directly to `historical_child_current` after authenticating the graph
projection. The old recursive operand-subgraph obligation is discharged there;
the remaining source application needs:

1. A constructor for the **entire actual nonidentity Context factorization**,
   linking every installed check and the exact residual/consumed branch to the
   same parent graph. One valid retained fiber is insufficient. Reuse the
   previous filter/carrier/path results, actual parser output and successful
   callbacks; do not assume universal Context equality.
2. All actual indexed Value constructors/ports and remaining source record
   adaptation. They remain in the original supported domain.
3. One committed native event erasure sharing heads, raw keys, all maps, queue,
   frames, representatives, post-check contexts and cancellation history.
   Associate distinct Replay births/indices and duplicate admissions with
   graph owners; use only actual merge cuts.
4. At accepted return, eliminate the concrete unfinished-owner path witnesses
   through that **same** execution and ordered diagnostics/ack/ReturnReady
   events, then supply semantic retained-row/fiber closure and the original
   source-scoped soundness connection.

The exhibited walk is a falsifier for an asserted closed graph projection,
not a source-qualified compiler counterexample. No impossibility, compiler
bug, original parent closure, semantic approval or production promotion is
claimed. No assumption that all native `completed` entries mean returned
children is used. Cancellations must erase this ghost graph at the same
checkpoint as native state; this module has no rollback constructor and does
not depend on the concurrent execution-history lane.

## Actual validation and resource receipts

Fixed installed Lake:
`/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake`.
Observed Lake `5.0.0-src+eb6cafb (Lean version 4.35.0)` and Lean `4.35.0`, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Official release digest was verified
by the primary, not re-fetched here; executable hashes are in the manifest.

Every focused call ran the bundled checker with:

```text
python3 .agents/skills/yulang-lean-proofs/scripts/check_lean.py
  --project /workspace/scratch/f98087c7ac1a/native-current-r3/project
  --lake /workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake
  --module YulangClosure.NativeReplayCurrent
  --theorem <explicit roots recorded in each receipt> --timeout 120
```

Its actual commands include `lake --version`, `lake --no-cache env lean
--version`, `lake --no-cache build +YulangClosure.NativeReplayCurrent`, and
`lake --no-cache env lean -j1 -M1024` for printed-type/axiom queries.
Final calls additionally execute the full originating-module census:

```text
lake --no-cache env lean -j1 -M1024 AuditNativeReplayCurrent.lean
```

Independent `.lake`; `LEAN_NUM_THREADS=1`; no memory/thread limit increase.
Eleven calls used of fourteen. Every call has a JSON command/exit/elapsed
receipt and retained log. Final call 11: all exits 0, 3.1548 seconds overall;
child user/system CPU 2.4769/0.6409 seconds; observed child maximum RSS
1,000,944 KiB. Earlier per-call peak memory was not measured. No whole-project
build, native/Cargo probe, network request, installation or Git operation ran.

Failures are retained: call 01 sandboxed Lake installation-configuration
recognition; calls 02–05 elaboration/induction/list annotations/constructor
patterns; call 07 missing explicit `keyOf`; call 09 reserved binder `local`.
Calls 06 and 08 accepted coherent earlier stages. Calls 10 and 11 accept the
final bytes and full audit. Failed source snapshots `source01.lean` through
`source11.lean` remain available. The initial tool invocation with a nonexistent
scratch cwd failed before launching any command; no proof result is attributed
to that attempt.

Full axiom census:

| Complete axiom set | Count |
| --- | ---: |
| None | 72 |
| `propext` | 35 |
| `propext`, `Quot.sound` | 34 |
| `propext`, `Classical.choice`, `Quot.sound` | 2 |

The two classical declarations are `missing_depth_has_frontier` and
`historical_child_closed_or_frontier`. All other principal graph roots use
`propext, Quot.sound`. No nonstandard axiom, proof hole, project axiom,
native-evaluation assumption or kernel bypass occurs. This is self-checking
of construction, not independent review or source correspondence.

A reported repository `scripts/__pycache__/check_lean.cpython-312.pyc` is not
attributed to this leaf: all checker invocations executed the file as a script,
never imported it, and drivers imported standard-library modules only. Its
provenance remains unknown here. No removal was attempted; primary owns the
artifact and any exact cleanup. Remaining Python commands set
`PYTHONDONTWRITEBYTECODE=1`.

## Frozen hashes

All hashes are SHA-256. The manifest contains every one of the 29 frozen
source/governing/configuration input hashes and all 53 scratch artifact hashes.
Its input recheck matched all frozen hashes. The freeze receipt also records
this handoff's hash after writing, avoiding a self-referential checksum.

| Object | SHA-256 |
| --- | --- |
| `NativeReplayCurrent.lean` | `fdd7dfa32f944f09b2cfc7440caeff95edcfad1fd5c839094f186d27168d9088` |
| Construction note | `ed7a97033d68822ac705bce26064ec590c07934df0c23d6a6761368bc1f6854a` |
| `manifest.json` | `7f75eef59d099db94b84b23a16d67c408825709649ce3ed10f314ac049f2d3df` |
| `check11-full-audit.log` | `a178c1111f62c4c46c1783426a3aece14e652207980b48c7cd13184e2962dda6` |
| `check11-origin-census.log` | `3c5c16b37c445a96a1668c0ed18123b8593e70819121d2223f5d63e58f603a28` |
| `theorem-inventory.json` | `36481e684ddefb232b3af751263529e87c811cafc8c515aa30a33aefbb8f053f` |
| `AuditNativeReplayCurrent.lean` | `326c80b1a8fb2326ce68c185cd4c2bcb383060b287633839c5d24ca213b2af6d` |
| `source-audit.txt` | `7af0a86c4d5042469be05a7645b2058ea51df97146d3bb918c864a07956e34ac` |

The fresh independent reviewer should check the original-parent boundary,
all represented source cases, the explicit guards and unproved authentication,
all child-key/payload equations, graph sharing versus occurrence acknowledgement,
repeated-merge carrier updates, and the finite-depth falsifier. Do not replace
that review with the audit count. Primary owns imports, review assignment,
status/audit records, staging, commits and pushes.

**WRITES STOPPED.** No background process or child remains. Final freeze receipt:
`/workspace/scratch/f98087c7ac1a/native-current-r3/freeze.json`.
