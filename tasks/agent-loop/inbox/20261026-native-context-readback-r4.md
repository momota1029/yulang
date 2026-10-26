# CONTEXT-COMMITTED-READBACK — constructive joint-history handoff

Producer: `/root/context_expansion_r4`, bounded generic proof leaf, inherited
model. Baseline supplied by the primary:
`820ed79a8891e72c85280a5e0313e57fb05f3b73`.

Status: constructive source-mapped forward/journal supplier, kernel checked;
**fresh independent review required**. Original full-context/native committed
application and original complete inference soundness remain OPEN. The first
new concrete native supplier is **TABLES-LIFETIME-READBACK**. No semantic scope
or source language was changed. No review or parent closure is self-certified.

## 1. Leased outputs and frozen dependencies

Repository writes are exactly:

- `notes/theory/lean/YulangClosure/NativeContextReadback.lean`
- `notes/theory/2026-10-26-native-context-readback.md`
- this handoff

The Lean module imports frozen `NativeContextExpansion`, `NativeDrainOwnership`,
and `NativeExecutionHistory`; their transitive local dependencies were copied
once into an isolated task-owned project. No old module, root import, shared
status/audit/configuration, Rust, expected output, dependency, Git state, or
sibling file was edited. No children were started.

All scratch/cache/source snapshots/checker programs and receipts are under:
`/workspace/scratch/f98087c7ac1a/context-readback-r4/`.

The final Lean SHA-256 is
`321d087c8d2df5099f67beb75e4316d44114806bbfae2aa64ebda22a34bd83f2`.
`inputs.json` binds the exact 14 input hashes, including all source-owner Rust
files, frozen Lean dependencies, and project/toolchain descriptors. The final
audit independently rechecked those owned frozen copies before execution.
`manifest.json` and `freeze.json` bind the final output, checker, census,
resource-receipt and build-artifact hashes. They are written after this handoff
to avoid a self-hash cycle.

## 2. Actual construction and parent application

The unchanged parent requires original complete Context decomposition and
native readback with the same full source/scoped witness, rather than an
extensional `ClosedAt`/`InstalledAt` assertion. The immediate missing case was
an original queued relation whose canonical processing relation changes after
merge, plus native discharge/memo publication before Dispatch completes.

The new shared `State` contains the immutable-occurrence drain projection,
actual complete relation/task interpretations, representative maps/generation,
computed original-to-processing routes and Derived edges, checked/published/
ready Context stages, actual discharge prefixes and post Contexts, active
residual owners, typed-pair memo, body seals and processed-occurrence receipts.

`prepare` executes the frozen parser and all ordered checks. `publish` records
the prefix before the separate successful sampling step. `admit` records the
native memo while the occurrence is still active. `finishPrefix` computes the
consumed or residual branch before sealing. A duplicate retains its actual
memo owner pointer; it never supplies a completed-body callback. The finite
control invariant proves that owner is live or sealed and eliminates the live
case at a true no-current cut.

The exact direct application to the old local construction is
`YulangClosure.NativeContextReadback.fresh_body_is_frozen_built`.
Its premises are the actual `prepare = some prefix`, `finishPrefix = some body`
computations with the same callback/representative snapshot, and publication
success. It concludes `NativeContextExpansion.Built t q key body` by
`staged_expand`. Cached bodies instead retain their old computed prefix and
later residual in construction-directed `PrefixRecipe`/`BodyRecipe`; no
semantic coverage or memo-completion assumption is added.

Main fully qualified roots (all prefixed
`YulangClosure.NativeContextReadback.`):

| Root | Exact application |
| --- | --- |
| `staged_decompose`, `staged_expand` | Factor the existing computation at the actual early-publication boundary. |
| `memo_has_actual_owner`, `owned_body_at_cut` | Derive active-or-sealed ownership and seal existence at a no-current cut from the shared run. |
| `actual_discharged_prefix`, `cached_parser_readback` | Derive fresh nonempty prefix origin and repeat-parse equality without a fixed fuel restriction. |
| `quiescent_original_context_readback` | From one initial run and empty queue/stack, read back every issued occurrence to its actual receipt, body recipe, old checks and Derived route. |
| `effect_receipt_original_body` | Join original queued owner, full source/transformer payload, actual Derived edge, all original published checks, and the sealed canonical processing owner. |
| `resolved_body_whole_child_provenance` | Every check/residual child keeps child-local Context, complete sources/transformer and nonzero-self admission guard. |
| `settlement_owner_readback` | At an actual top empty/current-none cut, return a seal or the exact active outer synchronous frame; no pending-coverage fallback. |
| `merge_session_has_actual_cut` | Preserve the actual entered settlement frame while allowing work queued by an earlier merge inside that loop. |
| `quiescent_replay_readback` | Obtain Context readback and diagnosed Replay ticket receipts from the same control projection. |
| `committed_readback`, `committed_quiescent_context` | Derive the surviving shared run and Context readback from the joint journal's concrete commit/cancel history. |
| `cancelled_attempt_restores_joint_state`, `cancelled_attempt_birth_not_reused` | Restore Context/control/memo/owner/seal together and retain a fresh attempt birth after cancellation. |
| `Witness.active_memo_run`, `Witness.active_memo_is_not_completed` | Concrete initial execution ending with a live nonzero-transformer/source-bearing memo owner and no seal. |
| `LifetimeBoundary.two_successful_parses`, `LifetimeBoundary.no_single_raw_table` | Checked obstruction to one unversioned Context lookup across raw-ID reuse. |

`named-roots.json` lists all 78 named roots. Every root and every originating
generated/private declaration has its complete actual type and transitive
axiom list in the census; this table is only navigation.

## 3. Native ownership and exact horizons

The source map and complete next-owner inventory are in the accompanying note.
The decisive original native cuts are:

- `candidate_context.rs:3767–3785`: Transport computes canonical relation,
  post-check Context and whole source/scoped payload, then records Derived.
- `candidate_context.rs:3839–3885`: already-discharged lookup; all filter
  callbacks; reserve/publish; sampling before returning to Dispatch.
- `candidate_intrusion.rs:423–455` and `lib.rs:13507–13518,14443–14456`:
  `completed[processing]` is written during pair admission **before** the
  residual. A duplicate can therefore refer to an active owner.
- `lib.rs:14344–14420`: actual clearing Dispatch/structured continuation cut,
  diagnostics and acknowledgements.
- `candidate_intrusion.rs:568–599`: settlement enters with the worklist empty,
  then can queue work before later merges of the same loop.

A top-frame settlement cut does not imply an empty outer synchronous stack.
The exact theorem retains that live outer owner. Completed bodies are derived
at true no-current or empty-stack cuts. Diagnostic completion is not absence of
conflicts. Effect recipes can contain retained fibers and conflict leaves.

The new state records merge representative updates and the settlement owner;
it does not reconstruct all physical bound vectors or establish semantic
current-carrier validity of every historically sealed raw leaf. The accepted
`NativeContextExpansion.mergeGraph`/`Body.transport` results must be applied to
the same actual `candidate_context_canonicalize_bounds` history. This remains
native carrier/Effect semantic interpretation, not an inference from empty
queues. Value Context forwards the whole request; complete structured Value
dispatch and source semantics remain with their concrete owners.

All completion receipts in this model are ghost records derived from actual
history cuts. They are not a required native `source_drain_completions` lookup:
`candidate_context.rs:2177–2184` allows that observation vector's reservation
to fail without failing inference. No implication from native `Ok` to presence
of that optional stored evidence is used.

The frozen local callback interface still supplies actual success flags. The
native event erasure must identify each child enqueue with its issued `Work`
and exact Replay transfer at `candidate_context_admit`,
`candidate_check_effect_operand`, and `enqueue_item`. The theorem covers every
actually issued occurrence and preserves every constructed child key; it does
not manufacture occurrence issuance from a Boolean. This is an exact emitter
connection for the common source projection, not an assumed completed body.

## 4. First actionable residual: TABLES-LIFETIME-READBACK

The joint journal is an exact proof projection of the **represented fields**.
Its generic cancellation theorem is not a proof that native Context/weight/
view/contribution/prefix-interner tables erase to one fixed `Tables t`.
The current packet makes no such claim.

Minimum native constructor/rollback owners:

1. All six `ContextExpr` constructors through `State::context`
   (`candidate_context.rs:2630–2655`), child-ID assertions, fresh renaming
   (1556–1689), and Context/key truncation on rollback (2141ff).
2. `source_weight` (2734–2758), exact allowed list/boundary/owner/position and
   attachment, with weight rollback and payload/view validation (1729ff).
3. `candidate_signature_view` (`candidate_effect.rs:859–909`), copy/remap
   (1155–1197), and checkpoint/rollback (313–389). The View ID is selected
   before weight construction, while the View is pushed afterwards; the
   intermediate weight cannot be assumed already validated against a View.
4. `candidate_effect_contribution` (1213–1236), effect/origin/instance and
   post-allocation sampling, together with contribution rollback.
5. Actual `candidate_context_source` interner results (3361–3372), including
   the nonzero PrefixLeft(weight,Identity) return ID; this is not an immutable
   independent total `prefixIdentity` array.
6. Complete relation/source/scope identities and their constructor/rollback
   references (`relation_with_scoped` 3062ff; source/relations 2145–2160),
   coupled to the common route checkpoint/commit/cancel owners
   (`lib.rs:9271ff,9489ff,9646ff`).

Required statement: a concrete constructor/extension/cancel trace determines
allocation-stamped handles or the exact observation footprint. Every still-live
observed handle reads back the same allocation birth and full payload at the
later callback cut; new allocated slots remain permitted. Meaningful `None`
observations belong to their observation version and cannot be silently
changed to a later `Some`. A cancelled raw slot reused with a new constructor
must receive a different logical lifetime. Prove actual parser, weight/View,
contribution, child-local-prefix and operand lookup computations transport
along that source-determined trace. Global lookup equality would forbid fresh
allocation and is not an acceptable replacement premise.

The checked boundary example gives raw Context slot 1 two different legal
contents: PrefixLeft(weight 1,Identity), yielding `[1]`/residual 0, and
Swap(Identity), yielding `[]`/residual 1. Native interning accepts both
constructors; rollback removes the former key and truncates the vector. This
refutes an unversioned readback shortcut, not the original soundness claim.

No new packet files, source edits, or versioning implementation were started.
The primary must issue the next exact lease/budget and fresh review assignment.

## 5. Complete checker and axiom receipts

Pinned executable:
`/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake`.
Actual versions: Lake `5.0.0-src+eb6cafb` and Lean `4.35.0`, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, x86_64 Linux Release.

Final audit 13 ran:

```text
lake --version
lake --no-cache env lean --version
lake --no-cache build +YulangClosure.NativeContextReadback
lake --no-cache env lean -j1 -M1024 AuditNativeContextReadback.lean
```

All commands exited zero. The actual complete commands/cwd are in
`check13.log`/`check13.json`; the abbreviated `lake` above denotes the pinned
absolute binary. Every process uses `LEAN_NUM_THREADS=1`, the project's
`-j1 -M1024`, `PYTHONDONTWRITEBYTECODE=1`, and the owned TMPDIR. No package or
toolchain was installed. The isolated build contains only this module and its
frozen imports. The primary retains default-project integration ownership.

Final all-origin census:

| Complete transitive axiom set | Theorem constants | All declarations |
| --- | ---: | ---: |
| none | 48 | 154 |
| `propext` | 18 | 29 |
| `Quot.sound` | 1 | 1 |
| `propext`, `Quot.sound` | 135 | 442 |
| `propext`, `Classical.choice`, `Quot.sound` | 26 | 26 |
| **Total** | **228** | **652** |

This includes **78 named roots**, **13 private declarations**, and **8 private
theorem constants**. No generated declarations are omitted. The census selects
the actual originating module index, rejects originating axioms, prints
complete types with proof/deep-term printing, and calls the transitive axiom
collector for every declaration. The parser rejects type elisions, reconciles
all unique blocks and named roots, and checks the approved standard-axiom set.
There are no proof holes or unchecked native-evaluation assumptions. The text
search's `admit` matches are the native admission event constructor and its
cases; they are not proof-hole tactics.

Evidence files:

- `project/AuditNativeContextReadback.lean`: complete census program.
- `check13-origin-census.log`: all 652 complete type/axiom blocks, 595,763 bytes;
  SHA-256 `acdc8afe9bf86415eb783adf9ce1ff7af0e39c326bf4eeb560381f134d9199c9`.
- `origin-inventory.json`, `census-summary.json`, `named-roots.json`:
  machine-readable complete reconciliation and root inventory.
- `source01.lean` through `source13.lean`, `check01.log` through
  `check13.log`, and corresponding JSON receipts: every material failure and
  successful source/check snapshot.
- `inputs.json`, `manifest.json`, `freeze.json`: exact inputs, outputs and
  final binding hashes.

## 6. Finite budget, failures, and stop condition

Stage began 2026-10-26 11:30:27 UTC; deadline 12:15:27 UTC (2,700 seconds).
Used **13 of 20** focused checks. Each has a 120-second total deadline; no
check exceeded it. Combined recorded checker elapsed time is
**127.127746 seconds**. Final audit 13 took **17.345842 seconds**, with
15.350125 user CPU seconds, 1.920541 system CPU seconds and peak child RSS
**1,013,952 KiB**. Audit 12's peak was 1,015,136 KiB. Lean's per-process heap
bound remained `-M1024`; no budget extension was used.

Retained failures: check01 exposed sandboxed Lake configuration detection;
the authorized native process execution resolved it. Checks02–05 repaired
namespace/reserved-field syntax, Option reduction, Prop elimination and
record-indexed invariant elaboration. Check10 repaired an explicit leaf
membership rewrite. Check11 repaired the concrete witness frame-record
normalization. Checks06–09 and 12–13 passed. Failed logs/source bytes were not
replaced by later successful versions.

All leased repository and scratch writes stop at the recorded `freeze.json`
time. The primary may now assign a fresh nonauthor reviewer to this exact
frozen packet and integrate only after adjudication. Original soundness and
the native version/event/semantic obligations above remain owned and OPEN.
