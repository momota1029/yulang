# Native Replay current-disposition r3 — independent M3 review

**Verdict: ACCEPT for the frozen, bounded Effect-operand/retained-bound graph construction.**
No BLOCKING or major defect was found in that advertised result. This acceptance
does not close `MERGE-EXPANSION-COVER-1`, native accepted-return correspondence,
or `SourceProblem.InferenceSoundness`. The qualifications below are part of the
accepted scope; in particular, `ClosedAt` is not a native return certificate.

Reviewer: `/root/native_current_review_r3`, fresh nonauthor, no children.
Assignment: independent M3 review of the primary's exact r3 packet; 900-second
wall bound, static review by default, at most two focused Lean calls if needed.
Baseline supplied by the primary: `60e8684224a8a911a5627b845312750a192be777`,
branch `yulang3`. Concurrent integration of the independent execution-history
packet is outside this review and is not a dependency of the reviewed module.
The only repository write is this receipt. No producer file, native code,
import, audit target, shared status, lease record, or Git state was changed.

## 1. Frozen bytes and verification method

I independently recomputed every digest in the producer's manifest/freeze:
29 governing/source/configuration inputs, 53 scratch artifacts, 3 repository
outputs, and 32 compiled outputs: **117 matches, zero mismatches**. The two
installed executable hashes also match the manifest. This checks the reviewed
source against the source snapshots, isolated project, retained compiler
artifacts, logs and inventory; it does not reconstruct a Git baseline from a
new Git operation.

| Object | Verified SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/NativeReplayCurrent.lean` | `fdd7dfa32f944f09b2cfc7440caeff95edcfad1fd5c839094f186d27168d9088` |
| `notes/theory/2026-10-26-native-replay-current-construction.md` | `ed7a97033d68822ac705bce26064ec590c07934df0c23d6a6761368bc1f6854a` |
| `tasks/agent-loop/inbox/20261026-native-replay-current-r3.md` | `508d7cbc9d453ed2c772eb5829431e972688ab31af79a230da94c9a1a278f401` |
| Producer `manifest.json` | `7f75eef59d099db94b84b23a16d67c408825709649ce3ed10f314ac049f2d3df` |
| Producer `freeze.json` | `f9e0bdd085107119cd7269a4a5c2b306e1d611677ed443d2e1b648ebcd5ed24d` |
| Producer `theorem-inventory.json` | `36481e684ddefb232b3af751263529e87c811cafc8c515aa30a33aefbb8f053f` |
| Producer `check11-origin-census.log` | `3c5c16b37c445a96a1668c0ed18123b8593e70819121d2223f5d63e58f603a28` |
| Producer `check11-full-audit.log` | `a178c1111f62c4c46c1783426a3aece14e652207980b48c7cd13184e2962dda6` |
| `NativeReplayCurrent.olean` in the producer's isolated project | `66ee7a64bde9db55ec92b3c98b45bfbbad9520882d5e380464a6e5398a5a6507` |
| Installed `lake` | `8ba83c98f76562d03b8dbc33f1057151ba6cbb121679dde76b2260ccc90495e1` |
| Installed `lean` | `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38` |

Reviewer evidence is
`/workspace/scratch/f98087c7ac1a/native-current-review-r3/static-review-evidence.json`,
SHA-256 `a7b0e1ca278992527e089a77a181ef2cbdbacda44d9d69f213381014b052d023`.
It records the exact file-by-file results, all producer check exits, binary
digests, census reconciliation and final resource receipt.

I read `AGENTS.md`, `AGENTS.pre-sprint.md`, the applicable authority/budget/sprint
rules, the Lean skill and both proof references, the pinned project files,
the r3 source/note/handoff, the relevant prior merge/Replay definitions, and
the cited native constructor/consumer bodies. Original scope was checked
against `Contracts.lean:119–155`, source-preservation §§1,3,5, the immutable
Value-birth-level correction, whole-proof closure §§1,6 and the original
`MERGE-EXPANSION-COVER-1` formulation in Replay lifecycle §6 and the preceding
merge construction §6. The current scheduling file was read, not modified;
the primary's live assignment supplies this review's exact authority and lease.

## 2. What the reviewed proof actually establishes

All new names here are under `YulangClosure.NativeReplayCurrent`.

`initial_accounted`, `step_accounted`, and `reachable_accounted` construct the
three-part invariant from the empty abstract event history: Replay origins,
valid current graph bodies, and registration of every historical batch member.
The public Replay roots take `Reachable tables keyOf s`, not an assumed
`Accounted`, recursive coverage law, completed ledger, solution, or `LocalLaws`.
`Reachable` remains an explicit **abstract event** relation; native execution
has not yet been shown to produce it.

The exact main root is:

```text
Reachable tables keyOf s ->
s.replay.operations[operation]? = some batch ->
batch[index]? = some pair ->
forall depth, CurrentAt tables s.graph depth (keyOf pair).
```

The operation and child equations are actual positions in the erased creation
history. `dependency_skip_current` uses the dependency-origin equivalence;
`old_old_current` uses the old-product invariant; `fired_product_current` runs
the concrete incoming/ordinary Replay step and registers its output. Thus the
two suppressions now reach the current graph rather than stopping at a prior
creation witness. None of these indices is silently promoted to a live
`ReplayOperationId`, creation epoch, or acknowledgement receipt.

The depth induction uses the same `g`, same tables, same status function and
same complete keys at every depth. It chooses the actual installed body in
each `expanded`/`returned` case. Registering children preserves existing active
owners; merge preserves child lists and queued/active status. No acyclicity,
topological rank, or recursive child-currentness premise is supplied.

`bound_current_merge` genuinely constructs the next carrier from the stored
previous carrier. It combines `copy_retains`, frozen-prefix canonical carrier
membership, exact endpoint equations, source/transformer preservation and the
actual added path. The absorption premise is exactly
`forall row, qNew (qOld row) = qNew row`; it is not a hidden assumed transport
law. Repeating the operation starts from the new stored carrier. Context is
the old carrier Context when its physical bound is unchanged and `post` of
that carrier otherwise. No old stored/post-check Context equality is invented.

The children case of `body_current_merge` applies the established complete
operand-outcome transport equation and preserves the full ordered child list.
`walk_merge` preserves arbitrary installed-edge walks, including repeated
visits. These are algebraic preservation results at any permitted abstract
merge cut, not proofs that the native scheduler permits every such cut.

## 3. Branches, cycles and the precise frontier boundary

`CurrentAt` explicitly admits retained, queued and active owners. It is not a
termination or child-completion theorem. `ClosedAt` removes those *alternatives*
and still accepts exact retained fibers as unresolved row obligations.
`historical_child_closed` retains the explicit additional premise
`unfinished s.graph = []`; the proof does not derive it from an empty worklist,
`completed`, `discharged`, operation erasure, `Queued`, or Rust `Ok`.

There is an important interpretation constraint on the definitions:
`CurrentAt` and `ClosedAt` are extensional operand predicates, not predicates
whose successful branch must equal `g.status key`'s installed body. Their
children alternative existentially quantifies a key list with the right
current endpoint projection. Their local-return and bound alternatives can
hold independently of the status label. The proofs reviewed here use the
installed body supplied by `Invariant`, but a later consumer cannot recover
that body or exact child payload provenance from `ClosedAt` alone.

Consequently the finite diagnostic is **one-way**:

```text
Invariant g, root in vertices, not ClosedAt depth root
  -> exists last length,
       length < depth and Walk g root length last
       and last in vertices and Frontier g last.
```

The proof selects a failing member of the actual installed children list and
recurses at the smaller depth. `Walk.step` requires an installed expanded or
returned child body. The final `unfinished` membership is computed from the
actual status and finite vertices. This satisfies the requested concrete
failure-path construction.

The converse is not proved and is false. For example, registering a bottom
operand key without processing it leaves a retained frontier, while the local
operand-return alternative can already establish `ClosedAt` at every positive
depth. A walk to a frontier therefore identifies an outstanding native owner;
by itself it is not a proof of `not ClosedAt`. Likewise finite-depth unfolding
does not prove semantic row satisfaction, native acknowledgements, or inference
termination. I read the note's “falsifier” wording as the stated conditional
failure-path theorem, not as a biconditional decision procedure. This is a
nonblocking integration constraint, not a defect in the proved implication.

The revised local-return definition adds the actual reflexive Effect return
with `transformer = 0`. This is justified by the native equality branch and
the earlier Context/interner rejection of nonidentity scoped self-relations.
It does not establish that the full parent Context ran successfully; that
separate obligation is retained. No generation change or cycle is used to
manufacture an acknowledgement or to replace pending status with `returned`.

## 4. Native mappings and remaining construction inputs

The source descriptions match the inspected owners at the frozen hashes:

- `candidate_context.rs:3992–4076` constructs the two ordinary quadrants,
  incoming full product, exact dependency suppression, ordered stored Context
  composition, unioned sources, composed scoped transformer and upper demand.
  The fixed `keyOf` is for one exact ordered **canonical physical input pair**
  and its attached immutable relation identities. Changed physical input pairs
  need their own generator projections in the same native history; `external`
  does not authenticate those projections.
- `candidate_effect.rs:1237–1305` and the imported `Effect.checkOperand` agree
  on all indexed Support members, optional Support tail, Contribution and
  AnnotationMember membership checks, closed-weight allowance selection,
  Allowance tail, local return, conflict and unavailable alternatives.
- `lib.rs:15214–15250`, `candidate_effect.rs:513–519` and
  `candidate_context.rs:3025–3036,3361–3372,3456–3482` justify the child payload:
  child-local source Context, processing-parent source set and full same-kind
  Effect transformer. `concrete_operand_children` computes that list, proves
  its current projection using representative idempotence, registers it and
  derives the next invariant/currentness. It does not assume child closure.
- `candidate_extrusion.rs:1147–1180` supplies the reflexive return and bound
  selection. `row_residual_step` covers a distinct row-lower request, both
  row/row level branches and rigid upper endpoints. It constructs the bound,
  exact directed pair and graph step. It does not derive the residual Context
  ID or successful full Context/Dispatch execution. General `Step.bound` is
  broader than this helper; rigid-lower/row-upper placement still needs its
  own actual-owner instantiation when constructing whole native coverage.
- `candidate_context.rs:3898–3936` distinguishes exact checked Allowance
  identity carriers from ordinary post-check residual carriers.
  `candidate_intrusion.rs:568–708` and
  `candidate_context.rs:4230–4254,4318–4331` support the copy/forest/frozen-prefix
  carrier and path mapping, including third-owner bounds.
- `lib.rs:14288–14420,14881–14947` keeps active dispatch, diagnostics, ordered
  completion and ReturnReady separate. Settlement is reached at the actual
  Transport/current-none empty-worklist boundary; a settlement loop may queue
  work before another merge. The algebraic merge rule alone does not establish
  those scheduler premises. Pair admission at
  `candidate_intrusion.rs:423–456`/`lib.rs:13507–13518` is not child completion.

Native admission success remains material even for the concrete child helper.
It computes key data and an abstract graph event, not successful interner or
enqueue execution. In particular `relation_with_scoped` at
`candidate_context.rs:3062–3073` rejects a nonzero-transformer self-relation;
a Support tail can compute a child whose canonical row endpoints coincide.
ID validity, that guard, resource success and partial-enqueue/transaction
handling must be established by the common event erasure. They must not be
inferred merely from `computed : operand ... = .children pairs`. The packet's
explicit unproved source-authentication boundary accommodates this; no native
success theorem is being accepted here.

## 5. Complete theorem census and retained failures

I inspected the origin-census program. It selects by originating module index,
not namespace spelling, visits all constants, rejects originating axioms,
prints every theorem type and axiom set, and rejects transitive dependencies
outside `propext`, `Classical.choice`, and `Quot.sound`. I independently parsed
all 143 complete begin/end blocks and compared every printed type and axiom
set to the inventory: **143 unique exact matches**, with no abbreviated types.
The census contains 333 originating declarations, 38 explicit source theorems,
105 generated theorem constants, and 15 private theorem constants within that
generated set. Authored and generated types were inspected, including the
recursive eliminators, projection theorems, matcher equations and equality
helpers; no unreported logical premise or project axiom appeared.

| Complete transitive axiom set | Theorem count |
| --- | ---: |
| None | 72 |
| `propext` | 35 |
| `propext`, `Quot.sound` | 34 |
| `propext`, `Classical.choice`, `Quot.sound` | 2 |

The two choice users are exactly `missing_depth_has_frontier` and
`historical_child_closed_or_frontier`. Principal constructive graph/Replay
roots use `propext, Quot.sound`. An independent source search of the changed
dependency cone found no proof holes, project axioms, native-evaluation
assumptions or kernel-check bypass. The producer's only broader regex hit was
the native API name `candidate_context_admit` in a comment.

Producer call receipts 01–11 were inspected. Exits are respectively
`1,1,1,1,1,0,1,0,1,0,0`. Call 01 records Lake installation-configuration
recognition failure. Calls 02–05 retain dependent-induction/simplifier goals,
list/type/constructor-pattern issues and an unavailable tactic; call 07 retains
the missing explicit `keyOf`; call 09 retains the reserved `local` binder.
All exact failed source snapshots are present and hash matched. Their changes
to the final source were inspected; the final additions supply explicit
frontier/recursive roots, concrete payloads and guarded reflexivity rather
than hiding a failed case as an axiom. Calls 06 and 08 are earlier successful
stages, not validation of the final bytes. Calls 10 and 11 validate the final
source and whole originating census; their census logs are byte-identical.

The recorded pinned commands use the fixed native Lake under
`/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake`,
`--no-cache`, isolated `native-current-r3/project/.lake`,
`LEAN_NUM_THREADS=1`, `lean -j1 -M1024`, and a 120-second check deadline.
The logs report Lake `5.0.0-src+eb6cafb (Lean version 4.35.0)` and Lean `4.35.0`,
commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Final call 11 is exit 0,
3.154775542 seconds including census, 2.476852 user + 0.640945 system child
CPU seconds, observed child maximum RSS 1,000,944 KiB. Call 10's full check is
exit 0 in 9.063859178 seconds. Earlier memory peaks were not measured.
Producer usage is 11/14 calls. No final error or warning is present in those
two final logs.

**Reviewer execution: 0/2 Lean calls used.** No concrete unresolved kernel or
elaboration risk required rerunning the frozen checks; review was static with
hash/type/census reconciliation and native source inspection. Therefore this
receipt validates the producer's recorded checker evidence and supplies fresh
independent mathematical/source-boundary review; it does not claim a new
independent kernel execution. No Cargo/native probe, network, installation or
shared-cache operation ran. Python reads set `PYTHONDONTWRITEBYTECODE=1`.
Reviewer peak RSS and exact wall consumption were not instrumented; the review
finished inside its 900-second envelope.

## 6. Application to the unchanged original parent

The accepted advance is the constructed, recursively unfoldable **operand
subgraph** from empty abstract events, including current carriers and both
Replay skips. Applying it to the original gate still requires all of:

1. **Whole actual Context factoring.** Construct outgoing clauses for every
   installed check and the exact residual/consumed branch, preserve pure-Replay
   versus directed-residual parser behavior and all successful callbacks.
   One favorable retained fiber cannot stand for the full parent Context.
2. **Whole constructor coverage.** Add every actual indexed Value port,
   record adaptation and remaining actual Effect/structural branch at its
   source owner. The current Effect fragment does not narrow supported Yulang.
3. **One common committed native execution.** Authenticate fixed `keyOf`,
   immutable tables and interning, full child payloads and guards, physical
   attachments, heads/dependencies, current representatives/post-check maps,
   queues, partial dispatch frames, duplicate admission and all merge cuts.
   Distinct Replay births/indices remain distinct acknowledgements even when
   they share one graph key. Rollback/cancellation must use the same committed
   cut and preserve identities under numeric reuse. This module supplies no
   rollback constructor or composition with the parallel execution-history
   result.
4. **Accepted drain and semantic application.** Eliminate relevant concrete
   unfinished owners using that same execution's diagnostics, ordered
   acknowledgements and ReturnReady; then supply retained-row/fiber semantic
   closure, full Context interpretation and the same original source-scoped
   witness. `ClosedAt` alone supplies none of these additional conclusions.

The primary retains ownership of those assignments, status synchronization,
integration and production decisions. The original A/B claims, complete Call,
effects/hygiene, source scopes and shared witnesses, ordinary supported source
domain, principal coverage and inference termination remain unchanged and
OPEN where previously open. No requirement is reclassified as optional
research, no source-qualified compiler counterexample is claimed, and no
production promotion follows from this acceptance.

**WRITES STOPPED.** No child, background process or checker remains. This
receipt and the single reviewer scratch evidence JSON are the complete output.
