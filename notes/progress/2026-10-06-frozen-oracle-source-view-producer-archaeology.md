# Frozen Oracle: parameter binding and captured marker views

Date: 2026-10-06
Status: frozen, independently compiler-referee reviewed with no findings; historical characterization only
Yulang3 baseline: `ef32d475bd7448bcf68d8e702d017cba50a15202`
Frozen Oracle: `/tmp/yulang2-oracle-rebuild`, `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Exclusive lease: this note only
Semantic and implementation authority: none

## Objective and result

Locate historical machinery nearest to
`SourceViewInst(r_A,d_f,e_f; k,beta,u,p0,sigma)`, especially parameter-boundary
introduction and capture/read association. Method: bounded static dataflow
derivation from the frozen source, with one existing fixture inspected only.

**Claim class: bounded historical characterization and a conditional local
preservation lemma.** An adapter constructs fresh runtime guard markers from
supplied hygiene data and attaches them to an argument before adaptation and
underlying invocation. A simple parameter binding stores the resulting
`SharedValue` unchanged under a definition-derived environment address; a
later closure captures that environment and its local read returns the stored
wrapper. This adds the explicit marker-to-parameter-to-captured-read route to
the prior annotation channel and provider-attachment archaeology.

The route consumes solved endpoints and existing hygiene plans. It does not
construct the current original upper-occurrence/formal-receipt association.
Marker attachment, lexical address retention and typed source provenance are
distinct obligations. No Oracle behavior is proposed for adoption.

## Governing scope and hypotheses

Current authority is inferred call views §§1.1–5, the nested-block addendum
§§1–3, and the direct directional decision §§1–4: a protected inferred variable
protects its original Function-upper output occurrence, without backflow to
an existing lower/provider occurrence. The DFRAG note §§2–4 specifies the
remaining typed/scoped source-origin association. Typed-boundary §6 distinguishes
views `(v,t,e)`, introduction, indexed transport and receipt; typed-core §6 and
§7 distinguish source entry from representation-preserving checking.
These current sources govern the comparison; frozen Oracle is historical only.

H1, established provenance: initial current direct dependencies equaled their
blobs at the assigned baseline; all seven historical files below equal their
frozen blobs. Baseline `tasks/current.md` SHA-256 is
`6d2ad15b3e55b9e355a3677eadbe91faa1a26bf1e4c44beff7d0e0b1b8532c00`;
DFRAG is `f3a1261968db9edac0c8841151d90c35fc1cf9649c00bd7beb5d18f748239d4d`.

Final revalidation found a concurrent primary-owned task-frontier update:
`tasks/current.md` became
`05f293b47151f456b2faa7bc20df41f817b941b1e07555fc7a723f597fb5c052`.
Its narrow diff records reviewed conditional SourceViewInst and capture/read
constructors on an independently typed source envelope, while leaving upstream
profile existence, source realization and admission open. The historical
derivation below is unaffected and does not challenge that successor result.
Statements locating a missing association refer to the assigned baseline and
the inspected Oracle route; they do not claim that the updated successor lacks
its conditional constructor. No new successor proof was reviewed in this lane.

H2, candidate control input: the inspected routes execute normally for a
well-formed adapter, a simple `Pat::Var(d_f)` parameter, and a nested Lambda
whose later `Local(d_f)` read is reached. Source parsing, inference and
selection of that adapter for the exact nested source are not established.

H3, local preservation envelope: between binding, capture and read, the
captured environment has no newer entry for `EnvSlot(d_f)`, and the stored
value is not changed by another operation. The plain nested closure route is
used; recursion, projections and all continuation routes are outside the lemma.

## Exact historical chain

All paths and lines below refer to the frozen Oracle revision.

1. **Boundary consumer after solving.**
   `crates/specialize/src/specialize2/emit.rs:257–266` supplies a selected
   argument contract to `wrap_expr_boundary_with_argument_contract`.
   At `:806–829`, absence of solved actual or consumer types, or consumer
   `Any`, returns the expression without this boundary. The remaining path
   uses those solved endpoints. `:1013–1055` can select a registered cast,
   reject an unsupported boundary, or invoke the runtime-shape constructor.
   This is not a pre-comparison source producer.

2. **Typed adapter and supplied plan.**
   `specialize2/runtime_shape.rs:875–905` constructs a `FunctionAdapter` for
   equivalent Function endpoints with an argument contract, while equivalent
   endpoints without that contract return the original expression. The
   supplied source/target types and contract feed
   `crates/specialize/src/hygiene.rs:15–33,38–68`; the latter partitions
   body/argument/return markers. The already documented formal-keyed marker
   extraction is an input here, not a new result of this pass.

3. **Dynamic marker introduction before underlying entry.**
   `crates/evidence-vm/src/runtime.rs:11589–11604` turns each supplied
   `GuardMarker` into a fresh `EvidenceGuardId`, a Frame marker and an AddId
   marker carrying family path, depth and guard/resume fields.
   `apply_adapter_result` (`:18556–18603`) combines body and argument markers,
   enters an Adapter marker frame and marks the argument for `target_arg`
   before adapting it from `target_arg` to `source_arg` (`:18616`) and calling
   the underlying value (`:18634`). If adaptation returns an effect result,
   `:18619–18630` installs a continuation instead of immediately entering the
   body. This pass does not trace that continuation.

   `mark_runtime_value_for_type` (`:25862–25870`) does nothing when markers
   are empty or the supplied type needs no hygiene mark; otherwise
   `:25873–25898` retains an existing adequate wrapper or constructs/combines
   `RuntimeEvidenceValue::Marked`. These runtime identities originate at
   adapter invocation, not at an original upper-use occurrence.

4. **Definition address, binding, capture and read.**
   `EnvSlot::from(DefId)` is exactly `def.0 as usize`
   (`runtime.rs:6095–6101`). `bind_pat`'s simple variable arm
   (`:24503–24513`) inserts the complete supplied `SharedValue`; it returns
   before decomposing the value or its markers. `Env::insert_slot`
   (`:6120–6126`) prepends an immutable Rc entry. `Env::get_slot`
   (`:6109–6117`) returns a clone of the nearest matching stored value.

   Closure entry clones the stored environment, binds its argument, then
   evaluates its body (`:18317–18330`); nonempty provider environments wrap
   this order without changing the simple binding code. A reached inner Lambda
   clones the current environment into its closure (`:15570–15587`,
   `clone_env` at `:10842–10848`). Runtime lowering maps `Local(def)` to the
   same `EnvSlot::from(def)` and retains `def` for errors (`:9535–9538`).
   Its evaluation returns `env.get_slot(slot)`, or `UnboundLocal(def)`
   (`:15515–15519`). The marker wrapper therefore survives this local chain.

5. **Typed sidecar identifies adapters, not ordinary local reads.**
   `crates/control-ir/src/evidence_ir.rs:43–76` keys type evidence by
   InstanceSignature or `(ExprId, ControlTypedExprSlot)`; adapter slots are
   Source and Target. `:608–630` records the adapter's supplied endpoint
   evidence. `:752–774` retains its function expression and marker vectors,
   defining `creates_callback_boundary` by nonempty marker vectors
   (`:1447–1450`). In this collector the Local arm is empty (`:682–683`).
   `crates/control-ir/src/ir.rs:56,73–77` likewise gives Local only a DefId,
   while FunctionAdapter carries source/target types, function ExprId and
   hygiene. This is a bounded representation observation, not a repository-wide
   claim that Oracle has no typed local information elsewhere.

## Local derivation and smallest discriminator

Under H1–H3, let `w` be the actual post-adaptation `SharedValue` supplied to
the simple parameter. Binding creates the head entry `(EnvSlot(d_f),w)`.
An inner Lambda captures a clone of that persistent head. Later cloning the
closure environment preserves that head, and binding its distinct `x` adds
an entry at another address. `get_slot(EnvSlot(d_f))` skips that distinct
entry and returns a clone of `w`. Hence any markers already inside `w` are
retained at the read. This follows from the concrete environment constructors;
it proves neither the adaptation's full marker correctness nor a source typing
theorem.

The smallest analytical discriminator uses one binder, one captured environment,
one read and one already marked value. Change only the read's DefId to a fresh
unbound `d_g`. Its compiled slot changes and the read yields `UnboundLocal(d_g)`;
equal underlying value/type elsewhere supplies no fallback. Separately, supplying
no adapter markers makes the marking helper an identity. Thus address-based
preservation transports supplied evidence but cannot create its missing origin.
These are code-level deductions, not executed mutations or accepted-source
counterexamples. No seeds, random ranges or exhaustive enumeration apply.

The one inspected fixture is
`crates/control-ir/src/evidence_ir.rs:1566–1664`,
`records_direct_blocked_and_unhandled_effect_routes`. It manually supplies an
adapter at expression 6, function expression 5, unit source/target endpoints,
and a `flip` body marker. Its assertions classify a callback boundary. There
is no formal variable or capture/read chain in that fixture; its endpoints
are not a well-typed Function adapter input for `apply_adapter_result`.
It tests structural collection assumptions, not source generation or runtime
typed receipts. It was read, not run.

## Correspondence cut, independence and coverage

The inspected actual producer is fresh guard allocation and value wrapping;
parameter/capture/read constructors preserve that supplied wrapper. The static
adapter evidence is an expression-indexed sidecar. None of these inspected
records joins `EvidenceGuardId` or `EnvSlot(d_f)` to the current tuple
`(k,beta,u,p0,sigma)`, original receipt `r_A`, evidence root `e_f`, or one
original joint `xi`. The semantic source-origin association cannot be inferred
from `DefId` address equality, solved endpoints or fresh guard allocation.
This does not exclude a differently named producer outside the bounded search.

Frozen implementation assignments are independent of the current toy checkers.
The specializer, control collector and runtime share the historical
implementation and supplied endpoint/hygiene assumptions. The manual fixture
shares the collector's assumptions and bypasses the source producer. A checker
assuming these transitions would give model consistency, not proof of their
source rules. No independent review of this note is claimed.

Coverage is the five chains above and one fixture. Omitted: complete parser/
inference/source-to-control correspondence, non-equivalent adapter branches,
casts, specialized routes, all effect continuations, projected patterns,
recursion/generalization, actual source acceptance, current source-origin
production, event observation, receipt/liveness, admission, soundness,
principality and production conformance. Changed blobs, failed adaptation,
unreached capture/read, another slot write, different lowering or a discovered
upstream provenance constructor invalidate the corresponding local conclusion.

Checks used read-only revision/status reads, bounded `rg`, numbered source
windows, and Python byte comparison against `git show <pin>:<path>` plus
SHA-256. Initially twelve current dependencies and seven historical source files
matched; final revalidation retained eleven current matches and found only the
task-frontier drift described above. All seven historical files still matched.
Early combined context captures truncated; decisive sections were reread
narrowly. One nonexistent `specialize/src/boundary.rs` locator failed and was
replaced with the actual `specialize2/runtime_shape.rs` path. No absence claim
uses truncated output or the failed locator.

Only lightweight reads/hash checks ran; no builds, tests, Oracle execution,
probes, formatters, Git mutations or children. No numerical process/CPU/RAM/
wall cap was assigned; CPU, peak RSS and wall duration were not measured.
Only this leased note was written. Writes stop at this frozen submission.

## Review and next source obligation

A compiler referee reviewed the frozen core claim with no blocking, major or
minor findings (reviewed note SHA-256
`adbfcd5272b823412571b4f11a4aea2c859164740e5ef38d0936b92d54827122`, Yulang3
HEAD `ef32d475bd7448bcf68d8e702d017cba50a15202`). This integration changes only
review status and the next-source-obligation wording. The cited chain supports
only the local preservation lemma;
the reviewer confirmed that the fixture supplies no runtime Function typing or
source-origin evidence, and that post-adaptation preservation is not a claim
that adaptation preserves every introduced marker. The reviewer also checked
that the successor's conditional SourceViewInst and capture/read constructors
are distinguished from their upstream premises; the successor proof itself
was not re-reviewed in this pass.

The next source obligation is to produce and admit the compatible complete
profile and typed invocation rows required by that conditional constructor.
This historical chain is useful only for distinguishing evidence introduction
from parameter/capture/read preservation.

## Frozen source hashes and commit packet

| Oracle path | SHA-256 |
| --- | --- |
| `crates/evidence-vm/src/runtime.rs` | `eb3f2d42752ff112b621d35471ebab79e767523f4597c7d6bd57329d02231ee7` |
| `crates/control-ir/src/evidence_ir.rs` | `98245e893190b10b26ebb7f33ccbef037b2a7f203e3b1dbff3bd326952c907c3` |
| `crates/control-ir/src/ir.rs` | `69b2bfc106e4159a04cf7d66ebfa5cbe47578b534fd36f18a0f4842347ff95a3` |
| `crates/mono/src/lib.rs` | `713c195d46f33725a3447062f82f9dea23f3746be0c8b2f569ad9e411e79e83d` |
| `crates/specialize/src/specialize2/emit.rs` | `7318b132cef4217ae089d084577fb28f3abed34a5728474ee8569e4079d71e7c` |
| `crates/specialize/src/specialize2/runtime_shape.rs` | `e4443fa1c23a1ea0d957d4582f484abea53e1aa0dffe2f86a3f44fc70aa2e0e4` |
| `crates/specialize/src/hygiene.rs` | `266c05f4c937fc9f9d95cb6b1c435e9ff74181ffc5e8d7719faeefc7a8ff33e4` |

- Exact leased path: `notes/progress/2026-10-06-frozen-oracle-source-view-producer-archaeology.md`.
- Baseline: Yulang3 `ef32d475bd7448bcf68d8e702d017cba50a15202`; Oracle
  `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: primary-owned `tasks/current.md` changed from
  `6d2ad15b3e55b9e355a3677eadbe91faa1a26bf1e4c44beff7d0e0b1b8532c00`
  to `05f293b47151f456b2faa7bc20df41f817b941b1e07555fc7a723f597fb5c052`;
  its conditional-constructor frontier update does not change this historical
  mechanism. Other checked dependencies matched. No dependency was edited by
  this producer; integration-time revalidation belongs to the primary.
- Review status: compiler-referee reviewed, no findings within the bounded
  historical characterization and conditional local lemma; no successor gate
  closure or implementation authority.
- Checks already run: revision/status, narrow source/fixture inspection,
  byte/blob equality, SHA-256, note scope and whitespace. No builds/tests.
- Proposed message: `research: trace Oracle parameter capture and marker reads`.
- Shared-record deltas left for primary/curator: record dynamic adapter-marker
  introduction plus definition-address preservation through parameter/capture/read;
  distinguish this historical preservation from the successor's newly recorded
  conditional source certificate, retaining upstream source realization/profile/
  admission and broader production gates. Do not promote Oracle to authority.
