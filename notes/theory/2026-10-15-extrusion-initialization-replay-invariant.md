# Extrusion initialization: exact contextual replay admission

Date: 2026-10-15
Status: independently reviewed bounded native queue-admission derivation;
implemented in the private successor, with source/parent gates unchanged
Baseline: `c3c0fbdf542c63577f75140cf278d40af51f20c7`
Branch: `research/simple-sub-intrusion`
Parent gates: H1/H2/U remain OPEN; H3/P disabled; production/F5 separate

## 1. Frozen question and scope

Can a successful native `candidate_extrude(initial, polarity, level)` schedule
ordinary contextual opposite replay for the Effect bounds initialized by
`Work::Bound` and `Work::IncomingAllowance`, after all structural construction
and bound-origin transport, before returning its rewritten endpoint?

Fix one such call and its original `initial`, `polarity`, `level`, occurrence,
processing relation and actual parent/copy records. Let S be its state after
the Work loop and `finish_candidate_extrusion`, before a proposed replay pass.
Let J be the sequence of exact canonical Effect BoundKeys installed by those
two Work arms. Let I be its IncomingAllowance subsequence, retaining duplicates.
For each b in J and each physically
stored opposite bound c at b's owner in S, orient their keys as (L,U).
Quantify over **every actual attached relation fiber** l of L and u of U in S.
The requested local conclusion is:

1. The pass admits the typed Effect obligation for the endpoint pair of
   (L,U), retaining the ordered pair (l,u), both exact BoundKeys, the ordered
   Replay context and the union of sources.
2. Before successful return, every newly admitted replay child is transferred
   to the typed worklist, with its replay acknowledgement; it precedes the
   rewritten Value subsequently appended by structural dispatch.
3. This pass preserves the initialized constraints, contexts, view lineage,
   polarity maps and actual intrusion provenance, and has finite local cost
   bounded by the actual stored bounds/fibers it visits.

This is a derivation for the proposed pass, **not a statement that baseline
already calls it**. It assumes successful allocation/accounting and completion
of this finite call. A resource failure propagates and cannot publish this
partial result as successful. It assumes the existing contextual replay rule
is the intended operation; it does not independently prove the semantic
soundness of bound construction, transport or that rule.

Excluded: source sufficiency/reachability, semantic residual eligibility, full
H2/U, context algebra termination, descendant completion before Value dispatch,
all future/cyclic continuation, rollback/suspension correctness, full complete
Call, hygiene, soundness and principality. No source domain or original parent
theorem is narrowed. The Visit-arm one-sided parent links are not members of I;
this claim does not cover every bound installed anywhere during extrusion.

Governing authority: top-level inference principles §§1–3; contextual residual
lineage selection, Selected policy; contextual attachment/admission design §4
(bound insertion, opposite replay, extrusion). The older unconditional rollback
row is subject to the top-level principles. The primary owns authority
adjudication and independent review.

## 2. Actual construction and freshness

`candidate_extrusion.rs:24–363` is the construction owner. A single call has
one row map keyed by (endpoint, polarity, target), one structural map, and one
view map keyed by (old view, mapped tail). Structural work is exhausted before
the pending-bound stack is resumed. The proposed pass runs only after both
stacks are empty, not at an individual insertion.

`Work::Bound` (`310–325`) resolves the actually mapped endpoint, inserts the
selected side on the copied owner, then transfers all original bound fibers
with an explicit Extrusion transport witness. For Effect instances its owner
is a fresh Effect row allocated at the Visit arm (`115–130`). Both positive
and negative cases retain their original polarity. Thus its BoundKey did not
exist before this call. Multiple selected bounds may share that owner; that
does not identify their items or fibers.

`Work::IncomingAllowance` (`295–309`) is scheduled only by the positive Visit
of an Effect row actually copied to a fresh tail (`163–179`). It resolves the
positive source mapping, obtains the view through the same operation-local
view map, installs the negative Allowance bound and transfers the original
bound's fibers. Even if its source row is reused, the mapped view is allocated
within this call: the map began empty and this path requests a fresh copied
tail. `candidate_remapped_effect_view` / `candidate_copy_effect_view`
(`candidate_effect.rs:871–913`) allocate or reuse that same-call view; they
never reuse a distinct old view merely because heads/tails agree. Hence this
upper BoundKey also did not exist before the call. Another Work item can reuse
the same key within the call; the replay pass must handle this case.

Canonicalization changes row representatives only. It does not coalesce view
IDs (`lib.rs:11497–11503`). None of these construction arms, view copying,
origin transfer or `finish_candidate_extrusion` drives the typed solver or
performs intrusion equality. Therefore no representative changes during this
call arise from running queued work. `finish_candidate_extrusion`
(`candidate_intrusion.rs:297–318`) finishes the actual output-to-parent-group
index before the pass; replay does not recapture or replace those records.

Insertion first creates its owner-emission fiber and physical slot
(`candidate_extrusion.rs:435–570`). Origin transfer visits every attached
original fiber and retains a Transport dependency, its post-check context and
sources (`candidate_effect.rs:563–574`, `candidate_context.rs:3403–3416`).
The separate origin-table fallback explicitly retains
`MissingOriginAssociation` (`candidate_effect.rs:590–598`). The pass must not
erase that gap, invent a relation-to-origin association or treat origin count
as fiber count. The local quantification is over the actual attached fibers,
including the owner-emission fiber and any deduplicated transported fibers.

## 3. Sparse owner invariant and constructive queue proof

It suffices to replay I, without retaining/replaying every Work::Bound key.
Here is the constructional reason, independent of source reachability:

- A copied row starts empty at exactly the target level. Every Work::Bound
  on that row adds only its selected copy-polarity side. Positive and negative
  map keys allocate distinct copies, so they cannot supply opposite sides on
  the same fresh row.
- Visit's one-sided source link writes on an owner whose level is strictly
  greater than target. It cannot write on any new copied owner, whose level
  is target. Revisiting a copied endpoint reuses it because its level is at
  most target; it does not allocate another copy or source link there.
- IncomingAllowance always uses a positive source key. If that source is
  genuinely copied, its owner is a positive copy and this arm adds a negative
  upper. If reused, the owner may already have either side; this arm still
  contributes the new negative upper. It never targets a negative copy as a
  genuinely copied source.
- No typed task executes during construction. Consequently every opposite
  pair incident to a J key either has an IncomingAllowance upper, or is
  impossible: a Work::Bound negative copy has only uppers, and a positive
  copy without IncomingAllowance has only lowers.

Thus every quantified pair is visited by replaying its IncomingAllowance
upper after the entire Work loop, including when its lower was copied later
by Work::Bound. This avoids redundant Work::Bound opposite scans and depends
on the exact current owner inventory above. A future constructor that adds an
opposite side on a copy invalidates this sparse coverage argument until that
constructor is included.

Retain an operation-local sequence I of the exact Effect BoundKeys produced
by IncomingAllowance, after insertion and origin transport succeed. Reserve/charge
its capacity using its actual element size. After obtaining the root result
and finishing its parent group, run, for every retained key `(owner,p,bound)`:

```text
candidate_replay_bound(owner, p, bound, None)?
```

Do not drain the solver between these calls. Free/uncharge I with the other
operation-local scratch on success and failure.

For each invocation, `candidate_replay_bound` (`candidate_extrusion.rs:766–806`)
enumerates every physical opposite at the canonical owner, retaining the
level-selected side. Positive means `(bound,opposite)`; negative means
`(opposite,bound)`. It constructs the actual Effect task and corresponding
positive/negative input BoundKeys, then uses
`candidate_context_begin_replay(..., false)` and `drive_replay(..., None)`.

The initialized key is fresh relative to entry and no construction arm has
replayed it. Consequently the first visit of each distinct ordered input-key
pair starts with replay heads `(None,None)`. `begin_replay`
(`candidate_context.rs:3131–3208`) enumerates all l×u fibers, not representative
origins or marginal witnesses. For each pair it interns the child with:

```text
pair    = actual lower endpoint <= actual upper endpoint
context = IDENTITY, only if both input contexts are IDENTITY;
          Replay(context(l), context(u)), otherwise
sources = union_sources(l,u)
dependency = Replay { child, lower:l, upper:u, lower_input:L, upper_input:U }
```

Different fiber pairs can intern the same child RelationId. Their exact Replay
dependencies still distinguish both parents and BoundKeys. Within this pass,
subsequent visits of the same pair encounter the saved heads and do not
regenerate its Cartesian product. No fibers change between visits, because
replay generation/queue transfer does not execute children, insert bounds or
transport additional origins. Thus duplicates in I and physical bound arrays
do not omit a new pair. If another path is later added that mutates fibers
during this pass, this stable-state argument must be revisited.

`drive_replay(None)` transfers successive retained children using
`enqueue_item` and stops at Queued once every child is transferred
(`candidate_context.rs:3281–3344`). It does not mistake Queued for completed:
completion remains owned by the outer typed drain. `enqueue_item`
(`lib.rs:12894–12915`) reserves evidence/queue/undo storage, transfers the exact
acknowledgement, and only then performs infallible push_back. It neither pops
nor executes work. A child already carrying its RelationId avoids reconstructing
its context from endpoints. Induction over the finite retained child vector
therefore gives one queued item per newly admitted dependency, before the
pass can return successfully.

Structural Value dispatch calls extrusion synchronously, then appends the
rewritten Value (`lib.rs:12469–12512`). Therefore these initial replay items
are queued ahead of that particular rewritten Value. This is an admission
ordering statement. An initial Effect item can append descendants behind
the Value, and Function processing can push children to the front; no complete
effect-discharge barrier follows. Existing typed-drain acknowledgement and
publication obligations remain necessary.

## 4. Why the additional comparisons are licensed

Every compared pair shares an actual row owner r with retained constraints
`lower <: r` and `r <: upper`. The selected transition contract §4 requires
ordinary opposite replay on those constraints, and baseline
`candidate_apply_effect` already invokes this exact operation after ordinary
insertion (`candidate_extrusion.rs:843–867`). The proposed pass uses that owner
operation on initialized constraints once all their fibers are installed.
It introduces no additional endpoint relation based on shape, family equality,
lineage similarity or independently chosen witnesses.

For nonidentity inputs the conclusion is the exact ordered contextual Replay
obligation above. It is **not** an unqualified `lower <: upper`, a commutation
of contexts, or an assertion that both derivations hold under independent
assignments. Shared sources and both dependency parents are retained. This is
constraint preservation relative to the existing contextual transition rule.
It does not establish that every pre-existing owner-emission/transport fiber
is semantically justified by authentic source evidence; the explicit evidence
gap remains an evidence gap. In particular, no stronger all-context cut
elimination theorem is assumed or obtained.

At the concrete consumer, Support expands into members of that exact view;
an unmatched member against an open Allowance forwards to that view's exact
tail (`candidate_effect.rs:953–1025`). Since the pass preserves mapped operand
IDs, member ordinals, exact input keys and the single view map, it neither
merges distinct residual recipes nor substitutes an original member for its
mapped counterpart. It schedules each actual stored cut separately.

## 5. Finite local cost and implementation constraints

Let K=|I| (the IncomingAllowance count), D be the sum of physical opposite counts across the K visits, and
Q the set of distinct ordered input BoundKey pairs so visited. Let f(B) count
actual unique attached fibers in S, and
`P = sum_{(L,U) in Q} f(L)*f(U)`.

The pass performs K replay-bound calls, D opposite-bound visits and at most P
fiber-pair iterations/admitted dependency candidates. Repeated physical pairs
still cost visits but their recorded heads suppress product re-enumeration.
Queue transfer is at most P items. Additional sequence space is O(K), and
retained replay child/queue space is O(P), in addition to actual context,
source-union, interning, evidence, hash-table and journal storage.

This is a finite input-sensitive bound, not a constant-time or linear-time
claim: sources can have nonconstant union/hash cost and dependency/context
interning has its own cost. No global graph rescan, recursive completion,
brute-force source search or new source restriction is required. The bound
does not prove global context saturation terminates. Resource exhaustion must
propagate through the existing safe-stop path; silently dropping a comparison
or treating a partially queued pass as successful violates the conclusion.

Minimal constraints: retain exact negative keys from IncomingAllowance;
preserve both Effect copy polarities and the sparse owner invariant above;
collect duplicate events safely; finish every origin
transfer and structural node before replay; finish actual parent/output
records before return; keep one existing view map; invoke contextual replay
with `incoming_use=false`, no fabricated provenance and no synchronous drain;
charge all added scratch; release it on every exit; preserve all existing
evidence gaps and error propagation. Replaying immediately per Work item can
miss fibers transported later to an already-seen key and is outside this proof.

## 6. Evidence, limits and handoff

Method: static constructor/consumer derivation. Read-only commands: bounded
cat/sed/rg, baseline/status inspection and SHA-256; only this leased note was
written. No compiler/test/shared-record writes, Git mutations, delegation,
builds, tests, probes, benchmarks or measurement repetitions. One static leaf;
12-minute wall cap; no heavy process; CPU/RAM peaks and exact elapsed time not
measured. Initial combined captures exceeded output limits; decisive source
ranges were reread separately. Requested routing: normal Sol/high proof leaf;
effective runtime model/effort metadata: unknown. Config declares the prover
and leaves model/effort unpinned; that does not establish runtime routing.

This changes the investigated owner from reconstructing source reachability
to retaining and scheduling the exact initialization outputs. Necessary local
activation is A/B; reconstructing it from stored evidence alone was D under
the existing proof-economy audit. No parent gate is reclassified or closed.
The prior native observation establishes baseline absence of direct replay;
it does not independently verify this proposed pass. The primary remains the
sole executable verification owner and assigns fresh independent review.

Next action: primary adjudication of this bounded invariant, then the minimal
authorized implementation retaining IncomingAllowance keys plus the post-construction pass,
with focused verification that exact current fiber products are queued and
lineage remains distinct. Descendant completion and source adequacy stay OPEN.

Direct frozen dependency hashes:

```text
ed3e213e943a553943784e409194723f64acb810a0bcf06607ee95b0eb4e4ed1  crates/yu-solver/src/candidate_extrusion.rs
6301ca80eec137df3f2c2c44e2edaa7dbdf1ed7a78c69617228888e63654e461  crates/yu-solver/src/candidate_context.rs
f414efa7efdb17644f4dfa6b0bba621c1bb7cccd0f83735c33a0acb875da6b91  crates/yu-solver/src/candidate_effect.rs
4a2b87ebf6e5e219c06763bc4e589517fd48c575c89038f2a11fc1e6494fe90e  crates/yu-solver/src/candidate_intrusion.rs
e902da1c9a7f0fb4dcd806c87563d1ae46d35bbb999e69b7fee51c3c0f6e4bf5  crates/yu-solver/src/lib.rs
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98  notes/design/2026-10-10-contextual-residual-lineage-selection.md
717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc  notes/design/2026-10-10-contextual-attachment-admission-design.md
b8a8e4b521f4285c5d30c761eb2efc9cf6a7ac0c8f96e6e907f226f83d9fbb2e  notes/progress/2026-10-15-extrusion-current-cut-activation-observation.md
00e9691a3ecb92029f15fc6bb0a0c79f906287d2c6517e672e33ab7c7f1c6cd5  notes/theory/2026-10-15-pending-symbolic-cut-continuation-application.md
a3cc8951a01c3e39d85255d8b4c7fd96a30af7eef7bc370c5c7e7835f354aebf  notes/theory/2026-10-15-annotation-member-copied-tail-lineage.md
```

## Commit packet

- Exact lease: `notes/theory/2026-10-15-extrusion-initialization-replay-invariant.md`.
- Baseline SHA: `c3c0fbdf542c63577f75140cf278d40af51f20c7`.
- Changed dependency hashes: a final handoff recheck observed concurrent
  `candidate_extrusion.rs` changing from the baseline hash above to
  `5b3b30c6cfb3370fa62e1c429a358d64890e0bab5396f4928001b231870e357d`.
  This derivation concerns the frozen baseline owners and proposed pass;
  the live implementation delta is not reviewed here. The other four direct
  source dependencies retained their listed hashes. HEAD remained the pinned
  baseline. Primary must reconcile the implementation delta before review.
- Status: unreviewed bounded derivation for a proposed implementation; no
  compiler change, independent certification or parent closure.
- Checks: static owner/context/queue/cost trace, dependency SHA-256 freeze and
  recheck, and note trailing-whitespace search (no matches); no executable
  verification.
- Proposed checkpoint: `research: derive extrusion initialization replay admission invariant`.
- Shared-record deltas for primary/curator: record the exact two-arm
  initialization coverage via IncomingAllowance-only replay, freshness/product
  and queue-admission invariant;
  distinguish initial-item order from descendant completion; preserve all
  original source, H1/H2/U, complete Call/hygiene/soundness/principality and
  production/F5 gates. No shared file was edited.

Writes stop at handoff.

## 7. Independent review and implementation correspondence

A fresh `compiler_referee` reviewed the frozen derivation at SHA-256
`80b1c51ec1885e8e7e9c9c503f949d3568738d19070ef5afac60ed8c99224452`
against the baseline constructors, then the frozen native implementation and
new regression. No proof or native-code correctness finding remained.
The primary accepts the stated finite local queue-admission invariant;
source sufficiency, descendant-completion barriers and the parent gates in
§1 remain OPEN.

The implemented correspondence is
`candidate_extrusion.rs`, SHA-256
`b73bcf9baa65c3e8c3093bb8ff6fa0e303fedb3baae35dc4587b70679991efee`:
`IncomingAllowance` retains its canonical installed key after origin transfer;
the final pass runs after both Work stacks and `finish_candidate_extrusion`;
ordinary `candidate_replay_bound(..., None)` queues its exact fiber products;
the outer typed drain retains completion ownership. `Work::Bound` and the
operation-local maps retain the construction used by the sparse proof.

Independent `performance_auditor` review found no blocking or major issue.
In addition to §5's O(K) sequence and O(P) replay-child/queue storage, retained
replay-operation bookkeeping is O(D + P), including empty operations for
duplicate physical visits. Distinct nonempty source-set unions also incur
their existing O(S log S) sorting cost per union; no unconditional linear
time or measured speed claim follows. No benchmark was needed or run.

The semantic delta review found one direct-test caller that opened a Fresh
route before consuming its newly queued work. Pre-write `spec_auditor` review
approved using the same production structural Value dispatch in that setup.
The repair preserves every assertion, expected value and injected-failure
transaction; semantic delta review closed the finding. The native Effect
constructors used above are unchanged by that test-only adaptation.

Executable verification and baseline-confirmed residual failures are recorded
in the [implementation checkpoint](../progress/2026-10-15-extrusion-initialization-replay.md).
