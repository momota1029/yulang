# R148 raw-bound history: fixed-source reconstruction obligations

Status: **conditional source-owner map; finite history NOT YET SUPPLIED**.
Author: `/root/r148_proof`, constructive leaf; no descendants. Independent
review and Luna adjudication remain required. This is stage 1, frozen before
the single observation, rather than a claim about an executed observer.

Contract: `tasks/agent-loop/sprints/raw-bound-history-20261020-r148-rev11.md`,
revision 11, SHA-256
`7ec1a9ac098020515b5651fd4dee8403288ce9c7b43b96b41d1828b0663407f0`.
Baseline: `4c9d549eab9f2ba38a2b319d4329599dd5272430`, tree
`a93b3c4d2eefdc80eb419b50d8605868d53976ea`.
Luna explicitly authorized read-only `git show BASELINE:path` for the four
mutable implementation-lane source owners. Their working-tree versions were
not read. All other inspected source owners below were unchanged inputs.

## Parent and actual application

The immediate parent is `R146-AUTHENTIC-RAW-BOUND-HISTORY-1`: obtain one
authentic production-reachable raw `Work::Bound` history from the unchanged
accepted `nested-recursion.yu`, its selected physical slot, relevant raw
preimages, mutation/canonicalization ordering, and actual relation-local
consumer. The original Simple-sub A/B and inference/evaluator claims retain
their original quantifiers and accepted source domain. R70 entry-to-return,
R71 raw/canonical coverage, source/native correspondence and production remain
OPEN. F1/FK1 and foreign continuations are not discharged by this local map.

The fixed source, SHA-256
`51aac3016d9000a1cc0e34e2050ca73f4aa44112f461ec6237195b0d65d89906`, is:

```yu
my loop x = { my helper y = loop y; helper x }
```

The useful result is an explicit reconstruction rule for a future finite
record. It identifies which exact owner justifies each transition and which
observed identities must agree. No selected slot, complete preimage set,
actual transport or consumer is inferred from the existence of these owners.
The missing runtime bridge is owned by Luna's one contracted observation and
the implementation lane's complete noninterfering event capture. A missing
bridge ends this stage; it does not license another source or observer run.

## Source construction to production extrusion

R146's source audit is reused only for its finite syntax/HIR/entrance map
(`notes/theory/2026-10-20-r146-source-admission.md`, hash below). Its observed
successful report had supervisor conformance UNVERIFIED, as its closeout
records; it is not reused as a raw chronological history.

The unchanged source resolves `loop` as ModuleDef, `helper` as Local and `x`/`y`
as their distinct Parameters. The two Apply nodes and the two Lambda nodes
remain distinct source occurrences. In `candidate_source.rs`:

1. `emit_candidate_source` retains Apply recipes and `ApplySourceInput` records
   (around 1389–1432), including source owner, callee/argument occurrences,
   level, result/effect components and checking cause. It retains Lambda
   recipes (1482–1498) with actual body endpoints and formal registration;
   Block uses a Group relation for its final expression (1501–1514).
2. Name construction (1293–1327) retains a Module action for `loop`. A Local
   either links an active initializer or retains a Local action; these paths
   must not be identified. The final `helper x` is after helper installation
   in the source schedule. The actual chosen Local route still needs its event.
3. `execute_candidate_action` (1742–1762) admits actual candidate/Lambda facts,
   routes Module uses through their active-open/incoming branch, routes Local
   uses, and installs local graphs. These are the constraint constructors;
   there is no hand-built graph premise here.
4. `candidate_scheme.rs::begin_candidate_fresh_bound` (1864–1908) reconstructs
   a captured bound's owner/item according to its retained polarity. If a
   relation exists, it constructs its FreshUse transport using the actual
   use identity/maps; then it begins physical bound restoration. This is a
   separate operation from ordinary extrusion and incoming allowance copying.
   `step_candidate_local_use` (2168 onward) completes these restorations before
   admitting the fresh-root link to the local occurrence target.
5. `lib.rs::dispatch_live_item` first respects pair memo state, canonical
   rewriting and retained extrusion rewrites. Its two calls at 12566 and
   12579 invoke `candidate_extrude` only for a structural/nonrow lower entering
   a row (positive, row level), or a row entering a structural/nonrow upper
   (negative, row level). A recorded helper invocation without its actual
   typed drain item, relation and production callsite is insufficient.

Thus the static route reaches the relevant constructors. It does not select
which production caller item executes or prove that its traversal has a deep
row with a nonempty selected side. Those are concrete observation premises.

## Raw selection and local transport rule

Write `C_t` for kind-preserving representative lookup at time t, and
`F_t(k)` for the exact RelationId prefix reached through
`State::bound_cursor(k)`/`bound_entry`, not the diagnostic origin list.
A physical slot is `(Value/Effect row, one of eight lanes, index)`; its stored
item is raw even if the representative has changed. Distinct slots can share
a key, and distinct raw keys can have one canonical image.

At baseline `candidate_extrude` records a new operation occurrence and builds
the root key from `C_t(initial)`, polarity and target level. For a visited deep
row, it snapshots selected direct/atom lengths before inserting the opposite
source link, allocates one same-kind copy at the target level, retains its
actual parent, and memoizes that copy. For each selected physical index n it
then retains two different objects (around 157–168):

```text
child key = (C_t(stored item), selected polarity, target level)
raw source = BoundKey(visited endpoint, selected polarity, stored item)
```

The source retains the raw stored item; the child key does not. Structural work
is processed before pending bounds. The local row/structure maps determine the
copy selected at `Work::Bound`; a final representative alone cannot reconstruct
the historical child mapping.

**Conditional local rule.** If this actual `Work::Bound(owner,p,key,source)`
executes successfully, its map lookup returns `copied`. It first calls
`candidate_insert_copied_bound(owner,p,copied,true,source,Extrusion{...})`,
then transfers the exact source prefix into
`BoundKey(C_t(owner),p,C_t(copied))`. For each relation r visited from
`F_t(source)`, successful `candidate_context_transport_witness_with_evidence`
(context 4091–4105) retains:

- the snapshot of `(source,Some(r))`;
- a destination child with canonical destination pair, r's actual source set,
  `post_check_context(r)` and the owner-defined `transported_scoped` payload;
- the exact Transport dependency, source/destination/reason witness,
  FiberTransform, and destination attachment.

This follows directly from the Bound arm, the exact-key cursor loop in
`candidate_transfer_bound_origins` (effect 677–688), and the transport owner.
It establishes forward transport for the visited prefix conditional on the
successful event, without assuming that this prefix equals all fibers at the
canonical key. The context cursor is an exact HashMap lookup (3141–3146).

The physical insertion owner canonicalizes its endpoints before admission,
appends to the selected lane, reads back that exact slot and checks full key
equality before evidence emission (extrusion 499–671). Admission preceding
append is not a converse proof that every admission has a completed emission.

Two distinctions are essential. In unscoped mode copied bootstrap emits an
OwnerEmission; it does not itself authenticate the selected source fiber. In
scoped mode the bootstrap imports relation-free evidence with
MissingOriginAssociation. The later `origins[source]` loop (effect 689–716)
also explicitly records relation=None and that coverage gap. Neither metadata
path replaces the separate executable-fiber loop. Missing source fibers remain
missing even when physical insertion and diagnostic metadata succeed.

## Mutation, preimages and the actual consumer requirement

`merge_candidate_rows` copies bounds before changing the forest representative,
then calls `candidate_context_canonicalize_bounds`, advances generation and
replays retained parent lowers. The sweep (context 4005–4023) captures the
current bound-key prefix and forwards each `(raw key,relation)` to its canonical
key with an EqualityCanonicalization witness; original attachments remain.
It includes third-owner incidence. This is forward transport, not reverse
saturation or equality of raw and canonical RelationId lists.

The R71 note's established one-way owner facts are reusable; its unsupplied
converse remains unsupplied. A canonical bucket can acquire independent raw
preimages. To instantiate the local rule above, the finite record must retain
the selected physical slot, forest at selection, every relevant raw physical
preimage and relation attachment, and the actual intervening merge,
compression and rollback order. Equal endpoints, payloads or final parent
rows cannot substitute for that inventory. A complete selected-fiber inventory
does not by itself establish that every canonical fiber is required by this
specific copying occurrence; the actual consumer must supply that obligation.

The owner of actual relation use is not the transport call. In particular:

- `candidate_context_begin_replay` (3767 onward) selects exact lower/upper
  bound prefixes, combines their specific relation contexts, source sets and
  scoped flows, and retains a Replay dependency with both input keys.
- Replay child delivery constructs a TypedWorkItem containing that exact
  RelationId and ReplayChildAck. With provenance it starts/steps an owned
  typed drain (3872 onward); without provenance it transfers into the outer
  worklist (3931 onward). Queued, drained and acknowledged are distinct.
- Relation checking can retain an exact discharged relation and residual
  (3616–3658). `post_check_context` selects that relation's own residual;
  equality of pairs does not license borrowing another relation's discharge.

An acceptable runtime reconstruction must join the selected raw relation,
actual Extrusion child, any subsequent EqualityCanonicalization/FreshUse
edges, exact Replay parent/input keys where applicable, and the actual typed
item/check/return. If the consumer has provider, attachment, witness, demand
or scoped payload, its actual identity must remain distinct and be recorded;
an absent field must be explained by the selected source/mode, not forged.
A transport dependency or a nonempty replay batch alone is not consumer use.

At this freeze there is **no observed event record** to instantiate any of
those identities. Therefore no authentic history, source-qualified failure or
actual consumer is established. No production repair follows. The exact next
step is reconstruction of Luna's bounded frozen receipt, if supplied within
the remaining original proof budget. Missing/incomplete output leaves R146,
R70 and R71 OPEN and stops this packet.

## Frozen inputs and checks

Four baseline blobs were read using Luna-authorized read-only `git show` and
their SHA-256 hashes independently matched rev11:

```text
8a1f531be9fb5e5f160bf4f75c6eb98bbc35ce0a30acaf06424c531840504ba4 candidate_intrusion.rs
fc0d948d884a406746066f3df8db257d5c6686505166b330bef839a9b9e2f35d candidate_extrusion.rs
6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0 candidate_effect.rs
002b9d86e26cfda6fdf094ea4d161501849a7127d55c2d147d408a781b9fd28d candidate_context.rs
cbc39315f4243b0bae1db74976cf94282bc94cd28b9eb463699c085f421065f7 candidate_source.rs
2e64dc8781189b4da21c30f4d1b3208aaef48ca247cae55fb7e77e68b5857850 candidate_scheme.rs
c75bf47b3d0d87e99d4365a587e6b90d5d05d05c335db16880cb2943b8b25985 lib.rs (solver)
19da9779e3e7866f5891e019e1cd343136ae0115bd1c47a02a7e7ee0cdfa80e0 candidate_value_graph.rs
620b09011ec4dc4bfa71998e2b6fc1498b9299b3056662fdaa80b17376ba23c3 candidate_receiver.rs
4ce290315e66b462052f4999178b6944bccbd3e048f5fe0664e459addb76d375 notes/theory/2026-10-20-r146-source-admission.md
f576ad08d386509eebda0eaf65da73ed90a0f2f4a668d1f63391bed16b32feee notes/progress/2026-10-20-r146-closeout.md
620947cece53ca60a7f8a2388a398f53850b835c79afd546bfdcfd10349a876e notes/theory/2026-10-19-r71-raw-canonical-fiber-coverage.md
```

The R71 note is historical conditional evidence, not new authority or an
independently certified theorem. R70's existing conditional simulation is
reused only under its stated entry well-formedness and successful-operation
premises. No new external dependency was introduced. Checks were bounded
source reading and SHA-256 only; no observer execution, test or build. One
initial read-only command used unavailable `python`; it was retried with
`python3` and produced no file. Only this note and its assigned inbox are new.
Requested routing: prover, configured Sol/high; observed model/effort UNKNOWN.
The exact elapsed/remaining budget and writer-stop receipt are in the handoff.
