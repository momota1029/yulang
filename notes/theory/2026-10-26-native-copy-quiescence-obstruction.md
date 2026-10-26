# Native copy obstruction to a first empty drain boundary

Date: 2026-10-26. Author: bounded `finite_copy_certificate` contributor.

Status: **independently reviewed source-code proof, scoped PASS**. This note
adds no Lean declaration, changes no solver behavior, and does not close or
refute `SourceProblem.InferenceTermination`. Its conclusion concerns the
particular already reached native candidate drain described below.

## 1. Exact conclusion and evidence classes

There is no finite, normal forward continuation of the recorded candidate
drain from the cut point in section 3 to its next `Transport` boundary with
`current = None` and an empty typed worklist. Consequently this drain cannot
return normally through its diagnostics/acknowledgements path. The proof uses
the actual copied upper fibers, insertion-triggered replay, relation-sensitive
memoization, retained rewrites, and settlement scheduling in the listed Rust
revision.

An availability error, checked identity exhaustion, allocation failure,
assertion failure, cancellation, or rollback is not a normal completion of
this drain. This note does **not** prove that actual Rust executes forever,
that every infinite continuation has unbounded row growth, or that a resource
error cannot occur. A finite observer cutoff is not used as a divergence proof.

Three evidence classes remain separate:

| Class | Evidence supplied here | What it does not supply |
| --- | --- | --- |
| Concrete initialization and finite reachability | A source file, a read-only observer patch, a source manifest, and explicit finite trace events | A Lean proof of the source-to-native initialization relation or of observer erasure |
| Native forward behavior after that prefix | The case analysis of the unchanged Rust owners in sections 4–7 | A kernel-checked Rust semantics or a theorem about an unspecified abstract solver |
| Original inference problem | The exact unchanged registered termination proposition is restated in section 8 | Its supported-input instance, `inferInitial` instance, or simulation by `inferStep` |

The independent reviewer must validate the first two evidence classes before
using this note as a native result. No successor-production premise is assumed:
section 6 derives the successor from the particular native constructors.

## 2. Fixed source revision and observational artifacts

Paths in this table are relative to the repository root. These SHA-256 values
were read from the current source and agree with the observer's
`source-manifest.json` for the same files.

| Native owner | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_context.rs` | `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `crates/yu-solver/src/candidate_effect.rs` | `70c42056a1041d54f88f16d7712875e3acf9ef7649b99a34bc990ff19f04936f` |
| `crates/yu-solver/src/candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| `crates/yu-solver/src/candidate_source.rs` | `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a` |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `crates/yu-solver/src/term.rs` | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` |

The observed source is preserved as
[`fixtures/2026-10-26-stale-bound-annotated.yu`](fixtures/2026-10-26-stale-bound-annotated.yu):

```yu
my top h (s:'t -> 't) = {
    my f x y (b:'b -> 'b) = { b b; b (y (b b)); h x; f {a: y}; y }
    f {a: (s s)} (s s) s
}
```

Its SHA-256 is
`f617815f862683495c3e8d040f4b378f14573cf1ef730a764ff254d748f07a84`.
The following files are in
`/workspace/scratch/e3678bef96db/native-termination-trace-r3/`:

| Artifact | SHA-256 |
| --- | --- |
| `stale-bound-annotated.trace` | `40b3c69d1cd992d73c411e85927eca640c57d21d701507ccd86dbd0bab9d2b1e` |
| `finite-prefix-results.json` | `19c644f0f7a596fae7cae1940e61678af0d6ff1c3649420ec6c57057cff52b8a` |
| `observer-only-r2.patch` | `99c3a3f402381581820c706cb1748b7216d67cb3d50ebf9193959a68e1216fb3` |
| `source-manifest.json` | `3fc156507e39d929bc031ad55f6a4021f7305960eb18b206e972341582364f26` |

The observer adds reads/formatting and trace output, exposes existing trace
sites, and deliberately panics at its event limit. It does not change the
solver-field updates used below. Its observed full run reached 12,000 numbered
trace events and 3,170 dispatches, plus the explicit cutoff marker; it did not report a
natural solver completion. Those totals are context only. The proof needs the
finite prefix through event 1229, not a conjecture based on elapsed time or
row-growth totals. Observation can itself change resource pressure; the
correspondence claimed here is the normal solver-field/control prefix with
observer activity erased, subject to independent review of that patch.

No build, compiler run, native rerun, dependency change, or Git operation was
performed by this contributor for this note.

## 3. The actual seed and the fixed cut point

Write `i -> j` for a physically stored direct upper row bound on row `i`,
with a nonempty actual `candidate_context` relation fiber at its `BoundKey`.
This notation is not an assumed transitive subtype relation. Let

```text
B = ValueRow(48), J = ValueRow(21), C = ValueRow(20),
S = ValueRow(47), A = ValueRow(45),
T = PositiveFunction(term276)
  = F+(B, EffectRow(43), EffectRow(44), B),
U = NegativeFunction(term301)
  = F-(C, EffectRow(19), EffectRow(47), ValueRow(18)).
```

At the cut point, `B`, `J`, and `C` have level 2. Rows `S`, 39, 32, and `A`
have level 1. In particular `A` retains its original upper `U`, whose argument
is still the high row `C`. The earlier merge was copy 51 into parent 45 at
event 354; it is not a premise that all high rows have already been lowered.

The relevant retained bounds and fibers are concrete:

| Stored bound | One actual fiber, with trace evidence |
| --- | --- |
| `B -> J` | relation 39, used as a transport parent at event 1223 |
| `J -> C` | relation 51, used as a transport parent at event 1220 |
| `C -> S` | relations 362/373/382, transported at events 1203–1217 |
| `T` is a lower term of `C` | relations 52/53, replayed at events 1166/1167 and 1839/1840 |
| `S -> 39` | relation 321, event 966 after dispatch 965 |
| `39 -> 32` | relation 334, events 1017/1018 after dispatch 1016 |
| `32 -> A` | relation 344, events 1050/1051 after dispatch 1049 |
| `U` is an upper term of `A` | relation 56, event 1067; `A`'s physical readout at 1049 also contains `U` |

The level-2 readouts include events 100 (`B` and `J`) and 1165 (`C`).
The low-path readouts occur at 965, 1016, and 1049. The only row merge in the
recorded prefix is event 354; its generation increment precedes this seed.

The earliest forced root copy used here starts at dispatch **1172** of `T<S`.
Occurrence **87** starts at 1173, with target level 1 and processing relation
363. Its negative and positive copies of `B` are `N0=65` and `P0=66`.
Its copied negative path is

```text
65 -> 68 -> 69 -> 47,
```

with transported fibers 412, 409, and 404/405/406 at events 1223, 1220, and
1203–1217. The original path `B->J->C->S` remains stored.
Occurrence 87 reports output term489 at event 1228:

```text
T0 = F+(ValueRow(65), EffectRow(84), EffectRow(85), ValueRow(66)).
```

Fix **tau** to be the solver/control state immediately before the body of
`dispatch_live_item` observed as event **1229**. This later dispatch is the
first convenient certified cut after the initial copy: reaching it implies
the preceding dispatch returned normally after finishing its extrusion,
retaining its rewrite, and enqueueing `T0<S`. The trace's event 1228 is inside
`candidate_extrude` before its final bookkeeping; event 1229, rather than
event 1228 alone, certifies completion of that bookkeeping and enqueue.
The observed generation at tau is 1 and there are 71 Value rows.

Later events corroborate, but are not hypotheses for the induction: `T0<A`
dispatches at 1713, `T0<U` at 1832, `C<N0` at 1833, and replay of `T<N0`
uses the original lower fibers 52/53 at 1839/1840. Occurrence 146 produces
71/72 and term494; occurrence 464 produces 77/78 and term499. The proof below
does not extrapolate from that observed count of three copies.

## 4. Formal proposition about the native execution

A native configuration here includes the active control location and drain
frames, typed queue, row arrays and levels, representative forests, retained
terms, relation fibers, replay operations, pair memos, and intrusion generation.
The transition meant by a **normal forward execution** is the actual
single-session execution of the Rust owners in section 2, with the candidate
graph enabled, continuing this already active drain. It preserves all other
queued Value and Effect work; it is not a projected Value-only interpreter.

Define `EmptyBoundary(sigma)` to mean that the next active
`step_typed_drain` case is `Stage::Transport`, its `current` is `None`, and
`typed_worklist.is_empty()` is true, immediately **before** the conditional
call to `settle_candidate_intrusion`. An empty queue while a Function admission
or enqueue phase is active is not `EmptyBoundary`.

**Proposition NQ (native first-empty obstruction).** Let tau be the concrete
cut in section 3, with the source and observer-prefix correspondence just
specified. For every finite normal forward execution

\[
  \tau=\sigma_0\longrightarrow\sigma_1\longrightarrow\cdots
       \longrightarrow\sigma_k
\]

of the same active candidate drain, no `sigma_i` is an `EmptyBoundary`.
Here “normal” excludes an `Err` return, panic/abort, cancellation, transaction
rollback, test-only mutation, external state mutation, or replacing/restarting
the session. These exclusions define the claimed continuation, rather than
asserting that an actual future execution cannot fail. Every fallible native
guard remains present: if it fails, this finite execution is not a normal
continuation to the proposed boundary.

Therefore the active drain cannot return normally via `Diagnostics`,
`Acknowledgements`, and `ReturnReady`: the only entry to `Diagnostics` first
passes the boundary above. No fairness hypothesis, infinite-identity axiom,
assumed row-closure law, or assumed successor-production law is used.

This is a precise source-code execution proposition and proof, not a claim
that a new formal Rust small-step semantics has been supplied or checked in Lean.

## 5. Native facts needed before a first boundary

Assume for contradiction that such a finite execution reaches a boundary,
and choose its first one, `E`. The following statements concern the finite
history ending immediately before settlement at `E`.

### 5.1 Fixed levels, representatives, and retained fibers

`step_typed_drain` calls settlement only in `Transport` with no current item
and an empty worklist (`lib.rs`, `step_typed_drain`, around 14308–14312).
There has therefore been no settlement after tau and before `E`.
`retain_extrusion_parent` records a parent and, when qualified, a pending
merge; it does not merge or lower the parent (`candidate_intrusion.rs`,
`retain_extrusion_parent`, 305ff). `merge_candidate_rows` is the candidate
operation that changes those representatives/levels and advances generation
(599ff, including 684/694).

The other existing-row level writes are source initialization
(`candidate_source.rs`, 2292ff), rollback (`lib.rs`, 9759), and legacy
extrusion (`lib.rs`, 13579). Source initialization does not interleave with
this synchronous drain; rollback is outside a normal continuation; and the
candidate dispatcher and `apply_value_task`/`apply_effect_task` take their
candidate branches before the legacy extrusion code. Fresh allocation only
adds new levels. Hence the listed high rows stay at 2, the listed low rows
stay at 1, and newly allocated target-1 rows stay at 1 throughout this history.
Generation remains 1.

Physical bound insertion appends; context `attach` either retains an existing
identical fiber or adds one (`candidate_context.rs`, 3284ff). Without merge or
rollback, none of the particular seed bounds/fibers disappears or changes
owner. Extra bounds are allowed and may produce extra work or errors.

### 5.2 What the first boundary says about prior work

For the ordinary route, `candidate_replay_bound` calls
`candidate_context_drive_replay(replay, None)` (1070ff/1110 in
`candidate_extrusion.rs`). That drive queues all children before its caller
returns; the outer drain owns their completion (`candidate_context.rs`,
4190–4236). Enqueue appends/prepends actual work items; it is not a pair-dedup
operation (`lib.rs`, `enqueue_item`, around 15200ff).

Function decomposition retains a four-child dispatch. Its admission and
enqueue phases cannot clear `current` until all four children have been
admitted and enqueued (`candidate_step_function_dispatch`, 14955ff;
`step_typed_drain`, 14367ff). At `E` no such phase is partially active, and
every item enqueued earlier in this active drain has been dispatched.
Otherwise that item would still occupy the queue or current slot.

There is no intervening scheme-restoration drain inside these ordinary
Value/Function dispatches. The synchronous replay route with nonempty
provenance belongs to `candidate_step_bound_restoration_child`, called by
scheme freshening/restoration outside the active typed dispatch. Ordinary
bound replay uses `None`. `start_typed_drain` requires an idle worklist, and
the local-use adapter also refuses source advancement while typed drain
frames exist (`lib.rs`, 14186ff; `candidate_scheme.rs`, 5055ff). Test-only
restoration call sites in `candidate_effect.rs` are inside its test module.

### 5.3 The replay fact uses insertion and fresh-endpoint ownership

Consider one of the ordinary bound insertions used below, with an already
present opposite physical bound and a nonempty relation fiber. The newly inserted
ordinary bound also has a nonempty fiber: `candidate_insert_bound` uses
`OwnerEmission`, and `candidate_context_bound_for` constructs and attaches
its derived relation (`candidate_effect.rs`, 530ff;
`candidate_context.rs`, 3898ff).

`candidate_apply_value` then calls `candidate_replay_bound` over every
opposite physical bound, even if the inserted physical bound is a duplicate
(`candidate_extrusion.rs`, 1115ff). `candidate_context_begin_replay`
(3992ff) enumerates the new-lower/all-upper and old-lower/new-upper fiber
quadrants. Thus any chosen lower/upper fiber combination either obtains a
queued child in this call or was already covered by an earlier replay call.
Its `replay_heads` advance only after the quadrants have been constructed.
The exact `Dependency::Replay` key can suppress a new queue entry only when
that dependency was already retained by a replay constructor. The production
constructor of those dependencies is this replay loop; test replacement
helpers are excluded. The ownership check below determines which replay
owner could have constructed a matching old dependency or replay head.

There is a necessary restriction on that historical argument. An incoming
restoration can construct a replay product whose later siblings have not yet
been queued while its current child drain is running. Consequently the mere
existence of an arbitrary `Dependency::Replay` does **not** establish that
its child was already queued in this drain. Historical completion can be
used here only after the following ownership check.

Every distinguished replay in this proof retains a fresh endpoint born
inside the current drain, in the exact data compared for deduplication:

| Consequence | Fresh endpoint in the actual child pair and dependency inputs |
| --- | --- |
| `F_N<next`, along the receiver path and `S->39->32->A` | The lower endpoint is the new Function `F_N`; the lower input is `BoundKey(owner, Positive, F_N)` |
| `F_N<U` at `A` | The lower endpoint and lower `BoundKey` still contain that same `F_N` |
| `T<N` at `C` | The upper endpoint is the new row `N`; the upper input is `BoundKey(C, Negative, N)` |

The intervening child `C<N` is a Function-port consequence, whose exact pair
also contains `N` as its upper endpoint; its creation does not use replay-key
deduplication. Each `N` is allocated in occurrence 87 or a subsequent actual
extrusion inside this same active typed drain. Its Function `F_N` contains
that new live-row ordinal. The native row/term constructors do not give
pre-existing valid bound fibers a reference to an unallocated future row.
The relation interner includes the actual child pair in its key; the replay
dependency key additionally includes both actual input `BoundKey`s.

Any suspended outer restoration product was constructed before its current
child drain started. It therefore predates `N` and `F_N`, so it cannot have
this child relation or these input keys. No new restoration is constructed
inside the active ordinary dispatch, by section 5.2. Thus an existing matching
dependency or matching recorded replay head for these particular fresh keys
comes from an ordinary replay in the current drain. That replay queues all
its children before returning normally. At `E` they have been dispatched.
This check also covers the first copied root `F_65`: occurrence 87 itself
was entered from the active dispatch at event 1172, not from a suspended
source initializer.

Replay composes context and scoped data and checks its guards. A failed guard
returns an error, so cannot be a silent escape on the hypothesized normal
history to `E`. The Value dispatcher does not consume a Value task merely
because a context returned “consumed”; that consumption branch is Effect-only
(`lib.rs`, 14432ff). A Value task with inappropriate checking filters errors
in context execution (`candidate_context.rs`, 3800ff).

This proves the required fresh-endpoint replay consequence by history. It
does **not** say
that arbitrary copied one-sided bounds trigger replay on insertion. The proof
uses opposite fibers that already exist before each ordinary insertion:
the copied upper path finishes before the rewritten root is enqueued, the
low path and `A.upper U` predate tau, and `C.lower T` predates every `C<N`.

### 5.4 Duplicate memos retain an earlier actual consequence

`pair_is_current` requires both an endpoint-pair memo and completion of the
actual processing relation at the current intrusion generation (`lib.rs`,
13507ff). Production completion marking occurs through
`record_typed_pair_admission`/`mark_candidate_pair` (15340 and
`candidate_intrusion.rs`, 423ff), not through the existence of a bound alone.

The mark can precede the same dispatch's consequence enqueue. This does not
justify dropping that consequence: at `E`, the marked dispatch has finished,
including any staged Function work. A subsequent duplicate therefore has a
historical consequence, even when it enqueues no new work. A canonical-alias
dispatch explicitly enqueues its canonical pair; if the canonical pair is
then skipped, its own existing pair memo supplies the earlier admission.
New copy rows in this interval have no representative alias at all.

For the relevant forms, the earlier dispatch must be one of the following:

| Pair form in this interval | Earlier consequence |
| --- | --- |
| Low `F_N < r`, with all four children of `F_N` at level at most 1 and `r` at 1 | Extrusion leaves the root unchanged; ordinary insertion installs `F_N` as a lower bound of `r` and replays existing uppers |
| `F_N < U` | Both shapes are Function; the four native children include `C < N` |
| `C < N`, where `C` is 2 and `N` is 1 | The row-row level test chooses `C` as owner and installs `N` on its upper side, then replays existing lowers |
| `T < N` | Its first actual structural extrusion, or a retained rewrite from such an extrusion, supplies a rewritten Function with a new negative copy of `B` |

None is an incompatible-shape, bottom, top, or equal-row early return.
For a low `F_N`, the unchanged-root fact holds from its birth onward, so a
prior memo cannot hide an earlier high-to-low rewrite of that same root on
these fixed level-1 receivers.

## 6. Native construction of an anchored successor

Call an **anchored occurrence** a completed actual positive extrusion of
`T=term276` to target 1, executed by dispatch of `T<r`, with these historical
properties: `r` has level 1; it already has a finite stored upper path to
`S`, all of whose vertices have level 1 and whose edges have nonempty fibers;
and its rewritten result is subsequently enqueued as `F_N<r`. A zero-length
path is permitted when `r=S`. This definition records actual constructor
events; it does not assert a closure or successor law.

### 6.1 What every such extrusion actually constructs

At entry, `candidate_extrude` creates fresh operation-local `rows` and
`structure` maps (`candidate_extrusion.rs`, 24ff). A positive Function visits
its argument negatively, argument effect negatively, result effect positively,
and result positively (around 293–334). Since `B` remains level 2, the
negative visit allocates a fresh target-1 Value row `N`; its positive visit
allocates a target-1 row `P`. The polarity is part of the local memo key.
`fresh_value_at_level` uses the current `bounds.len()` as the checked fresh
ordinal and appends the new row (`lib.rs`, 10456ff).

For a negative row copy the selected side is its upper side. The original
physical bounds `B->J`, `J->C`, and `C->S` are included in the selected
snapshots. `J` and `C` are copied negatively to target-1 rows `J_N` and `C_N`;
`S`, already at target level, is retained without traversing its bounds.
The resulting selected path is

\[
  N\longrightarrow J_N\longrightarrow C_N\longrightarrow S.
\]

Every edge has a nonempty actual fiber. `Work::Bound` first inserts the copied
physical bound and then calls `candidate_transfer_bound_origins` (397ff).
That function's **first loop** transports every actual source relation fiber
and attaches its child to the destination bound (`candidate_effect.rs`,
687ff; `candidate_context_transport_witness_with_evidence`, 4318ff).
The later origin-metadata loop is not used as evidence of a fiber. Successful
completion of the extrusion finishes all selected `Work::Bound` operations.

The result is the actual four-port Function

\[
  F_N=F^+(N,E^-_N,E^+_N,P),
\]

with both effect children also rows of level at most 1. This statement keeps
the native effect ports; it does not erase their queued work. The root's
changed negative argument means it differs from `T`. Function and live-row
term constructors retain their actual children/ordinals (`term.rs`,
`live_variable`, 1205ff; `positive_function`, 1230ff; structural interning,
1166ff).

Only then does ordinary dispatch retain and enqueue `F_N<r`
(`lib.rs`, 14707–14763). All selected upper-path fibers therefore predate
the ordinary lower insertion required for propagation.

Qualification of these new parents is immaterial to this interval: qualified
parents are pending, not immediately merged. This note does not assert an
abstract signed-occurrence qualification theorem.

### 6.2 From an anchored occurrence to the next actual root copy

Consider any anchored occurrence in the finite history to `E`. Its enqueued
`F_N<r` has been dispatched by `E`. All four children of `F_N` and all
vertices of the upper path from `r` to `S` are at level at most 1, so each
positive extrusion on that path leaves `F_N` unchanged. At each vertex,
ordinary lower insertion and section 5.3 yield the next queued pair, or its
earlier historical dispatch. The pre-existing path then continues through

\[
  S\longrightarrow39\longrightarrow32\longrightarrow A,
\]

so the history contains the consequence `F_N<A`. Its ordinary insertion
meets the retained fiber for `A.upper U`. Therefore `F_N<U` has also been
dispatched by `E`.

Both endpoints are Functions. The native contravariant argument child is
exactly `C<N`; the result and both effect children remain present as the
other three children. `candidate_function_port_admit` retains the actual
parent relation and either creates its Function-port relation or errors. A
matching scoped demand is checked against the actual negative Function root
and cleared for the Value argument child (3510ff). There is no successful
branch that omits the argument child.

Because `level(C)=2` and `level(N)=1`, the exact row-row guard in
`candidate_apply_value` chooses `(owner=C, polarity=Negative, bound=N)`.
`C`'s original lower `T`, with fibers 52/53, is still present. Its replay
therefore queues `T<N`, or certifies an earlier replay and dispatch of that
same pair. This is the required original high structure: replay does not
substitute `F_N` for `T` in `C`'s retained lower bound.

The ordinary dispatcher for `T<N` must use a real positive extrusion of `T`
to target 1. If this invocation is current and skipped, follow the finite
history to its earlier admission. If it uses a retained extrusion rewrite,
follow that retained rewrite to the actual earlier extrusion that installed
it. The only production writer of that retained field is the structural
extrusion branch (`retain_candidate_value_rewrite`, 15275ff); replay or a
diagnostic edge alone cannot manufacture it. There is no infinite backward
regress in a finite execution history.

At that earlier extrusion, receiver row `N` already existed. Every Value
copy made in this operation therefore has a strictly larger ordinal than
`N`. In particular its negative copy `N'` of the still-high `B` satisfies

\[
  N<N'.
\]

Operation-local memoization cannot reuse a row allocated in an earlier
extrusion. Reusing a retained root rewrite only reuses an extrusion that
occurred after this receiver existed, so it preserves the same strict
inequality. No ordinal reuse by rollback or merge occurs in this interval.

By section 6.1, this actual extrusion supplies `N'->J_N'->C_N'->S` with
nonempty fibers and enqueues its rewritten Function into receiver `N`.
Receiver `N` already has the copied level-1 upper path to `S`. Thus this is
another anchored occurrence in the same finite history, with a strictly
larger negative `B`-copy ordinal. This successor is derived from native
insertion, replay, dispatch, and copy constructors; it is not an additional
assumption about completed states.

## 7. Contradiction at the first empty boundary

The anchored occurrences completed by `E` form a finite nonempty family.
It is nonempty because occurrence 87, with receiver `S`, completed before tau
and enqueued term489; its selected upper path and fibers are in section 3.
It is finite because the hypothesized history and its native allocations are
finite. Choose an occurrence whose negative `B`-copy ordinal `N` is maximal.

Section 6.2 constructs another completed anchored occurrence in that same
history, with ordinal `N'>N`. This contradicts maximality. Therefore `E`
does not exist, proving Proposition NQ.

Choosing the boundary **before** settlement is essential. This proof does
not assume high levels survive arbitrary future merges. It proves that the
scheduler cannot reach the first opportunity to perform those merges on a
normal continuation of this drain. It likewise does not assume that every
eventually queued item is processed on an arbitrary infinite execution:
only a proposed finite empty boundary forces the historical completions
used in the argument.

## 8. Exact relationship to the original termination obligation

The unchanged registered declaration in
[`lean/YulangClosure/Contracts.lean`](lean/YulangClosure/Contracts.lean),
`SourceProblem.InferenceTermination` (152ff), is:

```lean
def InferenceTermination : Prop :=
  ∀ s x n, p.supported s → p.inferInitial s x n →
    Acc (fun next prev => p.inferStep prev next) n
```

**No instance of the negation of this proposition is proved here.** NQ
excludes one form of successful completion of a concrete candidate drain.
`Acc` concerns absence of an infinite chain of the selected `inferStep`
relation. An implementation that reaches checked identity exhaustion in
finite time can satisfy a termination statement while never completing this
drain normally. The note does not redefine `InferenceTermination` as
successful completion.

To apply this mechanism against the original obligation, the remaining
owners must supply all of the following at its original scope:

1. A concrete supported-source and `inferInitial` instance for the original
   problem, together with source initialization correspondence to this
   native prefix. Parser/CLI reachability alone is not that instance.
2. The selected meaning of `inferStep`, and a genuine correspondence between
   its states/steps and this copy/replay/settlement mechanism, including
   contexts, one-sided fibers, memoization, and pending merges.
3. If `inferStep` models an unbounded mathematical algorithm, a proof that
   its relevant constructors remain available and that the loop yields an
   infinite chain in that relation. It is not legitimate simply to delete
   the native error branches and call the resulting relation the original.
4. The required progress or nonstuttering correspondence, if a native
   constructor sequence is to be used as steps of that original relation.

These are original-application obligations. They are not hidden premises of
the native first-empty proposition. No source soundness, source principality,
full source witness, or abstract qualification conclusion follows from NQ.

## 9. Review surface and verification limits

The source-specific proof has these finite independent-review checkpoints:

1. Authenticate the observer-erased prefix and the actual fibers at the tau
   cut, rather than accepting a scalar row graph or the event-count cutoff.
2. Check the first-empty scheduling argument and all possible existing-row
   level/representative writes in the listed owners.
3. Check insertion-triggered replay with existing opposite fibers, the
   replay-head/dependency history, and the same-generation memo history.
4. Check selected upper transport and the retained-rewrite allocation-time
   argument, including the native effect and scoped guard error branches.
5. Check the original-theorem boundary in section 8 without narrowing its
   supported domain or replacing `Acc` by success.

No new Lean declaration is authored or asserted checked. The earlier
[`2026-10-26-finite-copy-closure.md`](2026-10-26-finite-copy-closure.md)
remains a separate conditional algebraic certificate; its hypotheses are
not imported as proof of the native transition facts in this note. A Lean
transcription of NQ would require an authentic native state/transition
encoding and discharge of the facts above, not another `Closed` or `Seed`
assumption containing the successor conclusion.

## 10. Independent review and finite-seed reproduction

Independent reviewer `/root/original_principal_closure_r3` passed Proposition
NQ as a manually reviewed source-code proof. The reviewed producer manuscript
has SHA-256
`f3d286abb819173279965b67673876466ddac708cbd019e00626676ba23cfb8d`.
One minor factual correction changed the numbered event count in section 2:
the old receipt's broader 12,001 count included the cutoff marker. This did
not affect the source, trace hash, seed or argument. Primary integration also
updates the status, links the byte-identical source fixture and adds this
reproduction section. The independent
[review receipt](../../tasks/agent-loop/inbox/20261026-native-copy-quiescence-review-r3.md)
retains the exact accepted and excluded scopes.

The fixture is 120 bytes with the section 2 source hash. A separate root-owned
run used the portable observer client, the same original native owners and
the independently reviewed read-only association extension. It stopped at
1,300 numbered events, observer exit 101, in 0.379 s, without a wall timeout.
The explicit observation cutoff is expected here. This is not a native solver
completion, an inference result, or a proof of divergence.

All 1,300 numbered trace lines match the earlier trace byte-for-byte. The
prefix through the actual seed event 1229 has SHA-256
`1f9ace6e0f253a61ec29fd0d650e809025244c3d9b5f5d8902fb0f23b6383398`;
all 1,300 lines have SHA-256
`c7e2c3ef5504c2a516f7e9f757585ae9e3d6de1319f7d79ba00162559e0606b5`.
The reviewer independently compared these prefixes. The run receipt and raw
output remain outside Git in
`/workspace/scratch/e3678bef96db/native-association-observer-r3/seed.json`,
`seed.trace` and `seed.stderr`.

From the repository root, with the matching installed Rust toolchain and
cached dependencies, reproduce this finite observation using the existing
private-copy preparation recipe:

```sh
proof_nq_dir="$(mktemp -d)"
python3 notes/theory/fixtures/2026-10-26-prepare-native-observer.py "$proof_nq_dir/observer"
patch --batch --forward -d "$proof_nq_dir/observer/source/crates/yu-solver" -p1 < notes/theory/fixtures/2026-10-26-native-association-observer.patch
CARGO_TARGET_DIR="$proof_nq_dir/target" CARGO_PROFILE_DEV_DEBUG=0 cargo build --offline --manifest-path "$proof_nq_dir/observer/Cargo.toml" -j1
YULANG_PROOF_TRACE_LIMIT=1300 timeout 20s "$proof_nq_dir/target/debug/yulang-finite-prefix-observer" notes/theory/fixtures/2026-10-26-stale-bound-annotated.yu > "$proof_nq_dir/result.txt" 2> "$proof_nq_dir/trace.txt"
```

The recorded run additionally limited process address space to 1 GiB.
The association readout is immaterial to the NQ argument; the numbered solver
trace is unchanged. This reproduction validates the concrete finite seed.
Sections 4--7, not the cutoff or the observed elapsed time, supply the native
first-empty proof. Section 8's original-theorem obligations remain open.
