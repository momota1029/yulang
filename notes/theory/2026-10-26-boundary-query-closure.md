# Constructed finite boundary-query closure

Status: constructed and checked; independent review pending. Research component,
not a production semantic decision or a native acceptance theorem.

Date: 2026-10-26. Producer: `boundary_query_construction`, generic `lean_prover`
leaf. Supplied baseline: `yulang3`,
`f5b947056f23fb50236463d86738bdea579c1514`; no Git operation was performed by this
leaf. Selection: [native continuation receipt](../../tasks/agent-loop/inbox/20261026-inference-native-continuation.md).

## 1. Original obligation and the completed component

The original manuscript's
[unchanged-view routing section](../../docs/yulang-whole-language-semantics-ja-expanded-20261023.tex),
lines 479–552, distinguishes four inputs: unchanged-view edges, producer
anchors, boundary-indexed demands, and direct concrete queries. An adaptation
consumes its input view and exposes its result at a separate output port; it
does not create an identity edge. Lines 356–425 give the optional-record
discriminator and non-resurrection rule.

The new module
[BoundaryQueryClosure.lean](lean/YulangClosure/BoundaryQueryClosure.lean)
constructs finite routing closure and proves its endpoint queries are exactly
the direct queries plus the original anchor/demand pairs connected by that
closure. No saturated relation, successful comparison, semantic interpretation,
or preservation law is supplied to this root. The completed record proof is
reused only for the original discriminator; record preservation is not reproved.

Before this component, the selected bridge lacked a constructed routing result
that respected the original distinction between identity flow and concrete
adaptation. After it, the routing obligation is a checked finite construction,
including a separate event induction for growing wiring. The first application
premise is now the authentic source/native extraction of those inputs and
events. That premise has not been hidden in the meaning of `Reach` or in an
assumed closure law.

The unchanged parent remains `SourceProblem.InferenceSoundness`:

```text
∀ source scope constraints solution,
  supported source → generates source scope constraints → solves constraints solution →
  ∃ witness, sourceJudgment source scope witness ∧
             sameScoped source scope witness solution.
```

Nothing here establishes this root, a complete Call certificate, contextual
effect meaning, joint interpretation, or diagnostic-completed native acceptance.
No supported source constructor is removed.

## 2. Exact data and finite construction

All declarations below are in `YulangClosure.BoundaryQueryClosure`.

`Port n` is `Kind × Fin n`, where `Kind` is value or effect. A finite completed
trace can supply a containing port universe; no particular numeric native ID
representation is asserted. In particular, separate proof-side view identities
must not be identified merely because native endpoint numbers coincide.

`Anchor n Head Origin` retains `(port, head, origin)`.
`Demand n Head Boundary Context Occurrence Tag` retains
`(port, target, boundary, context, occurrence, tag)`.
`Query` stores both whole records. Its equality is not equality of two endpoint
numbers. `Head`, `Origin`, `Boundary`, `Context`, `Occurrence`, and `Tag` are
arbitrary types; the routing roots do not require them to be finite or to have
decidable equality. Only their actual input lists are finite.

The opaque parameters can hold actual parent/source sets, scoped flow and
polarity, occurrence/cause, original paired indexes, and full contextual or Call
evidence. The algorithm neither projects them to scalars nor proves their
meaning. Every field is carried unchanged into the output query. In particular,
`Tag` is not a claim that an arbitrary tag is already a complete Call proof.

`Input` retains four lists: `wiring`, `anchors`, `demands`, and `direct`.
`Edge wiring a b` means that `(a,b)` occurs in the supplied wiring and the two
port kinds agree. Authentic source/context eligibility is an independent input
qualification obligation: the supplied graph must contain the edges appropriate
to that routing instance. Numeric equality and retention of a context payload
do not establish that qualification. This component does not model the native
raw-slot inventory or discard its distinct retained identities.

The actual closure procedure is:

1. Enumerate the finite port-pair universe.
2. Seed every reflexive pair and every admitted same-kind wiring pair.
3. Keep all unseeded pairs in `pending`.
4. A pair `(a,c)` fires exactly when some enumerated port `b` has both `(a,b)`
   and `(b,c)` in the previous route table.
5. Move firing pending pairs into the route table; stop when none moves.

This is a finite relational closure of identity wiring. Concrete query success
is not an input to its composition rule. `direct_does_not_change_routes` proves
that changing the direct-query list does not change any routed query.

The recursive `close` function uses the **initial pending length**, whose
sufficiency is proved. `remaining_strict` shows every changing round strictly
decreases that length. `pending_separate`, `additions_new`, and
`remaining_separate` show new rounds never re-add an old route membership.
`close_runs` constructs an explicit `Runs` receipt, and `routes_runs` applies it
to the real initial state. Each step of the receipt includes both new-membership
and strict-decrease proofs. There is no unresolved fuel adequacy premise.

`close_closed` derives transitive closure at the proved bound. `close_sound`
derives a genuine path for every retained pair by composing paths. Completeness
is induction on the independent `BirthLevelSCC.Reach` relation, using the actual
seed retention and derived transitive closure. Thus:

```lean
routes_exact (wiring : List (Pair n)) (a b : Port n) :
  (a,b) ∈ routes wiring ↔ BirthLevelSCC.Reach (Edge wiring) a b
```

`BirthLevelSCC.finiteReach` is not assumed or substituted for this algorithm;
only its independent `Reach` datatype and elementary path lemmas are reused.
The new closure is a proof-side reference procedure. It is not a proposal to
replace the native worklist with repeated full-table scans.

## 3. Exact query theorem, meeting ports and order

`routed` enumerates the input anchors and demands, retaining a pair precisely
when its port pair occurs in the constructed route table. `complete` appends
these routed queries to the original direct-query list.

For every natural `n`, all six arbitrary payload types, every input `i`, and
every complete query record `q`, the root is:

```lean
complete_exact (i : Input n H O B C X T) (q : Query n H O B C X T) :
  q ∈ complete i ↔
    q ∈ i.direct ∨
    (q.producer ∈ i.anchors ∧ q.consumer ∈ i.demands ∧
      BirthLevelSCC.Reach (Edge i.wiring)
        q.producer.port q.consumer.port)
```

This is exact **membership**, not a promise that query list order or duplicate
multiplicity is invariant. It preserves the original records and every direct
query. No evidence-resolution success is asserted.

`lowerAt_exact` and `upperAt_exact` characterize the two propagation directions:
an anchor reaches a meeting port, and a meeting port reaches a demand.
`query_at_meeting_port` proves that a routed query exists exactly when these two
original records meet at some port. The forward direction can choose the demand
port; the converse concatenates their path witnesses. This connects the finite
closure to the manuscript's lower/upper routing description.

`routed_kind` proves that routed endpoint kinds agree. Direct queries retain
their exact given kind fields; their validity is not certified by routing.
`completion_order_independent` proves that equal membership in the four input
lists yields equal completed-query membership. This covers reordering and
duplicate input records. It is not a simulation theorem for every native fair
scheduler or its reuse/currentness dispositions.

`query_eq_iff`, `origin_retained`, and `consumer_retained` expose the exact
record-equality consequences. In particular, boundary, context, occurrence and
tag must agree when queries agree, and the producer origin must agree as well.

## 4. Growing wiring and concrete adaptation boundaries

`Event` has edge, lower, upper, direct, and adaptation constructors.
`insertEvent` retains the prior lists and appends the event's inputs.
An adaptation event stores its input demand, output anchor, and a proof that
their ports differ. It appends both records and **does not change wiring**:
`adaptation_stops_identity` is the literal constructor equation.

`finish` constructs completed queries. `advance` applies an event and runs
completion on the updated input. `run` folds this operation over a finite event
list. `run_completed` is proved by induction on that list, and `run_exact`
applies the exact endpoint formula to the resulting input. The same theorem
can be instantiated at every finite prefix, including a prefix that creates
new child queries or wiring.

This is a separate finite event construction; a fixed-graph result is not
silently used for a changing graph. The global `Fin n` universe may include
ports allocated later in the trace. No theorem here says that an arbitrary
constructor event generator terminates, supplies a finite universe, is lawful,
or represents a successful native execution. Those are separate source/native
application obligations. No production retention of the event list is required;
it can be erased proof evidence.

Distinct input/output ports alone do not rule out an unrelated pre-existing
identity path between them. The generic adaptation equation claims only that
the adaptation constructor adds no such edge. An authentic extraction must
also exclude inappropriate pre-existing wiring for the new output view. The
checked two-adaptation discriminator starts with no wiring and therefore proves
the stronger absence result for that concrete construction.

## 5. Checked discriminators

The witnesses reuse `RecordBoundary.Witness.a`, `.b`, and `.c`: respectively
`{foo?:string}`, `{}`, and `{foo?:int}`. Their original record compiler and
preservation module remain unchanged.

* `Witness.unchanged_emits_failing_direct_query` places A and C on one
  unchanged-view edge. The completed query list contains the original A/C
  records, and the existing record compiler returns `none` for that direct
  comparison. Optional payload checking is not bypassed by an intermediate row.
* `Witness.two_adaptations_do_not_emit_ac` uses three distinct ports and two
  adaptation events through B. It emits A/B and B/C, while A/C is absent.
  `adaptation_wiring_empty` and `adaptation_ports_distinct` expose the exact
  reasons. This does not infer any concrete comparison by transitivity.
* `Witness.coincident_endpoints_retain_identities` changes origin, boundary,
  context, occurrence, or tag while leaving endpoint fields unchanged. Each
  changed query is unequal to the original.
* `Witness.late_edge_enables_old_endpoint_query` begins with an existing anchor
  and demand that cannot meet. A later edge event makes their exact query
  appear. This checks the event route that a fixed initial wiring theorem alone
  would miss.

The already checked record non-resurrection and distinct accepted-path results
are not duplicated here. Typed record-plan realization, child-plan resolution,
normal preservation, request/resumption closure, and native record dispatch
remain with their separate owners.

## 6. Source application and remaining owners

The native/source companion owns the map from actual annotation/checking and
record constructors to original boundaries, exact indexed child obligations,
context, occurrence and cause. It must justify unchanged-view edge admission,
and distinguish a new producer view from equality of native endpoint IDs. No
native ascription is instantiated as `Event.adaptation` merely because its
source syntax looks like a boundary. Its actual creation/consumer equation is
required; ghost view identities are permissible only with that correspondence.

The primary's separate native record-plan constructor can consume the exact
query records and fill child holes with resolved child plans. It must still
establish the real dispatch and field-order equation, diagnostic-completed
availability, and every child evidence contract. Routing does not turn scalar
regular-subtyping evidence into optional-record adaptation or complete Call.

The original source reconstruction owner still owes original sharing,
generalization, scoped witnesses, complete Call, contextual effects and
`SourceProblem.InferenceSoundness`. This packet reduces one concrete coverage
premise without weakening those obligations.

## 7. Verification and frozen evidence

Pinned tools: Lake `5.0.0-src+eb6cafb`, Lean `4.35.0`, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. The exact native Lake path was
`/workspace/scratch/e41512dd7957/toolchains/lean-4.35.0-linux/bin/lake`.
All checks used the isolated project under
`/workspace/scratch/f98087c7ac1a/inference-boundary-query-closure/project`,
`LEAN_NUM_THREADS=1`, `-j1`, `-M1024`, and a 120-second process-group deadline.

Final build: `lake build +YulangClosure.BoundaryQueryClosure`, exit 0, five jobs,
3.896 seconds including Lake. Final audit:
`lake env lean -j1 -M1024 AuditBoundaryQueryClosure.lean`, exit 0, 1.713 seconds.
The exact originating-module census checks **332 declarations, including 127
theorem constants and all private/generated declarations**, with 18 required
named theorem roots. All 332 begin/end audit markers match uniquely. Every
declaration's complete type and transitive axiom list is retained.

Of the 332 declarations, 211 have no axioms, 80 use only `propext`, and 41 use
`propext` and `Quot.sound`. None uses `Classical.choice`, `sorryAx`, a project
axiom, or unchecked native evaluation. Generic exactness/termination roots use
`propext` and `Quot.sound`; record-retention roots use `propext`;
`adaptation_stops_identity` has no axioms. No source hole or checker bypass
occurs in the new module.

Nine focused Lean invocations were consumed out of the primary's grant of 18.
All material failures are retained: initial reserved-identifier/implicit-notation
errors (01); one discriminator decidability failure (03); scratch audit counter
type inference (05); and an inspection whose guessed standard constant names
were unavailable (07). Calls 02, 04, 06, 08, and 09 succeeded. Audit 06 exposed
irrelevant standard classical order-law dependencies in Fin's default lawful
BEq package. The final source supplies a local direct decidable-equality BEq
for ports; build 08 and audit 09 verify the resulting source.

The sandbox prevented native installation self-location during setup. Explicit
environment guesses did not resolve it; no global settings or dependencies
were changed. Auto-reviewed escalation of the exact installed pinned toolchain
resolved the issue. `setup.log` preserves these failures and the successful
version receipt.

Frozen SHA-256:

| Item | SHA-256 |
| --- | --- |
| New Lean source | `7dad22c1b94e404be5dc4aaa51203e8d3882fd4c61006eb8b0c5f6f87a30f727` |
| Original manuscript | `28dc9b7fcb818e99a9513054d5847274ccce0d816a8c4a9644b802f0aa3fbd65` |
| Selected receipt | `2caf2e1965d3ca2cc07184a0895c74b116bbf1dfae568635afb9bb4b8a6626b5` |
| `BirthLevelSCC.lean` | `2c76b82d4dc85a4bf4c122731ba014b07df4c863ad679e9a795a57e6546243f0` |
| `Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `RecordBoundaryPreservation.lean` | `1bde9224c1b0d568d5cc73d84a5ccc5f1157452c87ea2ff428096c1dbd50d056` |
| Final build log, `check08.log` | `9af7a6215eba90ac4e185d2111f0ec446bebae28a28b8f6d900f35f3eb471293` |
| Final full audit log, `check09.log` | `eae205005c2e84e3f85b2caf61a58f6d08651964516ad24b1b89a0ed7c11e890` |

The source has exactly one terminal LF. Shared imports, status records, Rust,
tests, dependencies, and Git were untouched. Fresh independent review and
primary integration remain required.
