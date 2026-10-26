# Native record queries: constructive source and dispatch correspondence

Date: 2026-10-26. Status: research construction, submitted for fresh independent
review; not new semantic authority. Supplied baseline: `yulang3`,
`f5b947056f23fb50236463d86738bdea579c1514`. Owner:
`/root/native_record_correspondence`. Source inspection only; zero native tests,
probes or proof-checker invocations. The original
`SourceProblem.InferenceSoundness` and its supported source domain remain OPEN
and unchanged.

## Result and exact limit

This packet constructs the complete ordered native record skeleton from the
actual record slices, derives its child relation metadata and queue equation,
and traces a genuine source record-parameter action through both source
constraints to a record query and its return. It also constructs identity
payload plans for that trace. The source identity is an actual action,
occurrence/cause and execution derivation, not the synthetic `candidate_source::Wait`
token or a newly invented semantic stamp.

The unresolved equation is more specific than a missing certificate: neither
this record-parameter constructor nor the inspected annotation owners supplies
an elaborated **record adaptation** with its original semantic boundary and a
separate output view port. A native query skeleton is available; its attachment
to such an executable source boundary still needs its owning construction.
The completed `RecordBoundaryPreservation` consumer can be applied once that
attachment and corresponding child evidence are supplied. No full Call result,
request/resumption theorem, or complete source soundness follows here.

## 1. A genuine source generation, without a fictional record annotation

Use the existing source fixture text in `candidate_effect.rs:2918–2939`:

```yulang
my f {required, fallback = required} = fallback
```

This is a source-directed derivation of its constructors, not a newly executed
test. `local_source.rs:1378–1413` walks record-pattern children in syntax order,
retains each label, `SourceNodeKey`, binder identity and optional default, and
records each binder's source identity. `emit_candidate_source`
(`candidate_source.rs:1043–1068`) authenticates the actual `LocalSource` against
its HIR owner and checks every expression occurrence before recording
`source_owners`. Its record-formal case (`:1297–1313`) preserves field order and
binder positions in an `Action::RecordParameter` with the lambda occurrence.
`execute_candidate_action` (`:2457–2462`) calls the actual owner
`candidate_record_parameter`.

Let `p` be that formal's actual live row, `r` the required binder's row, `f` the
fallback binder's row, and `i` the fresh incoming row allocated for the defaulted
field. These names denote values computed by
`candidate_effect.rs:1581–1607`, not additional runtime identifiers. The owner
constructs:

| Order | Actual constraint or field | Source slot |
| --- | --- | --- |
| 1 | `i+ <= f-` for the incoming optional payload | `258 = 256 + 2*1` |
| 2 | `required+ <= f-` for the default expression | `259` |
| 3 | `R+ <= p-` | `43` |
| 4 | `p+ <= R-` | `44` |

Here the source-ordered slices are

```text
R+ = [(required, optional=false, r+), (fallback, optional=true, i+)]
R- = [(required, optional=false, r-), (fallback, optional=true, i-)].
```

The default's endpoint is taken from its source expression; it is not a presence
proof for `fallback`. The two record slices use the same `incoming` row for each
positive/negative payload. `term.rs:1334–1355` validates payload polarity and
copies the slice in order; it does not sort labels or remove duplicates.
`candidate_record_parameter` finally retains `R-` in `formal_domains`.

Each admitted source link calls `candidate_scheme.rs:4778–4788`, which constructs
`ConstraintOccurrenceId::new_wide(lambdaOccurrence, slot)` and
`CauseId::for_occurrence(id)`, admits its exact terms and provenance, and invokes
`constrain_live_value`. Thus slot 44's occurrence and cause are concrete
source-owned data. They are not inferred from an endpoint pair.

Slot 43 inserts the positive record bound on `p`; slot 44 inserts the negative
record bound on that same row. `candidate_apply_value`
(`candidate_extrusion.rs:1115–1138`) selects these opposite polarities and calls
`candidate_insert_bound` followed by `candidate_replay_bound`. Insertion records
the physical slot and verifies its readback against the exact `BoundKey`
(`:635–643, :728–750, :856–870`). Replay (`:1070–1110`) constructs

```text
lower_input = BoundKey(ValueRow(p), Positive, PositiveRecord(R+))
upper_input = BoundKey(ValueRow(p), Negative, NegativeRecord(R-))
task        = Value(PositiveRecord(R+) <= NegativeRecord(R-)).
```

The displayed rows are read through the owner's current canonicalization; the
raw source terms and original slice indices remain separate. On this fresh
formal construction the two bounds are the actual newly supplied producer and
demand. Their new fibers enter `candidate_context_begin_replay`
(`candidate_context.rs:3992–4056`), which constructs a relation and retains
`Replay { child, lower, upper, lower_input, upper_input }`. Its context combines
the two input contexts, its source set is their union, its scoped transformer is
their ordered composition, and its demand is the upper demand. A lower demand
is explicitly refused. The ordinary replay call queues its child with its
actual relation (`:4185–4199`); it does not run a separate source action.

For this particular example, the source set is **None**, not a fabricated
singleton. `candidate_context_seed:3383–3394` consults `references.checking`, and
`candidate_value_graph.rs:329–344` registers Apply occurrence slot 0 there, not
record-formal slots 43/44. Actual `Origin` entries, store provenance and the
typed-drain occurrence/cause still supply source attribution. Source sets are
not a substitute for all source identity.

## 2. Operational boundary identity and retained/erased evidence

The source frame selects an immutable schedule and action position
(`candidate_source.rs:443–458, :2423–2455`). The typed drain is created with the
original source occurrence and cause (`candidate_context.rs:2249–2258`).
`lib.rs:14186–14230` creates a source seed, chooses the incoming relation when
one already exists, enqueues the item, and only then constructs
`SourceDrainReceipt` with its actual origin index, selected relation, task and
cause. `Origin` separately retains the occurrence (`candidate_context.rs:3429–3438`).

A sufficient proof-side record event is the following product of actual values:

```text
RecordEvent = (source owner and action coordinate,
               source constraint occurrence and cause,
               source seed/origin and selected incoming relation,
               actual record-dispatch step in the execution,
               transported processing parent relation,
               raw record pair and both original record slices,
               parent post-check context, sources and scoped flow).
```

The execution step is an index into a genuine erased execution derivation; it
distinguishes repeated creation events without pretending that a reused
`RelationId` is a fresh semantic boundary. For slot 44, the source constraint is
`(lambdaOccurrence,44)`, and the Replay derivation names slot 43's producer as
well. After transport, `step_typed_drain` installs the actual work item's
relation before context checking and dispatch (`lib.rs:14303–14305,
:14341–14360`). That parent is the one used by RecordPort admission.

All fields can be recorded by induction over these actual source/solver steps.
There is no need to require every historical frame to remain allocated.
`record_source_drain_completion` (`candidate_context.rs:2177–2188`) may omit its
passive observation when reservation fails; an execution derivation can retain
the completed event even then. Conversely, a bare final relation or a synthetic
`Wait { generation, dependency }` cannot replace this derivation. The latter is
explicitly marked a synthetic source-boundary token at
`candidate_source.rs:448–464`.

This constructs an authentic **operational query identity**. Its equality with
the original manuscript's semantic adaptation boundary `j` is the separate
source-elaboration equation in section 7.

## 3. Exact finite shape construction

At a fresh concrete record-dispatch event, let `L` and `U` be the slices returned
by the original positive and negative record terms. Define `first(L,name)` as
the least original index with that name. This is precisely the increasing
enumeration with `HashMap.entry(...).or_insert(index)` at `lib.rs:14598–14600`.

Scan `U` by increasing original index `j`. The total mathematical outcome is one
of `Shape(slots,children)`, `MissingRequired(j)`, or
`OptionalRequiredUnavailable(i,j)`:

| Source lookup / target | Skeleton action | Actual native action |
| --- | --- | --- |
| No source field; target optional | `Absent(j,U[j])` | Continue; no child |
| No source field; target required | `MissingRequired(j)` | Stop scan; record diagnostic; return `Ok(())` |
| First source optional; target required | `OptionalRequiredUnavailable(i,j)` | Return `RecordAdaptationUnavailable` immediately |
| Any other common field | `Hole(i,j,L[i],U[j],query)` | Append one payload child |

For a hole,

```text
query = Value(value_endpoint(L[i].value,Positive),
              value_endpoint(U[j].value,Negative)).
```

The proof-side `slots` retains every target field, including absent optional
ones. Its `children` projection deletes only `Absent` slots and retains the
original `(i,j,query)` of every hole. Successful scanning therefore has one slot
per target field and exactly the native child vector at `lib.rs:14616–14619`.
The absent slot is reconstructible from the immutable slices even though the
native vector omits it. Presence bits are everywhere false.

This is a direct finite induction on target index, with the accumulated vector
as invariant. The first match is stable because `or_insert` never overwrites an
earlier index. Before each iteration the accumulator contains exactly the
common admissible fields in the completed prefix. Each of the four branches
above preserves that invariant or returns the exact first failing index.
Optional/optional is in the common-field branch and always contributes a
payload query, independently of any particular runtime value's absence.

Failure order matters: a missing required field ends the scan before any later
optional-to-required field is examined. On missing required, a temporary prefix
of common children may have been accumulated, but **none is admitted**: the
early return at `:14631` precedes diagnostic child edges and RecordDispatch
installation. Optional-to-required returns even before pair-memo admission at
`:14621`. These different outcomes must not be collapsed into Rust `Result`
success/failure alone.

## 4. Indexed child evidence and sibling consistency

Successful scanning installs `RecordDispatch { children, next:0, pending:None }`
(`lib.rs:14632–14641`). `candidate_record_port_admit`
(`candidate_context.rs:3603–3633`) then constructs:

```text
parent       = actual context.processing
raw query    = stored TypedPairKey in RecordDispatch
relationPair = candidate_context_pair(raw query)
context      = post_check_context(parent)
sources      = relations[parent].key.sources
scoped       = scoped_flow(parent)
child        = intern RelationKey(relationPair,context,sources,scoped)
evidence     = RecordPort(child,parent,original lower_index,original upper_index).
```

The possible local `PrefixLeft` branch is unreachable for this Value-child
path: `candidate_context_source:3361–3372` introduces local context only for an
Effect pair whose upper endpoint is an allowance. Thus the post-check-context
equation is exact. That context is the original context if not discharged, or
its retained residual/default identity if discharged (`:3297–3301`). A
`Derived(child,parent)` dependency is also retained when the algebra is
processing a pair. Neither dependency is an executed child cast.

The native constructor is named `Dependency::RecordPort`; its two indices are
the paired record-port evidence needed by an indexed proof representation.
Keep the raw query and canonical relation pair distinct. Neither compacted
child-vector positions nor canonical endpoint numbers can replace the original
field indices.

Within one uninterrupted successful record-admission block, equal canonical
payload pairs obtain the same child `RelationId`. Every step reinstalls the
unchanged `frame.current.relation` (`lib.rs:14303–14305`), and the current item is
cleared only when the whole block ends (`:14387–14394`). Frame preparation
(`:14261–14285`) prepares undo/ack storage without consuming children or
discharging contexts. Record admission only interns relations and dependencies;
RecordPort/Derived dependency insertion does not change relation keys or
post-check discharge (`candidate_context.rs:3153–3214`). Enqueue already has
`Some(child)`, so it does not generate replacement evidence. Hence parent
metadata and representative-dependent payload keys stay fixed during this
block. `relation_with_scoped:3062–3093` interns the complete key, giving the
claimed equality. Distinct RecordPort index incidences remain distinct even
when their child relation agrees.

This supplies native syntactic consistency for one per-relation evidence map.
It supplies neither selected semantic casts nor transport of an already solved
cast across a later generation or resumed/reconstructed history.

## 5. Queue order, processing, diagnostics and return

Write the successful child vector as `[q0,...,q(n-1)]`, ordered by original
target index. `candidate_step_record_dispatch` is actually at
`lib.rs:15007–15029` in the inspected bytes. With `next=k`, it admits
`q(n-1-k)`, retains the resulting work item in `pending`, and on the next stage
enqueues that item at the front and increments `next`.

If `W` is the pre-existing worklist, induction on `k` gives the queue after `k`
completed enqueues:

```text
[q(n-k),...,q(n-1)] ++ W.
```

After all admissions it is `[q0,...,q(n-1)] ++ W`. `enqueue_item` really uses
`push_front` (`:15223–15243`), and `pop_worklist` really uses `pop_front`
(`:15166–15171`). Admission order is reverse target order; initial sibling pop
order is target order. Later descendants can be placed ahead of later siblings;
the equation does not assert a flat global order of every descendant, nor does
solver queue order alone establish effectful runtime evaluation order.

Each popped child undergoes its own relation transport, context execution and
dispatch. Pair reuse additionally checks the actual processing relation and
current intrusion generation (`:13507–13517`). A current pair can skip fresh
dispatch; applying this fresh-constructor result to such reuse requires its
own generation/currentness evidence, not a new fabricated child list.

After queue exhaustion and intrusion settling, Diagnostics completes the
diagnostic delta and replays the root witness with the frame's original
occurrence/cause (`:14404–14417`). `replay_witness:16168–16189` reports a
`RecordMissingField` witness. Acknowledgements then complete replay ownership;
ReturnReady records the optional passive completion, pops the frame and
restores the previous processing state (`:14923–14945`). Return is a transition
count, not a plan or semantic typing derivation. `finish_candidate:10681–10692`
rejects unresolved active selection and packages observations, including the
error state; it does not turn `Ok` into an error-free semantic model.

Consequently successful semantic classification requires the relevant
diagnostic-completed, available, error-free route. `MissingRequired(j)` cannot
satisfy it, although native dispatch returns `Ok(())` for diagnostic recovery.

## 6. Concrete plan filling and the source example

Encode the finitely many actual labels injectively as the `Nat` labels of
`RecordBoundary`; this changes only label representation. Use one fixed
interpretation of payload endpoints, preserving the meaning of each actual
row. For a fixed authentic boundary, take one resolver
`resolve : Ty -> Ty -> Option Cast`. Fill each absence slot by `.absent` and
each hole by `.convert` when its corresponding child evidence establishes
`resolve(sourceTy,targetTy)=some cast`.

Induction over the scan, using the first-source lookup equation, gives the
existing consumer equation:

```text
RecordBoundary.compile (RecordBoundary.signature L)
  (fun _ => false) resolve U = some (filled slots).
```

This uses exactly `compileField`/`compile` at
`RecordBoundaryPreservation.lean:73–89`. The independent child supplier must
agree with **one** resolver for the boundary; arbitrary separately preserving
casts for equal payload pairs do not suffice. The sibling consistency result
above supports a syntactic per-relation map while leaving semantic evidence
construction explicit. No field-index or boundary stamp is added to semantic
`Ty` to force agreement.

For the genuine formal example, the actual child vector is

```text
[(0,0,ValueRow(r) <= ValueRow(r)),
 (1,1,ValueRow(i) <= ValueRow(i))].
```

Both comparisons survive shape construction; native value processing takes its
equal-endpoint case (`candidate_extrusion.rs:1120–1121`). Under any shared
interpretation of these rows, choose the identity payload cast for equality.
Its normal preservation proof is simply that its result is the input with the
same payload type. This fills the required and optional holes with identity
casts; the known-presence function remains false. The compile equation and
`compiled_run_preserves` therefore apply to this plan for every independently
well-typed visible input. The generic survivor theorem likewise applies. This
is a constructed instance, not a claim that the compiler executes this plan at
the formal-definition step.

The general shape algorithm also realizes missing optional targets as absence
and retains optional common payloads, so the manuscript discriminators remain
unchanged: direct `{foo?:string}->{foo?:int}` requires the payload query;
adaptations through `{}` preserve absence. Likewise a supplied
`{foo:int}->{}->{foo?:int}` plan cannot restore the forgotten field. No
transitivity rule is introduced.

## 7. Exact remaining source equation and routing handoff

Inspection of the annotation/checking owners prevents a false source bridge.
`SourceAnnotationValue` (`yu-hir/src/module/source_annotation.rs:140–155`) has
Unit, scalar, variable, hole, tuple and Function constructors, **no Record
constructor**. A source record ascription is therefore not an available trace
through that representation. For supported annotations,
`candidate_annotation_pair` checks the input at one source slot and exposes a
positive annotation at another (`candidate_effect.rs:1911–1947`);
`candidate_expression_ascription:1826–1832` passes the same candidate endpoint
as input and target. Local annotation instead uses a fresh root allocated before
checking, then exposed and returned after its check (`:1749–1772`). These are
the actual equations; none establishes the
required record output-view equation.

The record-formal owner constructs input-domain constraints and default-binder
links, then retains a negative formal domain. It does not return or attach an
elaborated `RecMap_j` node. Record literal construction also has a precise
different role: `candidate_source.rs:1979–1994` preserves source-ordered labels
and endpoints; `shadow_apply.rs:4014–4022` builds required fields in a positive
record and constrains the result row, with genuine occurrence/cause admission
at `:4165–4179`. It is a producer anchor, not an adaptation output certificate.

The indispensable supplier is thus an original source-elaboration equation of
the following form, with all displayed data tied to actual owners:

```text
elaborate(original source boundary)
  = check/adapt at j(input visible port,
                    distinct output visible port,
                    RecMap_j(filled exact native skeleton)),
```

together with the relation of that `j` to the event, scope, occurrence/cause,
producer origin and indexed children constructed above. If the source action
is only a constraint or unchanged-view flow, the supplier must classify it as
such, rather than inventing an adaptation. The whole-source theorem cannot
discharge this equation by the observed record dispatch alone. A complete-Call
consumer may own some application boundaries, but its native certificate
producer is a different unresolved construction; the already supplied original
`G_call` solution contains its own certificate.

For finite routing, raw Value-row links and the exact BoundKey/Replay
construction are operational inputs. Their classification as unchanged-view
flow still needs the original source rule and contextual guard. The edges in
`candidate_value_graph` are reference/SCC incidence, not automatically
unchanged-view record edges. An actual adaptation must have distinct ports and
no fabricated identity edge. Query tags, scope/context, occurrence and
producer/demand origins remain whole payloads even when endpoints agree.
No routing lemma can manufacture those source classifications, child casts,
contextual meaning or complete-Call evidence.

## 8. Frozen source identities and cessation

SHA-256 identities of the inspected inputs (paths under the repository root):

| Path | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `crates/yu-solver/src/candidate_context.rs` | `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e` |
| `crates/yu-solver/src/candidate_source.rs` | `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a` |
| `crates/yu-solver/src/candidate_effect.rs` | `70c42056a1041d54f88f16d7712875e3acf9ef7649b99a34bc990ff19f04936f` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `crates/yu-solver/src/candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| `crates/yu-solver/src/candidate_value_graph.rs` | `aaaa88a374083f898188cd390b8cf0244855d8c09c8939b9e68ee2831bc692cf` |
| `crates/yu-solver/src/shadow_apply.rs` | `f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d` |
| `crates/yu-solver/src/term.rs` | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` |
| `crates/yu-hir/src/module/source_annotation.rs` | `409ce491bc216c6963bf76d20810790aa2756edf260ecc35e76d5cfc05d24b3f` |
| `crates/yu-hir/src/module/local_source.rs` | `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1` |
| `notes/theory/lean/YulangClosure/RecordBoundaryPreservation.lean` | `1bde9224c1b0d568d5cc73d84a5ccc5f1157452c87ea2ff428096c1dbd50d056` |
| `docs/yulang-whole-language-semantics-ja-expanded-20261023.tex` | `28dc9b7fcb818e99a9513054d5847274ccce0d816a8c4a9644b802f0aa3fbd65` |

The operating maps, design authority, top-level inference principles, complete
progress note and continuation selector governed this bounded construction.
Only this note and its leased handoff are written. No Rust/Lean edits, imports,
Git, child agents, shared status updates, tests, probes or checkers were used.
Fresh M3 review and integration belong to the primary. All writes stop after
the companion receipt is frozen.
