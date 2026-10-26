# Boundary-query closure: frozen constructive handoff

Date: 2026-10-26. Producer: `boundary_query_construction`, generic
`lean_prover` leaf. Supplied baseline: `yulang3`,
`f5b947056f23fb50236463d86738bdea579c1514`. No Git command was used.
Parent authorization: ongoing whole-original-inference construction; selected
[native continuation receipt](20261026-inference-native-continuation.md).
Claim class: original inference-correctness component, not a weaker source
language or production semantic adoption. Independent review: **PENDING**.

## Outcome and original scope

Constructed an actual finite unchanged-view route closure, proved strict
new-membership/decrease receipts and adequacy of its initial pending-length
bound, and proved completed queries are exactly original direct queries plus
original anchor/demand records whose ports are reachable. No assumed saturation,
semantic model, preservation law, or arbitrary unresolved fuel is supplied.

Original source: manuscript
`docs/yulang-whole-language-semantics-ja-expanded-20261023.tex:479–552`;
optional-record discriminator at `:356–425`. The unchanged parent is
`SourceProblem.InferenceSoundness` for every supported original source, with
scope, sharing, generalization, complete Call, effects, optional records, and
method selection retained. This packet closes the constructed finite routing
component only. Native/source extraction and the full parent remain **OPEN**.

## Frozen artifacts and exact leases

Only these repository files were written:

* `notes/theory/lean/YulangClosure/BoundaryQueryClosure.lean`
* `notes/theory/2026-10-26-boundary-query-closure.md`
* this receipt.

Scratch/cache owner:
`/workspace/scratch/f98087c7ac1a/inference-boundary-query-closure`.
No shared import, status, Rust, Cargo, test expectation, dependency, toolchain,
question, or Git write. No children or new production checker.

| Frozen item | SHA-256 |
| --- | --- |
| Lean source | `7dad22c1b94e404be5dc4aaa51203e8d3882fd4c61006eb8b0c5f6f87a30f727` |
| Theory note | `9b529696fe010630b2c07755bc1d0cd642459e9472d612a5c5ddcdd73273895a` |
| Original manuscript | `28dc9b7fcb818e99a9513054d5847274ccce0d816a8c4a9644b802f0aa3fbd65` |
| Selected receipt | `2caf2e1965d3ca2cc07184a0895c74b116bbf1dfae568635afb9bb4b8a6626b5` |
| `BirthLevelSCC.lean` | `2c76b82d4dc85a4bf4c122731ba014b07df4c863ad679e9a795a57e6546243f0` |
| `Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `RecordBoundaryPreservation.lean` | `1bde9224c1b0d568d5cc73d84a5ccc5f1157452c87ea2ff428096c1dbd50d056` |

The isolated checked copies of the new module and all three source dependencies
are byte-identical to the repository files. The new source and note use one
terminal LF and no CR.

## API, theorem types, and independent inputs

All names below have prefix `YulangClosure.BoundaryQueryClosure`.

`Input n H O B C X T` has unchanged-view `wiring`, original `anchors`, original
`demands`, and `direct` queries. A port is `(Kind, Fin n)`. An anchor stores
`port/head/origin`; a demand stores
`port/target/boundary/context/occurrence/tag`; a query stores both entire records.
Opaque payload types are unrestricted. The theorem does not replace complete
Call or contextual evidence with scalar endpoint facts.

The main exact theorem, universally quantified over `n`, all payload types,
input `i`, and query record `q`, is:

```lean
complete_exact (i : Input n H O B C X T) (q : Query n H O B C X T) :
  q ∈ complete i ↔ q ∈ i.direct ∨
    (q.producer ∈ i.anchors ∧ q.consumer ∈ i.demands ∧
      BirthLevelSCC.Reach (Edge i.wiring)
        q.producer.port q.consumer.port)
```

`Edge wiring a b` is membership of `(a,b)` in wiring together with same kind.
Source/context admission of that wiring remains independently owed; stored
context and representative equality do not authenticate an edge. Direct-query
validity and payload semantics are not assumed or concluded.

Other required roots:

| Root | Exact contribution / premises |
| --- | --- |
| `remaining_strict` | A changed pending filter has strictly smaller length. |
| `routes_runs` | The real closure has a `Runs` receipt; every step adds new memberships and strictly decreases pending length. |
| `routes_exact` | `(a,b) ∈ routes wiring ↔ Reach (Edge wiring) a b`, for every wiring and endpoints. |
| `lowerAt_exact`, `upperAt_exact` | Original-record membership plus forward/backward reachability. |
| `query_at_meeting_port` | Routed membership iff the original producer and consumer meet at some port. |
| `routed_kind` | Every routed query's two port kinds agree. |
| `completion_order_independent` | Equal membership of wiring/anchor/demand/direct input lists implies equal completed-query membership. No list-order or multiplicity claim. |
| `query_eq_iff` | Query equality iff both full producer and consumer records agree. |
| `origin_retained`, `consumer_retained` | Query equality preserves origin, boundary, context, occurrence and tag. |
| `adaptation_stops_identity` | An adaptation with distinct input/output ports leaves wiring exactly unchanged. |
| `run_exact` | Every finite event fold has exact endpoint coverage for its resulting input. |

`close_closed` derives completion from the initial pending cardinality.
`close_sound` derives route witnesses, and `routes_exact` proves completeness
by induction on the independent path datatype. No arbitrary `LocalLaws` or
closure assumption is used at the application root.

`Event` constructors can add edges, anchors, demands, direct queries, and
adaptations. `advance` performs finite completion after every event.
`run_exact` is a separate finite event induction over one global finite port
universe. It does not assert termination/lawfulness of an arbitrary constructor
generator or extract a native history. The generic adaptation equation also
does not remove inappropriate pre-existing edges; authentic extraction must
exclude those separately.

## Original discriminators

All four named roots pass:

1. `Witness.unchanged_emits_failing_direct_query`: real original A/C record
   endpoints across one unchanged-view edge emit their query, and the imported
   record compiler rejects direct optional-string to optional-int comparison.
2. `Witness.two_adaptations_do_not_emit_ac`: two explicit adaptation events
   through empty B emit A/B and B/C, use distinct ports, and emit no A/C query.
3. `Witness.coincident_endpoints_retain_identities`: changing origin, boundary,
   context, occurrence, or tag changes the query despite unchanged endpoints.
4. `Witness.late_edge_enables_old_endpoint_query`: a later wiring event makes
   an old retained anchor/demand pair queryable; before that edge it is absent.

The first discriminator imports the frozen existing record witness. No record
normal-preservation proof or native record-plan module was rewritten.

## Actual verification and retained failures

Pinned Lake:
`/workspace/scratch/e41512dd7957/toolchains/lean-4.35.0-linux/bin/lake`.
Observed Lake `5.0.0-src+eb6cafb`, Lean `4.35.0`, native commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.

Each focused call used the isolated project, `LEAN_NUM_THREADS=1`, `-j1`,
`-M1024`, and a 120-second process-group deadline. Native self-location failed
under the sandbox; exact pinned commands succeeded with auto-reviewed
`require_escalated`, as confirmed by the primary. No installation, dependency,
global environment, or configuration change was made.

**Nine of 18 focused calls consumed.** Final commands:

```text
lake build +YulangClosure.BoundaryQueryClosure
  exit 0; five jobs; 3.896 seconds including Lake; check08.log
lake env lean -j1 -M1024 AuditBoundaryQueryClosure.lean
  exit 0; 1.713 seconds; check09.log
```

The audit identifies exact originating module indices and checks **all 332
declarations, including 127 theorem constants and all private/generated
constants**, plus membership/theorem-kind checks for 18 required named roots.
All 332 begin/end markers match uniquely. Complete printed types and complete
transitive axiom sets are retained, not just a source-name grep.

* 211 declarations: no axioms.
* 80 declarations: `propext` only.
* 41 declarations: `propext`, `Quot.sound`.
* No `Classical.choice`, project axiom, `sorryAx`, unchecked evaluation, or
  checker bypass. Named exactness and termination roots use the two standard
  axioms; record equality roots use `propext`; adaptation wiring equality has
  none.

Final build log SHA-256:
`9af7a6215eba90ac4e185d2111f0ec446bebae28a28b8f6d900f35f3eb471293`.
Final audit log SHA-256:
`eae205005c2e84e3f85b2caf61a58f6d08651964516ad24b1b89a0ed7c11e890`.

Preserved failures: check01 reserved `universe` identifier and unresolved
implicit abbreviation parameters; check03 discriminator Decidable synthesis;
check05 scratch audit counter type; check07 unavailable guessed standard
constant names during instance inspection. Checks 02, 04, 06, 08, 09 succeeded.
Audit 06 exposed standard classical Fin-order-law dependencies; a local direct
finite-port BEq removed them, with final source rebuilt and fully audited.
`setup.log` retains initial self-location/environment failures and the successful
version check. No failed log was overwritten by a later success.

Reproduction and full evidence live under the scratch root:
`project/`, `project/AuditBoundaryQueryClosure.lean`, `check.py`,
`check01.log` through `check09.log`, `setup.log`, `roots.txt`,
`named-root-audit.txt`, and `hashes.json`.

## Parent application and next obligations

The new theorem can supply the finite boundary endpoint-coverage premise once
actual source/native owners supply eligible unchanged-view wiring and intact
anchor/demand/direct records. `native_record_correspondence` owns that source
mapping. The primary owns the separate native record-plan skeleton and its
connection to resolved child plans and existing preservation.

The source companion was asked to identify authentic edge classification,
context guards, producer origins, demand boundaries/context/occurrence, and
separate adaptation output views. Its messages identify actual source/native
owners and warn that reference/SCC incidence is not automatically view flow.
This receipt does not certify those source claims; they belong in that leaf's
independently reviewed companion. Native ascription cannot be instantiated as
an adaptation event merely from its endpoint numbers or syntax.

Remaining duties retain their original owners: native acceptance/currentness
and diagnostics, constructor/event lawfulness and finite containment, original
record child resolution and computation contracts, complete Call, contextual
effect licensing/jointness, and full original scoped source reconstruction.
No semantic adoption or production promotion follows from this packet.

Mutual TODO: primary assigns fresh nonauthor review of frozen theorem plus
native map, applies accepted routing output at the record-plan seam, and owns
all shared imports/status/integration. This leaf has no requested extra writes.

**Writes stopped.** All three leased artifacts and the isolated evidence are
frozen for fresh review. No worker or background check remains running.
