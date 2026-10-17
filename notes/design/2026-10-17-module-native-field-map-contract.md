# Module native field map construction contract

Date: 2026-10-17  
Status: conditional source/native construction contract; no code authority  
Sprint: `module-source-family-embedding-20261017`, revision 1  
Parent: original Yulang inference/execution theorem; unchanged A/B claims,
quantifiers, source domain and source/native correspondence  
Source: `my id x = x; my answer = id 0`  
Original conditions closed by this artifact: **0**

## 1. Contract and boundary

This contract specifies the evidence a future implementation must retain or
reconstruct to map the full original module publication/use tuple to native
capture and `FreshUse`. It uses the frozen source-use map and the actual native
producer path inspected below. It does not change a source rule, decide a
missing semantic field, or claim that native row identity is a source
coordinate. There is no compiler or test lease in this assignment.

The mathematical source tuple is the complete original record at the fixed
`B,X,xi,Delta_c,d_id,u_id` indices: declaration and use origins, resolution,
publication/new-or-alias classification, selected final root, provider and
base anchors, every ordinary/logical/event field, binder and dependency
incidences, complete clause operands, guards, alternatives and witnesses.
The table in §3 covers every field class in the frozen map. Its producer column
distinguishes an actual compiler owner of structural evidence from the
source-rule owner that must supply the semantic coordinate. Where there is no
authentic native producer, the coordinate remains an explicit blocker.

For this fixed source the frozen source construction selects `Build(L_id)`,
`FinalRoot`, an actual `ModuleDef` name occurrence, publication before external
use, and a `new` instance on the direct published edge. The original source
embedding handoff constructs that source derivation but remains pending
independent review/adoption. The native route independently confirms the
syntax occurrence, `d_id` resolution, dependency-first publication and
external route. It does **not** authenticate the source rule's `new`/alias
judgment, provider, or complete semantic tuple. `d_x`, the declaration root,
the source-use root and a proposed registered contract root remain distinct.

## 2. Actual source and native owners inspected

Source provenance and schedules are produced by
`candidate_source::Plan` / `ConstraintBatch::emit_candidate_source` in
`crates/yu-solver/src/candidate_source.rs`. For a direct module Name, that arm
retains the occurrence, queues `PendingDefinitionUse { parent, target,
occurrence }`, and schedules `Action::Module`. The collection endpoint pass in
`crates/yu-solver/src/lib.rs` resolves `target` in the complete definition
table and creates `DefinitionUseId`, cause, parent, occurrence, use level,
use component and target-root component. Those are authentic source/provenance
incidences; they are not provider or typing witnesses.

`candidate_scheme::execute_candidate_graph_plan` captures each definition
graph at its publication boundary, stages and publishes dependency-first SCC
members, and clears the live component state after publication. The module
action routes an internal open use or an incoming published use. For this
source, `u_id` is external to `id`'s component and takes the published-graph
route. `route_candidate_graph` recaptures the actual published target root
and frontier for that use.

Capture is owned by `capture_candidate_graph_owned` and `Capture` in
`candidate_scheme.rs`. It records a graph root, boundary/frontier/owned source
regions, structural function nodes, canonical candidate rows, bounds with
orientation and relation, evidence snapshots, effect operand/tail data,
attachment bundles and context payload views. Function nodes retain the four
native value/effect ports. `expand_row` captures only mutable local rows and
their incident native bounds; a nonlocal row stops at its existing identity.
This is a graph of candidate constraints, not the source rule's entire typed
presentation.

`prepare_candidate_fresh_use` creates one use context and source-scope remap,
then maps each canonical candidate row once. Its actual eligibility predicate
is `row.local && level > graph.boundary && !metadata.non_generic`; repeated
canonical source rows reuse the same image, while other rows keep their
representative. It also reconstructs native terms, effect operands/views,
attachment bundles, context IDs, captured relation scope flows/demands and
evidence snapshot IDs. `begin_candidate_fresh_bound` restores bounds using
the saved orientation and creates a transport for the actual use. This is
authentic native behavior. No inspected producer links all these native
records to every original source-rule binder class.

The exact native limitations are also recorded in the frozen source-use map
§7 and local-use retention correspondence: native row eligibility is not the
SRC provenance-based fixed/eligible partition; scope IDs and numeric solver
levels are not source semantic scopes; evidence snapshots are not by
themselves source `EventProof` witnesses; a captured root is not by itself
`FinalRoot` or a provider certificate.

## 3. Field-class producer and ownership map

“Fixed/shared” and “instance-owned” below are source-rule classifications,
not guesses from whether the native endpoint happens to be fresh. The native
side must carry the classification key emitted by the authentic source owner.
Where that owner-to-native link is absent, the class is unresolved and the
contract does not treat a plausible native row as a substitute.

| Original field class | Actual source producer / native owner | Ownership and required map |
| --- | --- | --- |
| Source root, declaration `d_id`, formal `d_x`, occurrences `u_x`/`u_id`, exact resolution edge, rule/arm identity | HIR `LocalSource` is retained by `candidate_source::Plan`; ModuleDef arm queues the actual use; `lib.rs` collection endpoint pass owns `DefinitionUse` | Fixed source identity. Preserve exact origin and edge. `u_id -> d_id` is never replaced by the use root or `d_x`. |
| `Build` child tree, original local-rule signature, clauses and operand telescope | Source rule owner: selected Source Generalize `Build` and its actual `Sig`; native `emit_candidate_source` emits scheduled constraints from syntax forms | Must retain the complete constructor/operand incidence. There is no inspected native `Build` derivation or `Sig`-to-row owner map; exact blocker `SRC-BUILD-FIELD-ORIGIN`. |
| Final root, root provenance and declaration/use root distinction | Source rule owner: selected `FinalRoot`; native source schedule emits `Action::Link` for an unannotated definition body, graph capture starts at a live component root | Root fields stay distinct. Native link/captured root is structural evidence only; no producer authenticates it as source `FinalRoot`. Exact blocker `SRC-FINALROOT-ROOT-ORIGIN`. |
| Publication event, component/member and published-handle identity | Source rule owner: original module publication/lookup/Instance rules; native `candidate_scheme` SCC publication and `DefinitionUse` route | Publication/member identity is fixed for the declaration; use identity is instance-owned. Need a checked bridge between rule event and native publication record; current capture has neither source rule event nor alias witness. |
| `new` versus alias/Mono/Live partition and instance handle | Source rule owner: original source module reference/handle constructors; native module Name resolution and `Action::Module` | `new` is selected by the frozen source proof for this direct published edge. Native scheduling does not encode that classification or a source instance handle. Preserve it as a blocker; do not infer it from row freshening. |
| Provider, allocation/world/lifetime, `Intrinsic`, `Established`, `OneShot` and fixed anchors | Source rule owner: selected `Build`, publication and Instance derivations; native rows, terms and effects are created by source actions / candidate graph | Fixed/shared exactly as in the complete source tuple. No native field names a complete provider tuple or its certificate. Never allocate a provider while constructing FreshUse. Blocker `SRC-PROVIDER-ANCHOR`. |
| `Shared` declaration | Source rule's binder owner and dependency telescope; native canonical row map can preserve repeated endpoint identity | One source binder shared across every incidence, including the use. Repeated native row identity is supporting structural evidence only; source classification is absent. Do not split it per use. |
| Eligible `Desc` and dependency tuple | Source rule owner: SRC two-mode closure/allocation over `Build` and final root; native `Capture::expand_row` and FreshUse canonical row table | Instance-owned only when the source closure proves eligibility; map once per source declaration and remap every dependency under the same instance key. Native predicate `local/level/boundary/non_generic` is not proved equal to SRC eligibility. Blocker `SRC-DESC-PARTITION`. |
| Fixed/ineligible ordinary `Desc`; Internal component references | Source closure and original component/constraint rules; native captured nonlocal rows keep identity, local graph rows carry `RowKey` references | Fixed/ineligible declarations retain their original binder and whole dependencies. Internal references map through the one complete frame, preserving cycles as graph edges; do not unfold cycles or turn an Internal edge into eligibility. |
| `ViewLogic`, challenge, rigid opening and inference existential | Source local rule's dependent binder telescope and guards; native term/function graph and optional `ScopedFlow` | Binder class, order, guard, dependency scope and sharing are source-owned and must remain intact. Native structural term reconstruction has no source binder-kind tag; exact blocker `SRC-LOGICAL-BINDER-ORIGIN`. |
| Event / `EventField`, parent/occurrence and runtime operand | Source event-producing rule; native effect `Contribution`, annotation/support/allowance views, operation occurrence and captured relation | Runtime event origin and actual parent are fixed to the source incidence; effect operand can be reconstructed from retained native endpoint/tail only after an authenticated event key ties it to the source event. A FreshUse must not create a runtime event. |
| `EventProof` / event-owned proof witness | Source event rule and proof sub-telescope; native `bound_evidence`, relation and `EvidenceSnapshot` remaps | Instance-owned only if the source rule says so, beneath its exact event and mapped description dependencies. Preserve witness owner and guard. Evidence snapshot copying/import is not authentication as this source witness. Blocker `SRC-EVENTPROOF-OWNER`. |
| `Check`, `Specialize`, finite proof grammar and local premises | Source rule proof constructors; native bound orientation/relation, context and attachment-bundle retention/restoration | Keep complete grammar, owner, premise incidence and one coherent operand map. Native route restores captured native evidence but has no constructor derivation identifying these source proof nodes. |
| Published/family imported closed parameters | Source publication/family constructor and actual imported operand telescope; native source declarations/imported graph constraints if present | Closed shared family and its original binders remain fixed; map only actual free anchors. Do not insert another family instantiation. No such class is produced by the fixed source path unless the authentic source rule's actual `Sig` requires it. |
| All guards, alternatives, conjunctions, witnesses, root references and operands | Original source rule constructor and complete `Sig`; native capture stores reached candidate bounds and relation evidence | Preserve every branch and all dependencies, not only successful/reached rows. Capture is demand-reachable constraint graph evidence, so completeness of the source presentation is not established by graph reachability. Exact blocker `SRC-ALL-CLAUSE-COVERAGE`. |

This table names the missing owner rather than fabricating an input. The
native `candidate_source::Plan` is the actual source producer for syntax,
occurrences, scope regions and action schedules. It is not the semantic
producer for the SRC typed fields above. The exact semantic owner needed for
those entries is the owner of original module/source rule formation and the
actual rule signature `Sig`; that owner must supply a stable origin key per
field and clause. A missing native tag name alone does not prove that a
reconstruction from authenticated source syntax and derivation data is
impossible.

## 4. Commuting construction required for the whole tuple

Let `T` be the original typed source tuple and `N` the captured native graph
plus its `FreshUse` result. The required construction is a partial, typed map
`Phi_u : T -> N_u` at the original indices. It is defined only when every
source field has an authenticated producer key and every key has exactly one
native retained or reconstructed image. Its commuting equation is:

```text
erase_native( Phi_u(T), native route ) = alpha_u(T)
```

Here `alpha_u` is the complete SRC allocation for the authentic source
`new`/alias branch at `u_id`; `erase_native` forgets only native storage IDs
and transport bookkeeping, not source clauses, binders, guards, alternatives,
witnesses or source-use incidences. Equality is equality of the full typed
presentation up to one coherent binder-label convention. Endpoint equality or
equality of the root term is strictly weaker and does not satisfy this
equation.

For each coordinate, `Phi_u` must do exactly one of the following, with its
source owner and dependency edges recorded:

1. **Retain fixed/shared data:** map original source anchor keys and shared
   binder keys to their unchanged native or sidecar identity. Multiple
   incidences point to the same key. Do not use `FreshUse` eligibility to
   decide this category.
2. **Map instance-owned data:** use the authentic source allocation class
   and complete source key (including source declaration, scope and, for an
   event proof, actual event key). Apply the actual FreshUse row/scope/context
   remaps only to the native coordinate paired with that key. Memoize once per
   key, so repeated incidences remain coherent.
3. **Reconstruct from authenticated retained source:** if a native record
   omits the semantic field, walk the retained original source derivation and
   `Sig`, rebuild its binder/guard/alternative/witness record, then connect
   its operands to mapped native graph coordinates. Reconstruction must
   validate source ownership and all dependency edges; printed names,
   row ordinals or endpoint representatives alone are not authenticated
   inputs.

The source-use map's well-scope and whole-tuple lemmas provide the required
source-side invariant: every image retains its original translated scope and
dependency incidence; repeated Shared incidences stay shared; distinct
instance-owned binders remain distinct; and every clause, guard and
alternative remains incident. For this native contract, prove the same
invariant by checking each original edge `(a,b)` has exactly its mapped edge
`(Phi_u(a),Phi_u(b))` and each source clause's ordered operand vector maps
position-wise. Cycles remain registered graph edges. If any source coordinate
has no owner key or any native endpoint has two incompatible source owners,
`Phi_u` is undefined and the whole-tuple compiler bridge remains open.

## 5. Executable producer/representation plan for a later exact lease

This is a design recipe, not present code authority.

1. At the authentic source-rule formation owner, emit an immutable
   `SourceFieldKey` for each original coordinate and clause. Each key records
   source declaration/use origin, field class, owner rule/arm, parent scope,
   dependency keys, and fixed/shared/instance allocation class. Event proofs
   additionally record actual event parent and proof region. Record the
   original new/alias constructor and selected final-root derivation. This
   must be generated from the actual derivation and `Sig`, not guessed from
   HIR spelling.
2. Carry the keys with the already existing source-origin/use provenance to
   the definition capture boundary. Preserve all field keys even when no
   candidate bound reaches a field. Attach an incidence from each key to its
   native graph node/bound/operand where one exists; permit a sidecar-only
   image when no candidate row represents a logical source field.
3. Run the existing actual `Capture` and `prepare_candidate_fresh_use` route.
   Do not change their row eligibility or candidate publication semantics.
   Retain their output remaps alongside the field sidecar; use typed keys to
   apply remaps only to coordinates previously classified instance-owned.
4. Reconstruct omitted scopes, guards, alternatives, witness binders,
   provider/root links and complete ordered clause operands from retained
   source rule records. Rebuild dependent nodes parent-before-child using
   the source dependency DAG; registered cycles remain references. Keep
   native effect/event operands separate from event-owned logical proofs.
5. Validate totality, injectivity where source binders are distinct,
   equality of shared keys where source sharing is required, new/alias and
   final-root identity, exact source/native clause arity/order, and every
   scope/dependency/event-parent edge. Construct the full `Phi_u(T)` privately
   and publish it only after all checks and the commuting equation succeed.

For `n` total retained source field/clause/edge records and `m` native graph,
remap and operand records, a robust first implementation may use linear key
searches and an explicit cycle-safe scan: `O((n+m)^2)` time, `O(n+m)` private
working/retained space per captured declaration and `O(k(n+m))` retained
per-use sidecars for `k` retained uses. Graph structures are traversed as
finite presentations; registered cycles are never unfolded. This deliberately
accepts higher asymptotic cost for auditable complete matching. If an indexed
implementation is later used, it must retain the same checks and give a
separate collision/identity argument.

Storage includes every `SourceFieldKey`, class and dependency incidence,
source-origin-to-native-key link, sidecar image, and per-use mapping; omitting
logical/event records to save space breaks the bound. Existing native capture
already retains `Graph` and the graph's maps; its `FreshUse` retains row,
term, scope, relation, effect operand, bundle, context and evidence remaps.
This contract adds `O(n+m)` metadata to those existing retained records for
one captured declaration, plus `O(n+m)` for each retained use. Source syntax
and source derivation ownership remain alive or are immutably referenced for
as long as reconstruction is permitted.

Use checked addition/multiplication and fallible reservation (`try_reserve`)
for each sidecar, key table and dependency vector. Keep partial allocations
private and expose no half-map on failure. Resource exhaustion must not be
translated into a source-language typing rejection or a successful partial
certificate. The exact integration behavior on allocation failure must be
specified by the future code owner against the existing availability/error
path before cutover; this packet does not authorize a new rejection boundary,
fallback semantics, retry rule or changed diagnostic. No observable source
behavior changes as part of this representation contract.

## 6. Concrete falsifiers and STOP boundary

The following falsify the construction for a source instance:

- A source key is absent, duplicated across distinct owners, or points to a
  native endpoint with a different source owner.
- One source dependency or ordered clause operand lacks its mapped incidence,
  or an edge changes parent/child scope after remapping.
- Two Shared uses map to different binders, or distinct instance-owned
  binders collapse to one key/image where the source class requires
  separation.
- The actual source constructor is `alias`/Mono/Live but the map labels it
  `new`, or vice versa; new/alias is inferred solely from native row copying.
- A fixed provider, world, lifetime, root or witness is freshly allocated,
  copied per use, conflated with the use root, or replaced by an equal-looking
  endpoint.
- An EventProof is attached to a stale/different event parent, an event
  operand is treated as a description-owned proof, or a logical binder loses
  its guard/alternative.
- A captured reached-bound subset is treated as proof that every source
  clause/guard/alternative was represented.
- A partial allocation failure publishes a record, alters source admission,
  changes diagnostics, or converts unavailable evidence into an answer.

Two deliberately separate tests are required of any later executable bridge:
the frozen single-use source must commute without source-domain changes, and a
logical separation fixture must preserve one Shared witness versus two
instance-owned `ViewLogic` witnesses. The latter is a structural falsifier,
not a counterexample from this fixed program. Existing green candidate
observer checks do not test either whole-tuple equation.

**Exact blocker / STOP:** the inspected actual owners do not produce the
original source rule's stable field keys, `Sig` owner, allocation classes or
event-witness ownership beside capture/FreshUse. Therefore no total `Phi_u`
can yet be constructed from the inspected bytes. Required evidence is an
owner-authenticated producer for `SRC-BUILD-FIELD-ORIGIN`,
`SRC-FINALROOT-ROOT-ORIGIN`, `SRC-PROVIDER-ANCHOR`, `SRC-DESC-PARTITION`,
`SRC-LOGICAL-BINDER-ORIGIN`, `SRC-EVENTPROOF-OWNER`, and
`SRC-ALL-CLAUSE-COVERAGE`, plus the new/alias and publication-event bridge.
The next related in-envelope step is Luna's independent architecture review
of this frozen contract and the exact owner TODOs; any code work requires a
new explicit lease. This does not choose a semantic alternative or close a
theorem gate.

## 7. Reused evidence, direct pins and checks

Reused without promotion: the frozen module source-use map's complete
conditional tuple, source/native owner census and Shared/ViewLogic falsifier;
the original module source-family proof's `Build`/`FinalRoot`/publication/
`new` construction and §7.2 substitution (review/adoption pending); the
previous candidate observer's direct `Name(ModuleDef)` classification and
candidate-only boundary; and local-use retention's valid projection cut.
Rejected as whole-map evidence: endpoint equality, candidate row freshening,
source/native ordinal equality, captured `EvidenceSnapshot` as an
`EventProof`, graph root as source `FinalRoot` or provider, and green observer
assertions. No withdrawn Simple-sub bypass is used.

Direct inspected artifact SHA-256:

```text
tasks/agent-loop/sprints/module-source-family-embedding-20261017.md c78deada22ab326a02045bc0c0dc1c0e723f5aaf52cef81dc699ecda87afd18e
notes/theory/2026-10-17-module-declaration-source-use-map.md bab0392a58451c84e77892c6a88d9eb434bcf9a6995afc80c404e7f29aaa448d
notes/theory/2026-10-17-module-source-family-embedding.md c921db323ef1e1ce0f90465f4c51fbd5c6708ac84213bd670f8fe5d46fc4ba99
tasks/agent-loop/inbox/20261017-module-source-family-embedding.md 456733314dccc0e9cb08d574911e3c069099f3ceaf03c4d6f8a21021b5639474
tasks/agent-loop/sprints/module-use-source-map-and-provisional-observer-20261017.md e575fed444457c34bc229c5f10ca6510d8fb85d9e4ecc3f582f485d72952ec6e
tasks/agent-loop/inbox/20261017-module-call-provisional-observer.md 4d4f33a692c4322726f0b6e4d347e5b1e31c702da7171fecc6a18f42ccfaaa07
notes/theory/2026-10-17-local-use-retention-applied-correspondence.md 198046b6eb398734cf657ab03f05e171f8be568c1e8feb31115b9adc46d5f1ff
notes/design/2026-10-08-native-projection-public-export-definition.md aed6ef63b01f555a5f2804f87a599167c1a30fa999afc0b9d9f11b8ae974a919
crates/yu-solver/src/candidate_source.rs efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38
crates/yu-solver/src/candidate_scheme.rs 52b7281946de755003ee8f3b3d18cbc2df6cc6db5566b4e5ecf391b74a92640a
crates/yu-solver/src/lib.rs 2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f
```

Checks performed: read-only policy/contract/source/handoff/code inspection and
direct SHA-256 checks above. No tests, builds, Git, code changes, executable
probe, or scratch files. Requested runtime role/model/effort: implementer,
Luna / `gpt-6-luna` high. Observed effective model and effort: UNKNOWN; the
runtime exposed no session metadata. The initial no-shell boundary delayed
inspection until the primary clarified read-only shell access. Resource cap:
480 seconds; exact active telemetry unavailable, so charge the full 480-second
cap conservatively. **STOP:** only this note and its exact paired handoff were
written; no descendants or other output paths exist.
