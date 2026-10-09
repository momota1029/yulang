# Finite live value/effect graph extraction and fresh graph construction

Date: 2026-10-10
Status: independently reviewed structural theorem; bounded test-only core executed
Baseline: `eed17418cf92bc3fd80fdbd3381a307f74d2bd1b`
Authority: current Simple-sub correction; existing source/inference contracts
Scope: immutable complete active scalar graph snapshot and all-fresh graph construction at unchanged levels
Production/API adoption: none
Review: [independent proof and implementation review](../progress/2026-10-10-kind-qualified-graph-review.md)

## 1. Constructive result

The actual live solver already has separate value/effect rows, both directions of their bounds, and four-port Function terms. Its current F5 exporter walks only the value children and exports effects as Bottom/Empty. This note constructs a finite alternative research representation directly from the live tables: **every value and effect row, every admitted typed scalar pair key, declared actual root handles, and their complete actual term-child closure**. All rows and admitted pair keys are seeded, including records disconnected from the chosen result. No source eligibility classification or complete-residual link inventory is a premise of this core construction.

The main theorem gives an effective, lossless snapshot of that precisely specified complete active scalar graph projection and a two-pass all-fresh graph constructor with an effective inverse. Rows use a kind-qualified identity; a row's positive and negative occurrences use the same memo entry. All four Function children, bound-list direction and position, shared term-record identities, pair keys, levels and row metadata survive. Bound cycles terminate because rows are allocated before their references are copied.

The theorem concerns an immutable graph, not restored operational state of an entire `InferenceSession`. Actual term constructors intern equal nodes; they are therefore separated from the immutable nominal term records used by the inverse. A later realization into the actual term arena may merge equal terms while retaining the distinct immutable record identities.

An arbitrary complete residual can be retained with its original telescope and decoder. That proves preservation of its representation and original reference incidence. It does **not** prove semantic naturality under raw nominal renaming, lawful source fresh use, or transport of an arbitrary predicate's strategies.

A small code-derived deferred-demand graph demonstrates the owning F5 failure route. It contains a genuine unknown-formal scalar Function upper bound and a reachable symbolic effect row; no concrete provider or immediate satisfiability proof is required to build it. An additional actual scalar Function comparison produces a direct effect edge which the new representation retains. The bounded test-only core and this witness have now been executed as recorded in the review; no original complete-source Call counterexample is claimed.

## 2. Precisely specified raw graph projection

### 2.1 Input and successful physical scope

Freeze a finite session S outside a mutating operation. The synchronous typed worklist is empty, and no read races with term allocation, row mutation, generalization, route commit or rollback. The graph projection below is called `RawGraph(S)`; the name does not mean every field of the physical session.

Required validation is finite: parallel row-table lengths agree; every referenced ordinal is in the appropriate kind's table; actual term handles belong to the current branch or immutable prefix; every Function port has its prescribed kind and polarity; structural term references are acyclic; and direct row edges have paired lower/upper incidence. Unsupported or malformed records cause explicit construction failure, never omission or approximation. The theorem is conditional on these checks and successful fallible allocation/identity operations. It does not assert unlimited support or a new availability policy.

The actual supported term variants are the exhaustive `TermView` variants in `crates/yu-solver/src/term.rs:170–194`: Leaf, Component, LiveVariable, PositiveBottom, NegativeTop, NegativeBottom, PositiveFunction and NegativeFunction. Component recipes remain nominal component records, with their actual `live_components` translation retained separately. A collected component position is never treated as a live ordinal.

### 2.2 Identities

Use a constructor-owned snapshot identity s and define:

```text
RowKey(s,k,n)               k = Value or Effect; n = original dense ordinal
TermKey(s,t)                t = actual original opaque Term handle
PortRef                    polarized RowKey | tagged atom | TermKey
BoundSlot                  (RowKey, Lower/Upper, original list position)
```

The snapshot identity distinguishes sessions; it is a research wrapper identity, not a source provider identity. Kind is indispensable: Value(0) and Effect(0) are distinct keys. Polarity belongs to a row occurrence, not to the row key. One effect row in a negative argument-effect port and a positive result-effect port has one identity.

A `TermKey` identifies an original committed term record, even when another committed record has the same shape. Immutable graph terms are indexed records; reconstruction does not hash-cons their nominal identities.

### 2.3 Exact fields captured

For **every** value row, copy:

- `bounds[n].direct_lower_rows` and `direct_upper_rows`, in their original order;
- `exact_non_variable_lowers` and `exact_non_variable_uppers`, in original order;
- `has_int_positive_lower`;
- `value_levels[n]`;
- `value_metadata[n].origin` and `non_generic`.

For **every** effect row, copy the same four list fields from `effect_bounds[n]`, plus `has_bottom_lower`, `has_empty_upper`, `effect_levels[n]` and both effect metadata fields. Exact value endpoints preserve BottomPositive, BottomNegative, TopNegative, IntPositive, IntNegative, ValueRow, PositiveFunction and NegativeFunction tags. Exact effect endpoints preserve BottomPositive, EmptyNegative and EffectRow tags. Graph port references carry the kind and expected polarity implicit in those actual endpoint tags.

Copy every `live_components` entry as its original component position together with its kind-qualified row reference. Copy `parameter_live_base` as an original startup datum; any retained parameter recipe incidence also has its actual value-row reference. Roots are optional annotations on the whole snapshot, not a selection that removes other rows or terms.

For every actual term in the descendant closure of the declared roots, bound endpoints and admitted pair endpoints, copy its `TermKey` and exact variant:

```text
Leaf(tag)
Component(original ComponentId)
LiveVariable(RowKey, original polarity)
PositiveBottom | NegativeTop | NegativeBottom
Function(original polarity,
         argument TermKey, argument_effect TermKey,
         result_effect TermKey, result TermKey)
```

The complete Function sort table is:

| Port | Positive Function | Negative Function |
|---|---|---|
| argument value | Value negative | Value positive |
| argument effect | Effect negative | Effect positive |
| result effect | Effect positive | Effect negative |
| result value | Value positive | Value negative |

Copy the **key of every entry currently present in `typed_pairs`**, including already-completed pairs and pairs with no row support. A value pair key copies both `ValueEndpointKey`s; an effect pair key copies both `EffectEndpointKey`s. Preserve each original pair key as its immutable record identity. The exact core observation boundary is these admitted pair keys, not their diagnostic/cache payload. A HashMap's physical iteration order is not a graph field; a deterministic record order may be used.

The actual memo payload is concrete and deliberately outside this observation: `TypedPairMemo::Effect`, or `TypedPairMemo::Value { children, direct_witness, completion }`; children are ordered `(CanonicalValuePairKey, optional FunctionField)` diagnostic edges, and each `DiagnosticWitness` has terminal pair, error-kind tag, distance and optional first field. `DiagnosticCompletion` is Pending or Complete(optional witness). Those fields matter to diagnostic completion/continuation but are not needed to preserve this entire active scalar-constraint graph. No exact payload/cache restoration is claimed.

### 2.4 Actual term closure, without whole-arena enumeration

Construct the term seed list directly from actual handles:

1. every caller-declared actual root handle;
2. every PositiveFunction/NegativeFunction handle in every exact row bound;
3. every such handle in every admitted scalar pair endpoint.

Visit each actual handle with `store.term_view`, mark it before traversing descendants, and enqueue **all four** children of each Function. Store every visited variant, including component recipes and live leaves, with its original opaque handle. Extrema/int endpoint tags that occur without term handles remain tagged graph atoms; no nominal term handle is manufactured for them.

The validated structural DAG and finite initialized actual store make this closure finite. References never require guessing an ordinal range, looking through alignment gaps, reading uninitialized page slots or inspecting unused arena nodes. Current `term_view` supplies everything needed; no `term.rs` enumeration helper or new API is required. A root may be disconnected from the bound graph; it is retained because it is itself a seed. Terms disconnected from every declared root, bound and admitted pair are intentionally outside this observation boundary.

### 2.5 What is deliberately outside RawGraph

This projection does not capture unused term-arena nodes, typed-pair diagnostic payloads, interner/page-directory state, or source HIR, registered definitions/SCCs, source binding ownership, source description eligibility, arbitrary complete Call evidence, `ConstraintStore` receipts/facts/provenance/canonical indexes, errors and reported-error incidence, route state, generalizer caches, public routing, counters, heap capacities or allocation ledgers. It also does not restore extrusion marks/generation/stack or call-local diagnostic scratch. Those omitted fields have actual operational responsibilities.

For example, the private `RouteCheckpoint` at `lib.rs:8092–8160` captures many additional fields, while `ConstraintStoreCheckpoint` captures receipt, fact and provenance state. The theorem here is **not** an inverse of either checkpoint and does not claim a complete operational continuation.

## 3. The complete active-graph snapshot constructor

Let `J_S` be the finite record universe in §2. Every row, every admitted scalar pair key and every declared actual root is a seed. All terms reachable from their actual reference-bearing fields are retained. Thus a symbolic effect row with no bounds and a scalar pair disconnected from any selected result are still stored, without requiring unused arena records.

### 3.1 Extraction algorithm

1. Freeze and validate S as in §2.1. Enumerate every value/effect row and admitted typed pair key. Build and validate the actual term-child closure from the roots, bound endpoints and pair endpoints.
2. Build injective dictionaries from each original typed row key and actual term handle to a dense immutable graph record identifier. Preserve an inverse dictionary for each.
3. Allocate placeholder immutable record slots for the entire finite universe before writing reference-bearing fields.
4. Fill row records, translating every ordered bound endpoint through the dictionaries. Fill each term record with all original children. Fill each pair record with its original typed endpoint key. Translate `live_components` references and root annotations.
5. Validate that every translated reference resolves with its original sort and that each original direct row edge has both paired physical lists. Publish the immutable graph only after all slots and checks complete.

The dictionaries use kind-qualified row keys. An ordinal-only set is insufficient. The original term table is used, rather than the current F5 tree walker: that walker visits only argument/result and emits an ordinal-only `TermRow` (`f5c_tree_analysis.rs:175–200`). Merely visiting two more children without correcting its key would introduce a value/effect collision.

Row cycles cause no recursive row allocation. Term structural cycles fail validation; recursion through live row leaves is valid and remains finite.

### 3.2 Theorem RAW-EXTRACT

**Statement.** For a finite validated frozen S and declared actual root handles, successful extraction terminates and constructs an immutable graph K with effective encoding and decoding maps such that:

- K contains exactly every logical record of `RawGraph(S)` and its original reference incidence;
- all original record identities, ordered row slots and all four term ports are preserved and reflected;
- decoding K returns `RawGraph(S)` exactly, and re-encoding a constructed K returns that K;
- no unconstrained row, retained duplicate-shape nominal term or row-free admitted pair is discarded.

No source eligibility, Q/anchor partition, complete residual inventory, satisfying assignment or concrete callable is a premise.

**Proof.** Every enumeration ranges over a finite initialized table. Term references are finite and checked acyclic; traversing them with a marked worklist terminates. The dictionaries assign a new dense identifier once to each tagged original key. Their stored inverse makes them bijections onto their images; differing row kinds cannot collide.

All graph slots are allocated before references are filled, so any cyclic row reference has an existing target. Each row list is copied position by position. Translating then decoding its endpoints is identity by the dictionaries' inverse equations; therefore exact/direct lower/upper list sides, positions and repeated references are identical. Metadata, levels and flags are copied fields. Each term variant retains its tag and original reference-bearing children; field induction and the inverse term dictionary recover the original four-port DAG. Component identifiers are copied as nominal labels, while their live translation returns the identical original row reference. Each admitted pair key decodes endpoint by endpoint, with its Value/Effect tag unchanged. No completed diagnostic witness or memo payload is inferred or copied.

All seeds are retained, so there is no reachability-based elimination. Validation ensures no reference to a missing record. Applying the inverse dictionaries fieldwise therefore returns every original record and the same complete logical graph projection. Applying the forward dictionaries again returns the constructed record IDs and fields. Finite loops and successful finite allocation establish termination. No phase examines a solution, provider or admission outcome. QED.

This is an exact structural snapshot theorem. It is stronger than preserving the printed root type and narrower than restoring the physical session.

## 4. All-fresh construction with one typed row memo

### 4.1 Constructor

Choose a new research frame identity i. Every row is fresh in this core constructor; there are no anchors or source template eligibility inputs. Construct its image as `(i, original kind, original dense ordinal)`. The fresh frame tag distinguishes it from the original snapshot and every other new frame; the pair `(kind,ordinal)` makes the map injective within a frame. Keep its original numeric level and metadata as fields of the new immutable graph.

Use one map for the entire frame:

```text
M_i : original RowKey -> fresh graph RowKey
```

The key excludes polarity. A row occurrence copies its original polarity and uses M_i's row. In particular negative and positive effect ports refer to one fresh effect row.

Use a separate nominal term-record map:

```text
N_i : original TermKey -> fresh immutable TermRecordId
```

Enumerate the finite immutable term records once and assign `(i, term-record enumeration ordinal)` to each. Distinct original records receive distinct enumeration ordinals, giving a constructive injection even for equal shapes. Again allocate all identities before writing records. Then copy the complete graph fields through M_i/N_i. Component labels and `parameter_live_base` remain original recipe/startup labels with their mapped row incidences in the fresh graph; they do not become new source recipe IDs. Bound lists and every admitted pair key use the same maps. Root annotations use their mapped references. Original flags, metadata, levels, term tags and port labels remain unchanged.

This construction can be purely immutable. For a bounded helper, new row identities may also be obtained by successful actual `fresh_value_at_level(original_level)` / `fresh_effect_at_level(original_level)` calls in a dedicated session, then used to label the immutable records. The runtime allocator initially writes `origin=Fresh, non_generic=false`; the snapshot's original metadata is a preserved immutable field, **not a claim that those allocator-created rows already contain the copied metadata/bounds**. Installing those fields is a further operation.

### 4.2 Theorem RAW-FRESH

**Statement.** Given K from RAW-EXTRACT and successful finite identity/capacity operations for the explicit frame-tagged enumeration above, the all-fresh constructor terminates and returns K_i such that:

1. Every row has exactly one fresh image of the same kind, irrespective of polarity or number of occurrences.
2. Equality of original row and term-record references is preserved and reflected within K_i.
3. All four ports, row cycles, ordered bound slots and paired direct-edge incidences remain exact.
4. Effective inverse maps on M_i/N_i decode K_i to K.
5. Two independent frames can allocate disjoint row/term-record image sets; an alias reuses the same maps and graph and allocates nothing.
6. Original levels and metadata are unchanged immutable fields; no extrusion or eligibility step is invoked.

**Proof.** The first pass constructs one frame-tagged image per original typed row and per enumerated term record and stores its map entry before following any references. Distinct row keys differ in kind or ordinal, and distinct term records differ in their enumeration ordinal; hence these constructed maps are injective and have explicit inverse dictionaries. Kind-preserving allocation proves item 1 and prevents collisions between value/effect ordinals. A polarized live leaf copies its polarity but uses that one M_i entry, so differing polarities do not split the row. Injectivity gives both directions of equality for row and nominal term references.

The second pass traverses finite records and copies each field using the total maps. Bound cycles terminate because map lookup does not recursively allocate a row. Function reconstruction copies its four labeled fields individually; a shared child record is looked up in N_i and never independently reallocated. Both physical lists for a direct row edge use the same M_i endpoints, preserving their paired incidence. The same fieldwise argument applies to admitted pair keys. Applying inverse maps to every copied reference and identity leaves scalar fields unchanged and returns K exactly. Disjoint allocations establish item 5; alias reuse follows directly from reusing the same maps. Neither pass writes numeric levels or consults satisfaction. QED.

The all-fresh plan is a finite raw graph operation, not a theorem that all rows are source-generalizable. Inference rows, ordinary source Desc declarations and logical proof/witness binders remain different objects.

## 5. Actual term interning and runtime realization

The exact inverse above is on **immutable term records**, not on actual reinserted `Term` handles. This distinction is required by inspected code.

`BranchTermArena::intern` (`term.rs:1058–1095`) looks up `positions[TermNode]` and returns the previous Term for an equal node. `live_variable` invokes this interner with `(kind,polarity,ordinal)`. Positive/negative Function constructors validate all four endpoint sorts before invoking it (`:1122–1182`). Repeating a same-shape construction in one branch can therefore return the same runtime handle.

The immutable prefix and branch have separate lookup/storage responsibilities, and branch interning only consults its branch `positions`. The lower-level `push` can also allocate a node without that dedup lookup. Thus it is unjustified to assume that **arbitrary distinct committed original nominal handles** will have distinct images when reconstructed solely through the standard interning constructors. The graph snapshot retains those original handles and its own distinct TermRecordIds even if their shapes are equal.

A runtime realization map H_i can be constructed after row identities exist:

- realize a LiveVariable record by `live_value_term` or `live_effect_term`, using M_i and its original polarity;
- realize leaves/extrema by the corresponding actual constructors or collected leaf handles;
- realize Function records in structural DAG order using all four realized children;
- retain Component records and their mapped live translation as immutable recipe references; they are not ordinary polarized Function children accepted by `require_function_children`.

The result is a map from every immutable term record to a well-sorted runtime endpoint representation. H_i may be many-to-one. The original nominal inverse remains attached to the immutable record ID, so information is not recovered from H_i alone. No actual term handle is forged and no brand check is bypassed.

**Lemma REALIZE.** For validated live/extrema/Function records and a kind-preserving actual fresh-row map, successful runtime constructor calls produce well-sorted terms with the specified four children and live row occurrences. Repeated original records can share one runtime term, while immutable K_i still retains their distinct original nominal identities.

**Proof.** Live variable construction writes precisely the kind, polarity and ordinal of its map input. Each extrema constructor has the fixed appropriate sort. Induct on the finite Function DAG: all four realized children have their required sorts by induction; `require_function_children` checks exactly those sorts and current lineage before interning. The returned term is the requested Function shape, either previously interned or newly inserted. Shape reuse cannot change a child's row reference. Maintaining H_i alongside, rather than replacing, N_i leaves the immutable inverse untouched. QED.

This lemma does not prove exact runtime term-arena nominal round-trip, copied interner state, operational memo continuation or production scheme instantiation.

## 6. Dependent residual and scope representation

Let an arbitrary complete residual R with its original telescope tree T be available. Retain R/T **unchanged**, with all original proof choices, evidence occurrences, quantifier order, scope paths and dependency references. Attach K/K_i and their inverse dictionaries; do not replace R by a scalar Function constraint or a residual reconstructed from printed ports.

No complete link inventory is needed to build the entire active scalar graph snapshot. If original construction-owned links from R to raw row/term records are available, copy those link occurrences with their original scope/dependency maps and attach both their original reference and mapped graph-record reference. Without such links, retain R/T as the original opaque object; no proper residual-specific subgraph or original-to-graph semantic correspondence is claimed.

**Theorem SCOPE-RECORDS.** Copying the original T/R and their available original reference records alongside the graph decoder preserves every original telescope/dependency incidence and binder order. Decoding any linked graph record returns its original reference. This is a representation theorem, independent of whether R is satisfiable.

**Proof.** The constructor copies T/R and scope references without moving a node. At each binder, its original parent, declaration order, telescope and dependency references are identical. At each available linked occurrence, RAW-EXTRACT/RAW-FRESH's inverse returns its identical original row/term reference. Induction over the finite original telescope representation proves unchanged dependencies and paths. A finite registered recursive scope schema keeps its nodes/references without expanding or changing their keys. No witness is selected and no existential/universal is exchanged. QED.

For a **decoded representation** one may evaluate R on its original arguments obtained through the stored inverse. Its result is identical to the original evaluation because the arguments are literally the original ones. This is not semantic equivariance of R. For example an arbitrary nominal predicate may assert that a row key equals a particular original key; applying that same predicate directly to a fresh key can change its truth. The decoder preserves the old argument; raw renaming does not justify calling the new argument lawful or equivalent. Likewise this note proves no transport of arbitrary original strategies into a new source frame merely by renaming rows.

Source Generalize's SRC, SRC-J, GS and GC retain their actual local-rule, classification and allocation premises. They distinguish eligible Desc, inference existentials, fixed external Mono/Established fields, Internal relation references, Shared, ViewLogic, EventField and EventProof binders. The raw all-fresh graph supplies none of those distinctions automatically. Its decoder is useful retained representation data; it is not a new derivation of Source Generalize or a joint satisfying strategy.

## 7. Optional partial incidence extraction

The complete active-graph snapshot theorem closes the primary construction without source inputs. A useful stronger side construction is possible for **supplied construction-owned raw graph seeds**, explicitly distinct from source eligibility.

Build reverse incidence for every bound and typed pair. A direct row edge has support on its two typed rows. An exact bound on owner r with endpoint a has support `{r} union Rows(a)`, where Rows visits all four Function children. A pair has support `Rows(lower) union Rows(upper)`, retaining its original typed pair key. These supports form records for reachability; they are not converted into extra pairwise inequalities. Also retain original term-parent and component-translation references. Row-free pairs require explicit record ownership seeds; they cannot be recovered from empty support.

Starting from the supplied records, mark their referenced records and incident rows/constraints until closure. A reverse index allows an effect row with no bounds to find an incoming exact Function bound on a value-row owner. Forward effect-bound traversal alone misses that relation.

**Lemma PARTIAL.** A finite marked worklist computes the least reference/incidence-closed raw subgraph containing those seeds. Its record inverse is exact by the same fieldwise copying proof as RAW-EXTRACT.

**Proof.** Every finite record is newly marked at most once, so the worklist terminates. Processing a record enqueues all successors specified by the closure rules, proving closure at termination. Any closed set containing the seeds contains each discovered successor by induction on discovery time, proving leastness. The dense inverse remains injective on the selected original keys. QED.

This lemma does not prove that omitted global constraints may be erased, that an opaque residual's references have been discovered, or that connected rows are all fixed or all eligible source descriptions. The unchanged complement remains part of the environment, or use the complete active-graph seeding of the core constructor. Its cost is bounded by the finite records and materialized support incidence, not automatically by term-node count when shared DAG support sets are expanded.

## 8. Code-derived F5 witness

### 8.1 Deferred unknown formal

In a dedicated session allocate `r:Value`, `alpha:Value`, `beta:Value`, `e:Effect` at the same positive level ell. Construct through the actual session methods:

```text
D− = NegativeFunction(Int+, BottomEffect+, e−, beta−)
L+ = PositiveFunction(alpha−, EmptyEffect−, BottomEffect+, beta+)

submit alpha <= D−
submit L+ <= r
```

The actual `constrain_live` fallback handles both row/Function pairs. It stores D− as alpha's exact upper and L+ as r's exact lower. `extrude` reads all four children, but same-level rows are not aged. Alpha has no existing lower bound, so submitting the demand performs no concrete provider comparison and no satisfiability query.

The F5 positive-root walk from r expands its exact lower L+. Its outer effects are accepted extrema. Its negative argument alpha expands alpha's exact upper D−. At `EnterTerm(D−)` the result effect has Negative polarity. `pure_function_effect(e−,Negative)` inspects the actual EffectBounds row and returns `has_bottom_lower && has_empty_upper`, both false. The walker sets `invalid_effects`, and the actual raw-forest/generalization branches reject with `IdentityExhausted` (`f5c_generalization.rs:6440–6468, 7641–7670, 8691, 11522`).

This is a code-derived owner route, now also exercised by the bounded Rust probe. It is not an original-source counterexample or a demonstrated complete Call failure. The four rows preserve distinct result/root/formal/effect geometry; absolute graph-size minimality is not claimed. A smaller isolated Function graph can reach the effect guard but lacks the deferred unknown-formal demand.

### 8.2 Actual scalar effect incidence

Allocate another effect row q at ell and construct:

```text
P+ = PositiveFunction(Int−, EmptyEffect−, q+, Int+)
submit P+ <= alpha
```

The real lower-bound insertion replays alpha's D− upper. The four scalar children scheduled by the actual Function-pair branch are:

```text
Int+ <= Int−
BottomEffect+ <= EmptyEffect−
q+ <= e−
Int+ <= beta−
```

`apply_effect_task` stores q in e's direct lower list and e in q's direct upper list. This derives an actual effect edge from actual four-port scalar Function comparison; it is not a postulated source rule. RAW-EXTRACT/FRESH preserves both lists and all incident effect ports.

The complete original Call obligations remain distinct: receiver, whole argument, entry policy, returned callee, provider/world correlations, protection, result images, admission, licensing and future suffix evidence are not supplied by these scalar tasks. At the pinned baseline, the candidate collector constructs Apply demands with Bottom/Empty ports and discards child effect endpoints (`shadow_apply.rs:949–965`); it does not emit the symbolic e version here. The later private graph-mode [source effect constructor](../progress/2026-10-10-successor-source-effect-flow.md), committed at `280d399e4e7e1ddcaacf2c1c6d8cf882ec88dc57`, retains child effect components and a fresh invocation row. That source/graph implementation is a separate correspondence target; it does not change this legacy F5 witness or turn this manually constructed graph into an original complete Call derivation.

If Bottom <= e <= Empty is added, the F5 guard can pass, but its sink still emits effect constants rather than the original effect row/sharing. That is a structural information-loss observation. It is not by itself a semantic counterexample to the pure scalar fragment, where extrema bounds may identify the effect values.

## 9. Exact bounded test-only implementation recipe

The primary owns executable work. A small helper can implement the core theorem without new public APIs or production routing:

1. In a dedicated test module, define typed `ResearchRowKey`, immutable `ResearchTermId`, RowRecord, TermRecord and an admitted pair-key record. Capture every actual value/effect row and every key of `typed_pairs`, with the actual `live_components` translation and declared actual roots.
2. Seed actual term handles from all roots and reference-bearing bound/pair endpoints. Build their complete four-child closure using `store.term_view`, preserving original opaque handles and detecting malformed structural references. No term-arena enumeration or implementation edit is needed.
3. Validate kinds and references, assign immutable graph IDs and copy the exact §2 fields. Record the active scalar graph snapshot; do not call it a cloned operational session or diagnostic cache.
4. Freshen all rows with one typed M and all immutable term-record identities with N. Keep levels unchanged. Decode every record and compare with the original logical snapshot, including ordered row-list slots, all four ports and every admitted pair key.
5. Optionally realize live/extrema/Function records using actual session constructors. Keep immutable term record IDs separately when interning returns an existing runtime handle. This check is well-sorted realization, not nominal actual-term round-trip.
6. Construct §8.1 and assert **both** the causal `invalid_effects` flag from the reached D− effect guard and the returned `IdentityExhausted` at the actual cfg(test) boxed `F5cGeneralizer::build(r)` API (`f5c_generalization.rs:10706`), which calls `build_inner_work` and its `invalid_effects` check at line 11522. Add §8.2 and inspect actual effect direct lists. The code-derived claims become executed evidence only after this probe passes.

Discriminating cases are: equal V/E ordinals; repeated effect row across opposite polarities; e->q->e cycles; shared nested Function term; equal-shape distinct committed term records; disconnected unconstrained effect row and row-free admitted pair; two independent fresh graphs plus an alias; and reverse-incidence partial extraction from an effect endpoint. Mutations dropping kind, keying M by polarity, traversing only two ports, using only forward effect bounds, or reconstructing nominal term IDs from runtime interned handles must fail the corresponding check.

For an attached residual fixture, compare original scope paths, quantifier order and dependency/reference records after decoding. A nominal-sensitive predicate should demonstrate the distinction between decoded original evaluation and unsupported direct fresh-key evaluation.

Copying bounds into a session while clearing its typed pair memo is not exact restoration: later replay can append duplicate physical list entries. Even separately copying the §2.3 concrete memo payload would leave omitted store receipts, errors, route state, scratch, counters and ownership ledgers. This note claims no complete solver continuation; establishing one requires the actual additional state and invariants or a separately proved replay policy.

## 10. Remaining scope and dependency snapshot

This independently reviewed note closes a proposed finite constructor and its structural proofs: complete active scalar graph extraction, exact nominal-record round-trip, kind-qualified all-fresh graph construction, well-sorted runtime term realization and original telescope/reference representation. It proposes no source-local rule resolving f, no immediate satisfiability condition and no scalar replacement for a complete residual.

Open extensions include mixed anchors, actual Generalize eligibility/placement, source row/declaration links, original complete Call formation, complete residual solving, source lawful fresh use, unequal-level extrusion correspondence, fresh-use level changes, structured nonempty effects, protection operators, operational session continuation, public formatting and production adoption. Independent mathematics and specification review passed. Four executed tests cover the core immutable graph implementation and the F5/effect-edge witnesses; REALIZE, PARTIAL and an attached complete residual are not implemented by that helper.

Pinned Git blob dependencies:

```text
ae950c0c3080fbbb5030d5bd8018b3ba01110e6e  crates/yu-solver/src/lib.rs
001ffd3022b2fad0d7d67e0a853aaeb83db00b12  crates/yu-solver/src/term.rs
64d939d133739ef786d2bfb08187af00f668933c  crates/yu-solver/src/f5c_generalization.rs
3d5e0d36eebd54273728d02706d50b6b4a5bb339  crates/yu-solver/src/f5c_tree_analysis.rs
485b0c632658789919ac99c196fc32e3d787fc2f  crates/yu-solver/src/shadow_apply.rs
f7cd4e957d85ad5f1e94ae9ea3331dfaf1dcaae9  notes/theory/2026-10-08-source-generalize-definition-and-proof.md
f4668026a85965fa6bed3d90d6a16a9d366253f8  notes/theory/2026-10-10-simple-sub-complete-bound-accumulation.md
```

The later inspected term.rs hash `6779b26dfd5a655558f407a8691b0055cf3d4cc1` differs from the pinned blob only by the primary's local deprecation-warning attribute on the existing atomic brand allocator; its term interning/lookup/constructor behavior is unchanged.

Verification: bounded owner reads and read-only baseline hashes; no Cargo/build/test/probe executed by the producer. The artifact is exclusively this note; no implementation, authoritative records or theory statuses were edited.
