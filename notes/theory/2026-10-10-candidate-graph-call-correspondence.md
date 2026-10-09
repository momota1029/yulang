# Source-generated candidate graph capture, replay and fresh-use correspondence

Date: 2026-10-10
Status: independently reviewed mathematical construction; two actual source fixtures executed
Scope: actual nonshipping candidate source graph and logical scalar replay
Production/API adoption: none
Review: [independent construction and execution review](../progress/2026-10-10-candidate-graph-call-review.md)

Algorithm baseline: `21504b7952a1d39fedb3fe6e660721222f4da86a`; source-flow delta revalidated at `280d399e4e7e1ddcaacf2c1c6d8cf882ec88dc57`. The candidate graph owner is unchanged between these pins. Governing boundary: the user's current deferred Simple-sub correction and [question reassessment](../progress/2026-10-10-simple-sub-question-reassessment.md). Source Generalize is used only to distinguish the semantic boundary; its strategy or completeness hypotheses are not invoked. This is a research theorem about existing constructors, with no new source rule or production adoption.

Pinned implementation blobs: `candidate_scheme.rs` = `67ae0bb8c5915d776d7b3323aa64715dae976b51`; `lib.rs` = `2f262f656da5c51babbed15a5ba6f5a0116ac0c2`; `shadow_apply.rs` = `8ab2f15e4cd8d41aece4d821319f77469eae389d`.

## Result

The new algorithm admits a constructor-derived theorem for **the all-local rooted closure that its actual capture computes**, followed by actual per-use reconstruction and scalar replay. Its premise is a finite well-formed actual inference session and a definition root, not a supplied completed graph, residual inventory, successful source satisfaction query, or solved provider. For the actual candidate's supported empty-import HIR envelope, locality follows from startup and route construction (§2.1), and `invoke f = f 1` now emits genuine symbolic invocation-effect incidence (§2.2). The theorem proves four-port and kind preservation, one shared fresh map, row-cycle preservation, finite termination, and exact submission of the renamed retained logical constraints plus the receiving root constraint. A code-derived replay calculus factors through that map. It does not prove erasure of the uncaptured complement, Source Generalize, complete Call, or exact physical solver-state round-trip.

No necessary edge loss was found in that all-local forward closure. The mixed-anchor extension is concretely limited by skipped anchor direct adjacency. That observation is not promoted to an admitted-source counterexample: current startup/fresh rows are level one with `non_generic=false`, and the code-derived tests proposed below need no anchor seam.

## 1. Owning algorithm and entry route

The direct owners at the algorithm baseline are (the later `lib.rs` additions shift these positions by 14 lines; `candidate_scheme.rs` is identical):

| Responsibility | Actual code |
|---|---|
| Candidate entry and source preflight | `shadow_apply.rs:74–130`, `CandidateInference::solve` |
| Rooted capture, interning and local classification | `candidate_scheme.rs:133–518` |
| Anchor dependency check | `candidate_scheme.rs:519–539` |
| Dependency-first definition publication and incoming routes | `candidate_scheme.rs:573–643`, `execute_candidate_graph_plan` |
| Actual per-use row allocation, structure, replay and root route | `candidate_scheme.rs:644–822` |
| Fresh row levels and metadata | `lib.rs:9836–9897` |
| Typed worklist and memo | `lib.rs:11385–11556`, `constrain_live` |
| Value/effect bound insertion and transmission | `lib.rs:11179–11371`, `12400–12628` |
| Four Function child decomposition | `lib.rs:11492–11546` |
| Actual incoming route transaction and dispatch | `lib.rs:15027–15043`, `15247–15255` |
| Fact/provenance and final root constraint | `lib.rs:15408–15486`, `route` |
| Interning and four-port constructor checks | `term.rs:1058–1182` |

`CandidateInference::solve` at `280d399e` uses `ConstraintBatch::collect_candidate_mode(hir,true,true)`, rejects source-internal SCC uses, starts graph mode on the actual `InferenceSession`, and calls its actual `run`. The candidate SCC plan captures the actual `live_components[root_component].ordinal`, stages every graph in the component before exposing any, then invokes existing `route_incoming`. Graph dispatch is inside `route_incoming_inner`, therefore inside `with_route_transaction`; this is not a separate model or a disconnected raw graph helper.

The graph itself is indexed nodes, kind-qualified row keys, and a bound sequence. Its Function ports are ordered `[argument, argument_effect, result_effect, result]`. The two effect children are first-class nodes. Local classification is exactly `level > 0 && !metadata.non_generic`, at the existing module boundary zero. Origin and ordinal are not used to decide locality.

## 2. The closure is generated from the session

For a fixed actual session at capture time, start with the **positive endpoint of the actual definition value row**. Apply precisely the following discovery operations:

1. A newly discovered polarized row endpoint discovers its kind-qualified row key.
2. A discovered Function endpoint discovers all four actual children read by `store.term_view`. A positive Function requires kinds `[V,E,E,V]` and polarities `[-,-,+,+]`; a negative Function requires `[+,+,-,-]`. `term_endpoint` checks every child rather than guessing from a numeric ordinal.
3. Once per discovered local row, enumerate its actual `direct_lower_rows`, `direct_upper_rows`, `exact_non_variable_lowers`, and `exact_non_variable_uppers`. Discover both endpoints of every enumerated inequality. A lower direct entry on row `b` is `a+ <= b-`; an upper direct entry on `a` is the same inequality. Each exact lower or upper contributes its polarized nonvariable endpoint and its owning row endpoint.
4. Once per discovered anchor, discover its exact nonvariable endpoints for the anchor structural-dependency check, but emit no anchor bounds and follow no anchor direct neighbors.

This is an explanation of the executed constructor, not a new source premise. The all-local envelope says that every row reached by operations 1–3 has `level > 0` and `non_generic=false` in the inspected session. It allows arbitrary finite value/effect direct cycles, shared rows across polarities, repeated four-port children, shared nested Function DAGs, and mixed Function/effect incidence. It does not require equal original row levels or an acyclic bound graph.

The least forward closure intentionally differs from the complete raw snapshot. It does not reverse-search all Function parents from a child row, enumerate all disconnected rows, or seed all row-free admitted pairs. Such a reverse incidence/global inventory would be a stronger constructor and is not present here.

### 2.1 Actual-source locality follows from construction

Consider a finite actual HIR produced with empty semantic imports whose bindings pass `CandidateInference::solve` preflight and collection: the existing Integer, resolved module Name, lexical parameter Name, Group, Apply, and unannotated Lambda envelope, plus the explicitly admitted local-binding form; no source-internal SCC uses. This is an ordinary input envelope of the actual entry point, not a supplier of completed graphs.

**Theorem SOURCE-LOCAL.** At `280d399e`, every live value/effect row reached on this candidate path has level one and `non_generic=false` at every capture and successful use route, including every definition root, lexical formal, occurrence evaluation row, and new invocation-effect row. Hence every capture in this source envelope is all-local, and the anchor-dependency check has no seeds.

**Proof.** Startup `try_new` initializes **every** collected component row, including definition roots and effect components, at level one with Collected origin and `non_generic=false`; its next loop initializes every lambda parameter row the same way (`lib.rs:9775–9830` at `280d399e`). The record-building loop gives every actual DefinitionUse `use_level:1` (`:1259`). `admit_all_collected_facts` interleaves candidate and Lambda recipes with scalar facts (`:10779–10938`). These recipes construct terms from those existing rows; ordinary Lambda admission adds no row and submits a Function whose result-effect child is its actual body effect component. Graph Apply admission allocates its sole new invocation row at the current level of the application effect component (`shadow_apply.rs:1268–1273`), which is one by induction. The actual graph route allocates every local image at its record's level, also one. Neither graph capture nor Function construction changes levels or generic metadata.

The only level mutation along scalar propagation is `extrude`, which assigns an existing receiving row level or the minimum of existing adjacent row levels (`lib.rs:11043,11133` and the callers). If every existing row level is one, its target remains one. The graph SCC dispatch avoids F5 generalizer operations. The nongeneric assignments found in this source cone are test-only manipulations; neither admission nor graph routing sets `non_generic=true`. Successful transaction restoration preserves the prior invariant. Induction over initial admissions and then dependency-first graph routes proves the statement. Resource/identity failures terminate without a candidate result. QED.

This is stronger than checking `rows().all(is_local)` after a fixture: it derives the classification from the actual constructors. It does not justify future import, annotation, higher-level local-generalization or explicit nongeneric extensions; those must revalidate the invariant.

### 2.2 Actual `invoke` constructs symbolic source incidence

At `280d399e`, the source `my invoke f = f 1` has actual live rows: definition value `r`, lexical formal `alpha`, literal value `s`, call result `beta`, literal evaluation effect `ae`, formal-Name evaluation effect `ce`, fresh invocation effect `e`, and Apply evaluation effect `re`. Reading the real collector/admitter yields these relevant constraints:

```text
Int+ <= s-                         (actual integer recipe)
BottomEffect+ <= ae-; ae+ <= EmptyEffect-
BottomEffect+ <= ce-; ce+ <= EmptyEffect-
alpha+ <= NegativeFunction(s+, ae+, e-, beta-)
ce+ <= re-; e+ <= re-
PositiveFunction(alpha-, EmptyEffect-, re+, beta+) <= r-
```

These are **the actual source-emitted scalar constraints**, not an arbitrary kernel-model source. The new Apply demand uses the actual argument evaluation row as its positive argument-effect port and allocates `e` for its negative invocation-effect port (`shadow_apply.rs:1247–1310`). Slots 1 and 2 emit `ce <= re` and `e <= re` through actual fact/provenance admission and `constrain_live_effect` (`:1313–1380`). The lambda's positive Function reads `re+` from its body effect component (`lib.rs:10911–10918`). Capture from `r` reaches the outer Function's `alpha` and `re`; alpha's exact upper reaches `e`, and re's direct lower list independently reaches the **same** typed `e` row. This is concrete retained cross-port incidence produced by source construction.

Before any provider/use arrival, alpha has no provider lower and `e` has no EmptyEffect upper. There is no need to satisfy a pure-effect F5 guard or resolve f's provider merely to retain this demand. The invocation row and its correlation with the application result effect are retained/freshened by the actual graph algorithm. Whole Call/provider/role semantics remain separate.

## 3. Capture theorem, proved from the constructor

**Theorem CAPTURE.** For a finite, well-formed actual session and its valid definition root in the all-local envelope, the actual `capture_candidate_graph` terminates with an availability error or returns a graph with the following properties:

- Its endpoint and row discovery are exactly the least closure of §2 operations 1–3.
- There is exactly one graph row index per reached `RowKey`, with value/effect kinds distinguished even when their ordinals coincide. Both polarities of that row use that same index.
- Every reached Function keeps its constructor polarity and all four labeled children with their checked kinds/polarities. Repeated actual endpoint references have the same graph node index.
- For every physical direct or exact slot in each reached original row, the capture emits its correctly oriented typed inequality into `graph.bounds`, in that row expansion's list order. In particular, no exact Function upper on an unknown formal is discarded because no provider is known, and no effect child is replaced by a pure-effect constant.
- Row cycles are represented by finite node/row indices. Structural Function references form a DAG; they do not need unfolding through row bounds.

**Proof.** `intern` tests `endpoints` first, reserves/inserts a placeholder node and pending item only for a new endpoint, and installs its dictionary entry before the endpoint can be expanded. Thus every endpoint has a single discovered node and a single pending expansion. `row` does the same for `RowKey`; its dictionary does not contain polarity and does contain kind. `expand_node` rewrites exactly its reserved node. Function expansion reads all four actual child handles, verifies their required sorts through `term_endpoint`, and interns them; live/component row children translate to the actual corresponding typed row identity. Therefore shared endpoint references and opposite row polarities do not introduce independent rows.

The capture loop drains pending endpoints, then expands the row at `row_cursor` and increments that cursor. New rows are appended; no already expanded row is rescanned. The four local-row loops enumerate every original list slot without a summary-based filter. Every direct entry calls `bound` with its actual directed endpoints. Every exact entry calls `bound` with its actual owning row, exact endpoint and component kind. `bound` interns both endpoints and appends a bound, so no discovered inequality is left with a dangling reference. Conversely, nodes, rows and bounds are created only by these operations; induction on discovery time proves inclusion in every §2-closed set containing the root. At termination the constructor has processed every pending endpoint and row, proving closure and hence leastness.

Finiteness is obtained from the **actual session**, not by assuming a complete graph: the two row vectors and their finite bound lists supply finitely many typed rows and nonvariable endpoints; the referenced term store contains finitely many already constructed terms. A Function can only refer to existing validated children when constructed (`require_function_children`); immutable committed/branch nodes do not acquire later child references. This gives a finite structural DAG. `intern` bounds discoveries by that finite endpoint universe, and the cursor bounds row expansions by the two finite row vectors. Every slot loop is finite. The all-local case has no anchor dependencies; the general anchor checker additionally visits each captured dependency node at most once. Any fallible reservation, invalid endpoint, absent metadata, overflow or rejected anchor terminates through `Err`. The constructor performs no provider choice or satisfiability query. QED.

The emitted list has **one entry per visited source list slot**, not one entry per unique logical inequality. A paired direct edge normally appears twice, once from each adjacency direction. The graph carries the inequality, kind and sequence order; it does not carry an explicit origin label saying which source row/list/slot produced that duplicate. Consequently this theorem is not an inverse for physical source lists.

## 4. Actual instantiation theorem

**Theorem FRESH-ROUTE.** For the graph produced by §3 and a valid actual incoming `DefinitionUse`, successful `instantiate_candidate_graph` constructs a kind-preserving injective map on its local rows, shared by every occurrence in that use. It reconstructs the four-port shapes and submits the exact mapped retained bound sequence to the actual typed solver, followed by the root inequality into the existing occurrence's receiving value row. Two successful distinct use routes allocate disjoint local row images. Bound cycles and within-use correlations survive.

**Proof.** Before traversing any structural node or replaying any bound, the first loop allocates exactly one image for every `graph.rows` entry. A value source calls `fresh_value_at_level(use_level)` and an effect source calls `fresh_effect_at_level(use_level)`. Both allocators append an empty row, its numeric level, and `origin=Fresh, non_generic=false`; ordinals are the corresponding vector's former length. No scalar propagation allocates more rows. Therefore distinct rows of a kind have distinct fresh ordinals; different kinds remain distinct through `RowKey`. The resulting map is injective on the typed row set and fresh relative to rows existing before this route. Its entries are already available when any cycle is referenced. Distinct successful routes append later rows and have disjoint image sets.

The `terms` array gives one reconstruction result per graph node. A row node consults that single `rows[row]` entry and preserves its polarity. A leaf uses the actual matching leaf/extremum constructor. A Function is finished only after all four children have entries; the constructor receives `[a,ae,re,r]` unchanged in order and validates the expected child sorts. Induction on the structural DAG proves exact four-port shape reconstruction. Row-bound cycles never recurse structurally because row nodes terminate at preallocated identities. The graph node walk is iterative. When a shared child is reached again, `terms[index].is_some()` prevents reconstruction; separate equal-shape nodes can still intern to the same actual Term, which is addressed in §6.

For each `graph.bounds` entry, the algorithm obtains its reconstructed lower and upper Terms and calls `constrain_live_value` or `constrain_live_effect` with the retained component kind. Thus every emitted source slot has its mapped constraint submitted, including duplicate submissions. After this sequence the root's reconstructed positive endpoint is used as the lower endpoint, and the receiving `use_value_component`'s actual value row is used as the upper endpoint. The final call to existing `route` admits the root fact and provenance, submits the constraint, and publishes existing routed-use ownership. The candidate route then retains this same row map in `FreshRoute`. All bound and root submissions use `ConstraintOccurrenceId(record.occurrence,0)` and its `CauseId`; original capture-time causes are not copied. QED.

Levels are intentionally **not** copied from the capture: every local image starts at the use's numeric level. Original metadata is not copied either. Later propagation can lower those numeric levels through the existing `extrude`. The theorem is about actual substitution, shape and constraint submission, not the reference algorithm's copied polarity-dependent extrusion.

## 5. REPLAY and TERMINATION: constructor-derived proofs

For precision, use logical endpoint expressions consisting of polarized typed rows, the seven retained extrema/leaves, and four-port Function shapes. Erase actual nominal Term handles in favor of their recursively read shape; do not unfold rows through their bounds. A constraint is a typed positive/negative pair of these expressions. This is a syntactic reading of the actual live kernel, not a new full Function denotation.

Read the following finite task rules directly from `constrain_live`, `apply_value_task` and `apply_effect_task`. The extrema and incompatible terminal dispatch takes precedence; the installation rules below apply only after that dispatch. In particular, `BottomPositive <= ValueRow` and `ValueRow <= TopNegative` terminate without installing an exact bound:

- A same-kind row pair installs the direct edge and transmits existing exact lowers of the lower row to the upper row and exact uppers of the upper row to the lower row.
- A nonvariable-to-row pair installs the exact lower, intersects it with current exact uppers and transmits it to direct upper neighbors.
- A row-to-nonvariable pair installs the exact upper, intersects it with current exact lowers and transmits it to direct lower neighbors.
- A positive/negative Function pair emits **four** child tasks: negative Function argument <= positive Function argument; negative argument effect <= positive argument effect; positive result effect <= negative result effect; positive result <= negative result.
- The actual extrema fast paths and incompatible shapes are terminal scalar tasks. Value incompatibility records a diagnostic witness; it is not an availability error and does not establish source rejection.

Let the bound seed sequence be computed from the actual source session by §2. Let its row substitution be the actual freshly allocated map from §4. **Every generated logical rule instance factors through this map**: selecting a direct/exact list, its endpoint references, child position, component kind, extrema case or incompatible outer shape is unchanged by kind-preserving substitution. Function argument reversal occurs in both calculations at the same labeled position. A row cycle remains a cycle with renamed typed endpoints. This is proved by case analysis on the listed actual transitions, then induction on a finite task derivation. Since the map on typed rows is injective, the same argument with its inverse applies to derivations that remain entirely in this renamed all-local component. Therefore the least logical closure generated from those retained bounds commutes with substitution, modulo equal structural shapes.

This gives a useful **factorization of the actual route**: reconstruct the image of the retained bound seed; run the existing scalar closure on it; then submit the root-to-receiver task against the live receiving environment. The latter phase can connect additional environment constraints and is not claimed to be an isolated copy of source closure. The factorization neither asserts that all original global pair keys were retained nor that every uncaptured source constraint is semantically erasable.

Physical task order and physical duplicate counts need not commute: actual memo keys use Term handles, and interning can merge equal shapes. Direct adjacency contributes duplicate bound seeds. The claim is exact submission of the retained seed **sequence**, and shape-based logical closure/derivation transport; it is not identical execution counters, pair-cache entries, diagnostic witness paths, or final list lengths.

Termination is also constructor-derived. Once use rows and structural terms are allocated, scalar propagation allocates no new endpoint, row, or Function term. It selects endpoints from existing rows, exact lists and Function children. With finitely many positive/negative value and effect endpoints there are finitely many typed pair keys. `constrain_live` records an unseen pair before performing its transmission/decomposition; repeated pairs are skipped. Each newly admitted pair adds at most finitely many list entries and schedules finitely many tasks. Each list remains finite because at most the finite admitted-pair universe can insert into it. Thus there can be only finitely many nonduplicate expansions and only finitely many duplicate tasks they produce. Incompatible/extreme tasks are terminal.

`extrude` allocates no identities or structural terms: it decreases row levels in place, marks a lowered row once per generation, and reads finite direct/exact lists plus finite structural children. Revisited already old rows are skipped. Structural terms are a finite DAG, so even repeated paths terminate. Diagnostic completion operates on the finite admitted value-pair graph with finite SCC/member/edge traversals and a bounded per-SCC bucket range; arithmetic/capacity exhaustion returns availability error. There is no successful infinite worklist or recursive structural cycle hidden in a row cycle. Each finite candidate SCC/member/use loop then consists of these terminating operations. This is a finite termination proof, **not a linear-time inference bound**; repeated DAG paths in extrusion and solver closure can be expensive, and allocation failure can occur.

Successful capture and reconstruction are linear in captured reference/list occurrences before replay, with hash-table operations interpreted in the usual expected-cost sense. General solver replay is outside that linear bound. Failed-capture high-water accounting is not certified by the final successful sample, and this packet supplies no numeric RSS/resource ceiling or retry guarantee.

## 6. Reconciliation with complete raw extraction/freshening

The independently reviewed raw-snapshot construction has a stronger record-retention goal. It captures all value/effect rows, all four list families and ordered slots, levels/metadata/summary flags, all admitted pair keys, actual root/component translations, and distinct immutable term-record identities. Fresh record maps decode to those exact original records. Runtime realization may merge nominal Term handles while immutable record identities remain separate.

The actual candidate constructor does something materially different:

| Dimension | Complete raw snapshot | Actual candidate capture/route |
|---|---|---|
| Seeds | All active rows/pairs plus referenced terms | One actual definition value root |
| Closure | Complete/reference incidence available | Forward structural children and reached local row bounds |
| Rows | Every active typed row | Reached typed rows; anchors retained by original identity |
| Direct slots | Original owner/list/slot retained | Directed inequality emitted for every visited slot; owner-list provenance omitted |
| Exact slots | Exact source record retained | Directed structural inequality emitted; source causes omitted |
| Metadata/level | Original immutable fields retained | Only local/anchor Boolean retained; local runtime images use `use_level`, Fresh metadata |
| Summary flags | Original flags retained | Recomputed as a byproduct of replay, not copied |
| Term identity | Original nominal handle and immutable record retained | Captured node identity retained, original Function handle dropped; runtime interning can merge shapes |
| Pair cache/evidence | Pair-key records retained, not whole continuation | No original cache copy; actual session memo handles replay |
| Result | Exact record inverse | Kind/shape/correlation and retained logical-constraint factorization |

The theorem here does not weaken RAW-EXTRACT/RAW-FRESH. Conversely, those stronger snapshot theorems do not establish a physical round-trip for this actual candidate implementation. Replaying a direct edge captured from two paired slots normally yields one solver installation because the typed memo suppresses the second logical pair; clearing a memo while keeping old physical lists can instead append duplicate entries. Either behavior disproves an unsupported assertion of identical physical row slots/cache continuation. The candidate uses its actual persistent memo and does not claim restored original physical state.

## 7. Exact limits and attempted falsification

Two distinct bounded methods were used: constructor/worklist invariant derivation, and a direct code attack on source ownership, anchor adjacency, pair omission and interning. No third supplier inventory or supplied-graph premise was introduced.

### Mixed anchors

`expand_row` returns after traversing an anchor's exact nonvariable endpoints. It never scans the anchor's `direct_lower_rows`/`direct_upper_rows`; the later dependency check only follows structural Function children and rejects a local row reached along those children. Therefore it does not certify closure through direct anchor adjacency. A finite session shape `local r -> anchor a -> local q`, with `a` made nongeneric at positive level, can make `q` absent from capture while old `a -> q` remains active. Subsequent fresh `r_i -> a` constraints can reach the old `q` through the actual solver. This is an exact structural limitation, **not an executed admitted-source counterexample**: current candidate source collection does not produce that nongeneric marking, and a test that sets metadata by hand would only establish the private-session seam. Level-zero adjacency ordinarily lowers connected younger rows through `extrude`, so one must not present a manually invented level-zero mixed graph as though normal source construction produced it.

Anchors keep their old live identities and installed bounds in the current session. Import/outer capture correctness requires actual environment closure and appropriate non-generic/source classifications, which this slice lacks. The independent source Generalize theorem distinguishes `Desc`, `Mono/Established`, `Internal`, `Shared`, `ViewLogic`, `EventField`, and `EventProof` at their real scopes. A numeric row eligibility Boolean supplies none of those full certificates. The all-local theorem avoids this unresolved seam without inventing an anchor supplier premise.

### Missing global records

Disconnected rows, row-free pairs, reverse Function-parent incidence, original diagnostic causes and original pair-cache payload are absent from candidate graphs. This refutes an all-active-record inverse assertion but is not itself a proof that the root's logical inference result is wrong. No elimination/completeness theorem for the omitted complement is claimed. A necessary-edge source counterexample would have to show a legitimate source-owned relation whose logical obligation is lost at the actual capture/route, rather than merely supply an arbitrary kernel graph or opaque residual that mentions an omitted row. No such admitted-source counterexample was established by these reads.

### Deferred inference and complete contracts

The actual Apply recipe constructs an upper demand against the callee row and does not require an existing positive Function lower or a selected provider. That is the deferred Simple-sub spine. It does not attach complete receiver, whole-argument provider/world/xi, entry/protection, returned-callee, result-image, admission/license, future/event or logical scope evidence. `CandidateInference::unresolved` retains every existing unresolved premise. A literal packet carrying full external documentary sources is not a CallMem/C0 proof; this packet makes no such inference. All original complete-contract obligations remain owned by their source/solve/elaboration phases.

## 8. Executed actual HIR/candidate evidence

The test-only [candidate source module](../../crates/yu-solver/src/tests/candidate_graph_call.rs)
uses actual parsing, `yu_hir::shadow::lower_module_with_shadow_applications`,
empty semantic imports and `CandidateInference::solve`. The candidate collector,
SCC graph plan and actual incoming routes are the implementation under test;
there is no test-only source inference replacement. The two executed fixtures are:

```yu
my invoke f = f 1
my first = invoke
my second = invoke
```

```yu
my id x = x
my invoke f = f 1
my first = invoke id
my second = invoke id
```

Both check the actual HIR/definition/Name-use ownership, no recovered scalar
conflict, the positive Lambda and negative demand's four ports, integer support
at the argument, shared result identity and the same symbolic invocation-effect
row feeding the body effect. The captured formal has no positive Function lower
path, and the invocation-effect row has no retained path to an Empty upper.
The positive Lambda's separate argument-effect port remains its actual Empty
negative leaf. No whole receiver/protection meaning is inferred from that leaf.

For each actual incoming use, the retained source-row map is tied to the
corresponding export by owner-aware identity. The tests check every source row
is local in these empty-import fixtures, one image per typed source row, kind
preservation, disjoint Value/Effect local images across two uses and stable
identity on reborrowing a route. Opposite-polarity occurrences pivot only through
the same source row in the directed bound search; rows from different graphs
are not identified.

The second fixture checks both `invoke` routes and both `id` routes. An actual
`IntPositive` lower must reach each receiving definition result root through
retained directed constraints. It also checks the expected captured `invoke`
relations after provider routes have run. This is a final structural observation,
not a before/after equality test of every slot. The borrowed API exposes the
retained maps and graphs, not mapped fresh bound Terms; no installed incidence
claim is inferred from map counts.

These two cases passed after independent code review and the bounded assertion
repairs recorded in the linked review. They do not execute arbitrary inputs,
nonempty effect-label semantics, source-Generalize correspondence or a closed
public scheme. The current candidate explicitly retains every unresolved
complete-contract premise.

## 9. Exact proof boundary

SOURCE-LOCAL, CAPTURE, FRESH-ROUTE, REPLAY and TERMINATION derive the actual graph from source construction and the actual session, preserve the symbolic invocation incidence and one typed substitution map, and prove finite constructor/propagation behavior. They do not assume a supplied completed graph, resolved provider, successful constraint satisfaction query, or complete source Call certificate.

The obligations for complete Call, Source Generalize, a principal public scheme, source eligibility and production acceptance are not claimed discharged. Independent mathematics and specification review checked the full statements and actual owners, including the all-local source induction, every retained slot, the shape quotient and receiving-environment boundary. Both passed; the terminal-rule precedence clarification in §5 was applied after both reviews. Executed source evidence and its precise limits are recorded separately; the mathematical proof does not depend on passing fixtures.
