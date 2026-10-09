# Source-generated directional bounds: exact fresh membership construction

Date: 2026-10-10
Status: independently reviewed source construction and logical membership theorem
Baseline: `334fd359944cc1ecc5903e768c26349708e40fab`
Scope: actual admitted empty-import level-one candidate source and directional membership closure
Production/API or language adoption: none
Review: [independent directional proof review](../progress/2026-10-10-candidate-directional-source-review.md)

The [earlier capture/route theorem](2026-10-10-candidate-graph-call-correspondence.md)
is pinned to `280d399e`. Direct ownership and scheme initialization changed at
the new baseline; no transport of that old operational proof is assumed here.
The current user-directed deferred Simple-sub construction and the existing
source/solver owners govern this research result.

The closure proved below is a finite worklist invariant for currently installed
constraints. It implies neither a solved type nor final initializer constraints,
and is not a requirement to freeze a local scheme before processing a
continuation. The [live let correction](../progress/2026-10-10-live-let-level-extrusion-correction.md)
governs the general local adapter. This theorem certifies the pinned candidate
module-graph path; it supplies no mandatory initializer scheduling barrier.

## Result and the substantive delta

There is a constructive updated theorem for the actual candidate's currently admitted **empty-import, level-one source envelope**. Startup, source recipe admission, graph capture, per-use freshening and scalar propagation remain all-local. In this envelope `candidate_extrude` returns exactly its original endpoint; it allocates no copied row or reconstructed Function. Nevertheless the scalar calculus is now directional and the previous paired-edge proof is inapplicable.

For a row constraint `a <= b` at equal levels, candidate solving installs **only `b` in `a`'s upper list**. No paired lower incidence is inserted on `b`. Graph capture now retains the installed owner side. Fresh initialization explicitly restores that same owner-side membership, bypassing the ordinary pair memo, then processes induced comparisons. The updated theorem preserves the complete reached **directional membership closure**, all four Function ports, typed row identities and actual source invocation-effect correlations. It does not assert paired-edge semantics, physical row-list equality after replay, or recreated pair/diagnostic evidence.

There is an important idle-restoration scan nuance (§5): its opposite-list count is sampled once, but its direct/exact index boundary can change while individual comparisons run. Therefore an assertion that it explicitly visits every initially sampled opposite slot is not justified. The theorem uses the stronger fact supplied by the actual constructor: capture is taken from a logically saturated source membership state and restores **every reached membership as an explicit seed**. It does not invent a stable-list premise or require a supplier of a completed graph.

## 1. Exact dependency snapshot and owners

| Pinned path | Git blob |
|---|---|
| `crates/yu-solver/src/candidate_extrusion.rs` | `2ca0a0ae198defc358f571a7cd42418b38ad57ae` |
| `crates/yu-solver/src/candidate_scheme.rs` | `a087621d37c3004387f9b4ae001031aaaa71ad2f` |
| `crates/yu-solver/src/lib.rs` | `7d14ccb011dac6602a536d75b8fcb3501de15be8` |
| `crates/yu-solver/src/shadow_apply.rs` | `8ab2f15e4cd8d41aece4d821319f77469eae389d` |

The owning functions are `candidate_extrude` (`candidate_extrusion.rs:36–263`), `candidate_insert_bound` (`:280–404`), opposite-list access (`:406–459`), idle `candidate_restore_bound` (`:465–498`), active `candidate_replay_bound` (`:500–536`), and directional value/effect application (`:538–590`). `candidate_scheme::Bound` now has `side:Polarity`; its eight local list loops write Positive for lower memberships and Negative for upper memberships. Its use loop at `candidate_scheme.rs:773–791` reconstructs endpoints, recovers the owner using that side, and calls `candidate_restore_bound`. The final receiving-root call still uses the existing route transaction and fact/provenance owner.

`lib.rs` dispatches graph-mode effect/value row tasks to the new directional helpers, and nonvariable value bounds to `candidate_extrude` before ordinary installation. Legacy F5 retains paired adjacency and in-place aging. `shadow_apply.rs` is unchanged from `280d399e`: CandidateInference selects `collect_candidate_mode(hir,true,true)`, symbolic Apply invocation rows, actual argument effects, callee/invocation output flow, and Group child-effect forwarding.

The implementation checkpoint reports independent static review and owning checks, with runtime behavior unverified at that checkpoint. The linked review now records independent review of this separate level-one constructive source argument and the primary's executed source evidence. This theorem makes no conclusion about the general unequal-level implementation.

## 2. SOURCE-LOCAL and identity extrusion

The source envelope is a finite actual HIR produced with empty semantic imports and accepted by CandidateInference preflight/collection: Integer, module-resolved Name, lexical parameter Name, Group, Apply, unannotated Lambda, and the already admitted special captured-local binding form. Source-internal SCC uses are rejected. No mutable test intervention changes levels, metadata, bounds or routes.

**SOURCE-LOCAL.** Every live row on this entry path has numeric level one and `non_generic=false` throughout successful initial admission, candidate capture and incoming routes. Definition roots, lexical formals, evaluation rows and symbolic invocation rows are included.

**Proof.** `try_new` initializes every collected value/effect component and parameter row at level one with Collected origin and `non_generic=false` (`lib.rs:9791,9807,9826` and surrounding constructors). Actual DefinitionUses have `use_level:1` (`:1261`). Candidate Apply allocates its invocation-effect row at its application's current effect-row level. Graph instantiation allocates local images at the use level. There is no source-path nongeneric assignment; the assignments found in this code are test manipulations. Unlike the old path, graph-mode directional helpers do not lower levels. Their nonvariable value-bound handler invokes `candidate_extrude` at an existing receiving row's level; the following lemma shows that it creates no younger or copied row in this envelope. Graph SCC dispatch bypasses F5 generalizer operations and legacy aging. Induction over actual source recipe admission, then dependency-first graph routes, preserves the invariant. Availability failure returns no candidate result. QED.

**IDENTITY-EXTRUDE.** If all reachable actual rows have level one and target level is one, a successful call to `candidate_extrude(endpoint,p,1)` returns **that same endpoint identity**, preserves all existing rows/levels/metadata/memberships, and allocates no row or structural Term.

**Proof.** On a row Visit, `original_level <= target` is true; lines 68–70 memoize the original endpoint and continue before any bound snapshot, fresh allocation, source link or pending-bound operation. Extrema/leaves memoize themselves. On a Function, all four children are visited with the prescribed polarity reversal for argument and argument effect. Induct on its actual immutable structural DAG. Each child returns its original endpoint, so the Function finish's `changed` flag remains false and it stores `original`, bypassing both Function constructors. Row-bound cycles are never traversed because their row Visit took the old-enough branch. Thus no `Work::Bound` is produced, no `candidate_insert_bound` is called, and no younger-row branch runs. Maps/work storage and resource sampling still occur and can fail; identity does not mean zero allocation or a free operation. QED.

For any source nonvariable bound comparison, the rewritten key therefore equals its original key. The new transformed-parent branch is not taken. No general polarity-copy, unequal-level termination, extrusion equivalence or copied-approximation theorem follows from this result.

## 3. The current directional logical kernel

Use logical endpoint shapes formed from polarized kind-qualified rows, retained leaves/extrema, and the four labeled Function children. Nominal actual Term handles are read into their shapes; row bounds are not unfolded inside a shape. Use **sets of installed owner-side memberships** for logical reasoning, while the actual constructor retains physical slot sequences.

The rules are read from current code, with level comparisons simplified only by SOURCE-LOCAL. Terminal extrema/incompatible dispatch takes precedence over the installation cases. In particular, `BottomPositive <= ValueRow` and `ValueRow <= TopNegative` do not install exact bounds:

1. An unseen same-kind row pair `a <= b`, with `a != b`, installs `Upper(a,b)`. Self pairs are terminal and insert nothing.
2. A nonvariable-to-row pair installs `Lower(row,nonvariable)`.
3. A row-to-nonvariable pair installs `Upper(row,nonvariable)`.
4. Each newly installed lower item `l` on owner `o` schedules `l <= u` for every existing upper item `u` on `o`. Each newly installed upper item `u` schedules `l <= u` for every existing lower item `l`. Direct rows and exact nonvariable items participate in both lists.
5. Positive/negative Function comparison emits the actual four variance tasks: negative argument <= positive argument; negative argument effect <= positive argument effect; positive result effect <= negative result effect; positive result <= negative result.
6. Value extrema shortcuts and incompatible shapes are terminal, with the latter recording a diagnostic witness; the effect Bottom/Empty comparison is terminal. These are the actual scalar rules, not a denotation for complete Call.

The current rules **do not install both row-edge incidences**, nor do they assert explicit transitive adjacency. For example `a.upper b`, `b.upper c` represent a chain even without `a.upper c`; a later concrete lower on `a` schedules a comparison into `b`, which then schedules into `c`. This is enough for the actual deferred spine and is different from the previous paired-edge operational state.

An active `candidate_replay_bound` snapshots an opposite count and queues its comparisons without executing them between list reads. Therefore its indexing sees the same direct/exact boundary during that loop. Processing resumes only afterward on `constrain_live`'s owning worklist. Each insertion of the second side of a lower/upper combination schedules its comparison. The memo admits a new pair before its application/decomposition and skips subsequent duplicates. Immutable Function pairs cannot acquire new children. A duplicate row pair's installed side continues to participate in all later opposite insertions.

The source induction begins at **actual empty startup memberships and an empty pair memo**, which are closed. On each active fact/recipe submission, a newly installed side pairs with every opposite already present; if a new opposite arrives later, its own insertion pairs with the first side. Thus at the return from each worklist drain, every newly enabled cross-side combination has had its membership consequences installed or already represented, and every four-child decomposition is drained. Previously enabled combinations remain covered because memberships and memo consequences persist. This proves preservation of membership closedness by actual active admission from this constructed state. It is not a claim that an arbitrary idle solver, manually inserted row lists, or an arbitrary supplied memo is saturated.

Here “closed” concerns **membership consequences**. It does not mean all equivalent comparison keys have been inserted into the cache, that an inequality is satisfiable, or that every terminal incompatibility is represented in an exported graph. Solver errors remain owned by the candidate result.

## 4. CAPTURE from the actual source constructor

**CAPTURE.** At each candidate definition capture on the actual source path, the algorithm terminates or returns an availability error. On success it returns exactly the least forward closure from the actual definition's positive value-row endpoint, following all four structural children and every installed local membership. Every reached source slot is represented with its correct kind, owner side, endpoint orientation and sequence order. Its logical membership set is closed under the current directional kernel.

**Construction proof.** The actual root is obtained from the frozen root component position and `live_components`, not supplied as a completed graph. `intern` creates one pending node per previously unseen polarized endpoint. `row` creates one row per `RowKey`, which contains kind and ordinal but not polarity. A Function Visit reads/validates all four actual child kinds and polarities and interns them. Each row cursor scans all four physical lists exactly once. Lower slots get `side=Positive` and owner as the upper endpoint; upper slots get `side=Negative` and owner as the lower endpoint. The item is distinguished as direct/exact by its endpoint constructor. Every source slot is emitted, even if logically duplicated. The pending stack and monotonically advancing row cursor establish closure; induction on discovery establishes leastness. Finiteness comes from actual finite row vectors, finite physical lists and the immutable structural term DAG. Bound cycles use indices rather than recursive unfolding.

The row key plus Bound side and item constructor now retain the **owning list**. Filtering graph bounds by owner, side and direct/exact category reconstructs the source list's endpoint-shape order and multiplicity on reached rows. Original Function handles, levels, full metadata, summary flags and causes remain omitted, so this is still not a complete raw-record inverse.

**Closedness proof.** Initial active recipe/fact admission drains current directional rules as in §3. Before capture, incoming dependencies are routed by the existing dependency-first plan; the restoration/root lemma in §5 preserves logical closedness, allowing induction over this actual execution order. Consider any rule instance whose premises are memberships on a captured row. Capture copied that row's entire installed lists, so both premise items are retained. Their structural children and every referenced row are reached. Every consequent installed in the actual completed source state is then a membership on one of these reached rows, and that row's whole list is copied. Function decomposition never creates a new structural shape on the level-one path; it selects existing children. Thus restriction to the constructed forward closure remains logically closed. No reverse-parent inventory or global row enumeration is needed for this argument. QED.

This does not prove erasure of the uncaptured complement for arbitrary source meanings. It proves closure of the scalar membership component that the actual algorithm constructs.

## 5. FRESH-ROUTE and logical REPLAY

**FRESH-ROUTE.** Actual incoming routing preallocates exactly one fresh same-kind image for each captured local row, all at level one with Fresh origin and `non_generic=false`. One map is shared across both polarities, every Function child, and every bound. Two successful routes have disjoint typed row images. Actual reconstruction retains four-port shapes and bound cycles. Every source slot is explicitly restored to its mapped original owner side, and the final receiving-root constraint uses the real use occurrence/cause and route transaction.

**Proof.** The rows loop finishes before term traversal or replay. Fresh ordinal append is injective within each kind, and `RowKey` prevents cross-kind ordinal collision. Row nodes consult the same map entry for both polarities. Function finish passes all four realized children in original order to the checked constructor. Its DAG walk terminates at row identities, even when bound references cycle. Runtime interning may merge equal shapes but cannot change a typed row reference. The bound loop maps both endpoints and, using `side`, chooses `(owner,item)=(upper,lower)` for Positive or `(lower,upper)` for Negative. `candidate_restore_bound` always calls `candidate_insert_bound` before any induced comparison, irrespective of pair memo membership. Hence every original owner-side slot has an explicit mapped insertion, in graph-bound order; induced insertions may interleave additional entries. The final route still admits the receiving fact/provenance and invokes ordinary `constrain_live` on the reconstructed root. QED.

### 5.1 Why idle restoration cannot be described as ordinary pair replay

The old theorem that every retained inequality is submitted as a seed pair is false for current code. Seeds are **installed memberships**; only induced comparisons enter `constrain_live`. This distinction preserves source owner choice even when fresh rows share a level. Ordinary re-comparison of a Positive row lower slot could select the lower endpoint's Negative owner instead; side-preserving initialization does not make that switch.

There is also a concrete scan boundary to retain in the proof. In `candidate_restore_bound`, `count` is sampled at line 478. Each iteration reads the current `candidate_opposite_bound(...,n)`, then drains `constrain_live`. The latter can append to that owner's direct opposite list. Since `candidate_opposite_bound` locates exact items using the current direct length, an old exact item can move beyond the originally sampled count or be displaced by new direct items. Therefore this packet **does not claim** that the loop individually compares against every opposite slot present at its start. No such immutability premise is in the code. Active replay does not have this interleaved mutation pattern.

### 5.2 Exact logical membership preservation despite that scan boundary

**REPLAY.** Before receiving-root submission, the final logical membership set on the fresh component is exactly the image of the actual captured source membership set, interpreted as endpoint shapes. Extra physical entries and memo differences are allowed. After receiving-root submission, active scalar solving closes the resulting connection against the existing receiving environment.

**Proof.** Let C be the membership set constructed and copied by CAPTURE; CAPTURE established C's closedness from actual completed source admission and dependency-first routing. Let M be the actual newly allocated typed row map. Define M(C) by mapping row references in each captured owner and item while preserving side and all four Function children. Case analysis on current directional rules proves that M(C) is closed: row kinds, self/nonself tests, equal-level owner selection, side choice, Function labels/variance and terminal shapes commute with M. Structural interning identifies equal shapes only. This is a construction-derived set, not a supplied completed Graph premise.

Fresh rows start empty and are disjoint from existing environment rows. During restoration every explicit membership is in M(C). Every induced comparison uses items from these memberships, and every membership consequence of such a comparison is already in M(C) by closedness. IDENTITY-EXTRUDE introduces no additional representative, original row, term shape or link. Thus induction on actual restoration/worklist steps proves that the live logical set stays a subset of M(C). This remains true if the idle opposite scan repeats or skips an item. Conversely the outer graph-bound loop visits **every captured source slot** and unconditionally inserts it on the retained side. At its end every member of M(C) has been installed. Therefore the final set equals M(C).

This proof deliberately does not infer complete comparison-cache or diagnostic recreation from that equality. Some source row-free pair admissions may be absent. Terminal comparisons can be omitted or deduplicated without adding a membership. Original candidate conflicts remain available from the result, but per-use diagnostic replay identity/completeness is not proved here.

The receiving root task is then processed by the active worklist, starting from two logically closed states: the copied component and the existing candidate environment. Its new membership, and each consequent insertion, queue all current opposite combinations using active replay. Every newly added opposite membership likewise pairs with all existing items of the other side. An already admitted pair either produced its immutable Function children or its directional membership on earlier processing; that membership is still present. Therefore memo skipping does not remove later opposite incidence. Finite worklist drain yields the membership closure of this connection under the current rules, while preserving the source seed set.

Applying the argument inductively to each actual incoming route establishes the closed-state premise used at the next capture in §4. No source provider resolution, satisfaction test, arbitrary residual supplier, or stable idle-list premise appears. QED.

The theorem is logical set preservation plus actual seed insertion. It is neither exact final physical slot round-trip nor a theorem that the new directional state is physically equivalent to the old paired state. Physical duplicates can be appended by unconditional restoration and by a later first memo admission of the same seed comparison. Counts and order of induced entries, pair cache, diagnostic path, resource capacities and nominal Term identities need not match.

## 6. TERMINATION on the actual source envelope

SOURCE-LOCAL and IDENTITY-EXTRUDE bound the endpoint universe during each propagation phase. Initial Apply recipes add one known invocation row each. Fresh route allocation adds one image per captured row and finitely many reconstructed structural nodes. After that, scalar solving and identity extrusion create no endpoint/row/Function identity.

The positive/negative value/effect endpoint universe is finite, so the typed pair-key universe is finite. Each unseen comparison is memoized before applying its finite membership/decomposition consequences; each newly memoized pair installs at most one membership and schedules finitely many opposite comparisons. Immutable Function decomposition has exactly four children. Each physical row list is bounded by its finite initial/restored slots plus the finite admitted-pair insertions. Thus every active replay loop and every nonduplicate task is finite, as are the duplicate tasks they produce.

Restoration adds one explicit insertion per finite graph bound. Its count snapshots are finite even when their index boundary shifts; each call to the ordinary worklist terminates by the finite-pair argument. There are finitely many such calls. On this envelope extrusion traverses only the finite structural DAG, with row visits terminating immediately; no pending bound copying occurs. Capture and instantiation use finite indexed worklists. Existing diagnostic completion traverses the finite admitted value-pair graph/SCCs and bounded bucket ranges. Checked overflow/capacity failure terminates through availability error. Definition/member/incoming-use orchestration consists of finitely many such operations.

No aggregate linear-time inference bound, numeric resource envelope, failed-allocation peak or retry guarantee is claimed. In particular identity extrusion still allocates transient maps/work capacity and samples resources; lower/upper cross-products and diagnostic/provenance work can be expensive. This proof does not extend to unequal-level copying, whose source links can enlarge memberships and whose termination requires a separate argument.

## 7. Actual `invoke` delta and fixed source tests

The real source collector remains the `280d399e` collector. For:

```yu
my invoke f = f 1;
my first = invoke;
my second = invoke
```

the lexical formal alpha has the exact upper demand `NegativeFunction(s+,ae+,e-,beta-)`; e is the newly allocated symbolic invocation effect, and the lambda root has a positive Function with argument alpha and result effect re. Actual source constraints include `ce <= re` and `e <= re`. At 334, these install **ce.upper re and e.upper re**, not re.lower ce/e.

Capture discovers e through alpha's exact upper demand, then discovers re through e's upper membership. The outer Function already discovers re independently. The same typed e is used in its demand port and its directed membership into re, so the invocation/application correlation survives actual capture and both fresh routes. The earlier theorem's claim of finding e through re's direct lower adjacency belongs to the old paired pin and is false at 334.

The pure formal-Name evaluation row ce can be absent from invoke's capture: ce is an incoming directional predecessor of re and no Function port names ce. Its `ce.upper re` record is therefore not a captured slot. This is a concrete partial-capture change, not a counterexample to the bounded theorem. ce has the existing pure Name evaluation facts; the graph theorem does not claim all source fact occurrences are copied or that the uncaptured complement is semantically erasable for complete Call.

The repeated-provider fixture remains:

```yu
my id x = x;
my invoke f = f 1;
my first = invoke id;
my second = invoke id
```

Its dependency-first actual routes install separate fresh invoke maps and ordinary Function demands. The mapped formal demand and mapped invocation upper into application evaluation are owner-side seeds. Provider arrival enters the active four-port worklist. Executed source evidence is recorded separately in the review. The existing tests inspect retained directed inequalities and owner-aware row identities; old legacy paired-list tests are not evidence of paired behavior in graph mode. This proof neither assumes a passing fixture nor changes any expected result.

These observations establish deferred scalar construction/constraint retention. They do not establish source acceptance, provider/world correlation, receiver/entry/protection, whole argument, complete result image, admission/licensing, future/event evidence, structured nonempty effects, Source Generalize, public scheme correctness or F5 cutover. All complete contracts remain open at their original owners.

## 8. Exact proof boundary

The proof derives closure from actual startup, active admission and the
well-founded dependency-first route order. It never takes an arbitrary idle
session, supplied saturated graph or stable opposite-list scan as a premise.
Owner-side seed insertion and membership-set equality are proved directly;
physical slot equality, pair-cache recreation and terminal-diagnostic replay
completeness are not consequences of that equality.

The old paired-incidence assertion is false at this baseline. The stronger
claim that idle restoration visits every opposite slot sampled at its start is
not justified by its interleaved mutable indexing, and is unnecessary for this
construction. No necessary-source-edge counterexample has been established in
the stated envelope. The mathematical result is the constructive theorem above,
with complete original Call, Source Generalize/public scheme and unequal-level
source correspondence left at their independent owners.
