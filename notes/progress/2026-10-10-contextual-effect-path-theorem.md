# Contextual effect paths: exact representation and terminating observations

Date: 2026-10-10
Status: independent mathematical review passed for the stated word/observer subsystem; full inference gates and production authority remain open
Claim class: constructive finite-observation theorem for an inspected algebraic subsystem; exact finite derivation representation for the full supplied transition schema; minimized obstructions to stronger claims
Assigned baseline: `b69bb905983881506cdbb294805f2bdeacf77be9`
Branch: `research/simple-sub-intrusion`
Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Lease: this note only; disposable executable probe is outside the repository

## 1. Result and the boundary of the result

An infinite set of exact POP contexts does not force infinite work to answer every effect observation. There is a terminating, exact algorithm for **all one-ID normal-form contexts**, and a separate terminating simultaneous-ID analysis of **upward active attachment-family/filter observations**, on any finite graph whose transfer operations are one-sided word composition. It permits arbitrary PUSH and POP cycles, arbitrarily large counts, independent attachment IDs with the same family, and future graph additions. The algorithm computes finite context-free reachability relations. It never truncates a count.

That result does not, by itself, solve the complete directed Oracle transition algebra. The actual directed replay operation is nonassociative. A three-operand example below disproves treating arbitrary mixed replay derivations as the weighted walks of an ordinary graph. A finite grammar of **bracketed derivation trees** does retain their exact meaning and terminates as a representation-building algorithm, but it does not automatically give a terminating decision procedure for every observation of that grammar.

There are therefore three different statements:

1. A finite grammar can represent countably many exact residual contexts without enumerating them.
2. Particular finite observations can be decided exactly by finite saturation, without any finite quotient of all residual contexts.
3. A finite contextual memo that preserves all possible future prefix/replay observations is generally impossible even for one attachment ID.

Statements 1 and 2 are proved within the scopes below. Statement 3 has an explicit counterexample. This note does **not** infer impossibility of a terminating full solver from statement 3. Pushdown and grammar algorithms are examples of terminating procedures that do not use a finite context congruence.

The target remains

```yulang
my f(cb: (int -> [io] 'c)): 'c = run_io: cb 1
```

with expected scheme `(int -> ['b, io] 'c) -> ['b] 'c`. Nothing here changes that requirement or introduces a source restriction. The theorem's syntactic subsystem is a scope of a proved algorithm, not a proposed accepted-input envelope.

## 2. Source-exact algebra used in the proofs

The selected annotation policy is in `notes/design/2026-10-10-annotation-effect-hygiene-integration.md`. The inspected Oracle owners are:

- `constraints/directed_weight.rs`, `LeftStackWeight::compose`, `compose_same_id_counts`, `DirectedWeights::mix`, and `active_stack_items`;
- `constraints/mod.rs`, `ConstraintWeights::swapped`, `both_from_right`, `compose_for_replay`, and `without_left_filter`;
- `constraints/machine/propagate.rs:11–55,207–271`, wrapper normalization and all four Function ports;
- `constraints/machine/bounds.rs:3174–3191,3213–3255,3285–3360`, filter consumption, registration, current/future lower checking, and positive Function no-op;
- `constraints/machine/entry.rs:1092–1107`, Oracle's unconditional same-variable omission.

For one immutable attachment ID, normalize a left word to `(p,n)`, meaning `p` leading POPs followed by `n` PUSHes of its fixed family. Composition is

```text
(p,n) ; (q,m) = (p, n-q+m)       when q <= n
              = (p+q-n, m)       when q > n.
```

Only PUSH then POP cancels. POP then PUSH does not. Different IDs never cancel, including IDs having the same family. Active-family checking inspects `n>0`, rather than `p>0` or the mere presence of the ID.

These equations are the natural-number mathematical lift of the inspected source. Oracle stores `u32` counts and uses saturating addition in some places; this note does not use integer overflow as a mathematical finiteness argument or claim unbounded exact arithmetic from that implementation.

Filters are consumed before bound storage. A retained filter checks current/future positive lowers and active stacks. Checking a positive Function does not descend to its ports. Function comparison, when it later becomes available, independently generates argument/argument-effect children under `swapped(W)` and result/result-effect children under `W`; pure argument-effect passthrough uses `both_from_right(W)` and its owning target constructor. These are separate transitions, not a grant inferred from row equality.

## 3. Independent walk semantics for the associative subsystem

Let `G=(V,E)` be a finite primitive graph. Vertices retain kind, source occurrence and owner coordinates where relevant. An edge is an actual source-owned traversal, not a permission attached to a canonical row. Each edge carries a finite left word over PUSH/POP of immutable attachment IDs. Expand finite words into fresh edge-intermediate vertices. No empty word is lost: it becomes an epsilon edge.

For a seed at a vertex, the reference semantics is **all finite edge walks** beginning at that seed. Evaluate each walk by literal same-ID PUSH/POP cancellation, independently of the candidate algorithm. For ID `i`, its normalized result is `(p_i,n_i)`. The observable at endpoint `v` is whether at least one such walk has `n_i>0`. Family support is the union of the fixed families of these active IDs. Different events/seeds can be retained as separate coordinates and unioned only at this public observation.

This semantics allows infinitely many exact weights on one endpoint pair. It includes zero-length walks, cycles, and every finite cycle power. It does not need a complete registry of all future contributions. A newly inserted lower/seed or edge extends the primitive graph and changes this same definition.

The source algebra proves that append evaluation of `n_i` obeys

```text
PUSH_i: n_i -> n_i+1
POP_i:  n_i -> max(n_i-1,0)
other ID / epsilon: n_i -> n_i.
```

The leading POP coordinate is irrelevant to these **forward active observations**, even though it remains essential to exact exported contexts and future prepending. This follows directly from the composition equation; it is not an assumed POP idempotence.

### Algorithm

For each attachment ID `i`, relabel its PUSH as `U`, its POP as `D`, and all other-ID operations as epsilon. Retain their original IDs in the graph; relabeling is an operation-local projection for one query.

Compute a relation `B_i` on `V×V`, initialized with diagonal pairs and epsilon edges, by increasing saturation under:

```text
B(a,b) and B(b,c)                         => B(a,c)
U(a,b) and B(b,c) and D(c,d)               => B(a,d).
```

It recognizes balanced Dyck walks, allowing epsilon edges. Then compute `P_i`, initialized with `B_i`, under:

```text
B(a,b) and U(b,c) and P(c,d)               => P(a,d).
```

It recognizes Dyck-prefix walks: no prefix has more POPs than PUSHes, but the final excess PUSH count may be arbitrary. Compute ordinary graph reachability `R` from the seed, disregarding labels. The active observation at `z` is

```text
exists a,b: a in R and U(a,b) and P_i(b,z).
```

An initially weighted seed is represented by a fresh finite entry chain for its actual word; it is not replaced by a guessed active flag. Multiple seeds use distinct entry coordinates when provenance must stay separate.

### Termination

Both `B_i` and `P_i` are subsets of the finite set `V×V`. Each successful saturation addition adds a previously absent pair. There are at most `2|V|²` additions per ID. Ordinary reachability is finite. This proof permits PUSH-bearing SCCs and POP-bearing SCCs; it assumes no count bound or iteration limit. A simple implementation may have inefficient joins, but inefficiency does not change its finite termination proof. The finite number of currently formed source IDs is used only to enumerate current queries, never as a bound on their multiplicities or a registry requirement for future source input.

### Soundness

The two rules for `B_i` respectively concatenate balanced words and surround a balanced word with one matched PUSH/POP. Induction on saturation derivations therefore yields an actual balanced walk for every pair in `B_i`. The `P_i` rule concatenates a balanced walk, an unmatched PUSH, and a prefix walk; induction yields an actual Dyck-prefix walk.

If the algorithm reports activity, ordinary reachability supplies an actual prefix to `a`. Its current count can be any nonnegative integer. The edge `U(a,b)` adds one. The prefix walk from `b` to `z` never consumes that new bottommost unit because each suffix prefix has nonnegative relative balance. Thus the complete actual walk ends with positive active count. No authority is created by the query projection.

### Completeness

Take any actual finite walk ending with positive active count. The ordinary append equations admit a literal stack interpretation: PUSH adds one token; POP removes the top token when nonempty and otherwise only contributes leading POP debt. Choose the oldest token that remains at the end. Its producing PUSH occurs on the walk after some ordinary reachable prefix. After that PUSH, no suffix prefix can consume it, so the remaining suffix is a Dyck-prefix word. Balanced words have the standard decomposition into concatenated matched pairs; prefix words decompose into balanced segments separated by unmatched PUSHes. Induction on those decompositions places the suffix in `P_i`. The algorithm therefore reports the observation.

Activity and a forbidden active-family witness are existential observations per ID. Projecting away other IDs is consequently exact even if several independent IDs share one family. This does not claim exactness for conjunctions requiring two different IDs to be simultaneously active on the **same** walk, or for support projection whose definition is not union of active-family observations.

### Stronger exact theorem: all one-ID normal forms, without count bounds

The same balanced relation gives an exact finite automaton for **every** reduced context of one ID, not merely its active bit. Fix start and exit vertices. Construct states `(v,phase)` with phases `pop` and `push`. Every pair in `B_i` is an epsilon transition within either phase. Every original POP edge is a labeled POP transition within phase `pop`. Every original PUSH edge is a labeled PUSH transition from `pop` to `push` and within `push`. Start in `(start,pop)` and accept either phase at the exit. Other-ID operations, when asking for this one-ID marginal, are already epsilon edges. Multiple starts/exits and provenance coordinates need no new argument.

This finite automaton accepts exactly the normal-form words `POP^p PUSH^n` obtained from actual primitive walks. Its loops retain arbitrarily large `p,n` literally; no powers are equated.

For completeness, perform literal stack matching on any actual walk. Unmatched POPs occur before unmatched PUSHes: a PUSH preceding a later unmatched POP would either be matched to that POP or imply that POP was not unmatched. After deleting the unmatched letters, every interval between them is a balanced Dyck word. In particular, a matched pair cannot cross an unmatched POP or an unmatched PUSH; the stack matching rule would contradict unmatchedness. Hence the raw word factors as

```text
D (POP D)^p (PUSH D)^n,
```

where each `D` denotes a balanced subwalk, possibly empty. The corresponding epsilon/POP/PUSH transitions form an accepting run of the finite automaton.

For soundness, replace each epsilon `B_i` transition in an accepting run with its actual balanced witness walk. Concatenating these witnesses and the labeled edges yields an actual primitive walk. Each balanced interval evaluates to identity; the surviving phase-restricted labeled word is `POP^p PUSH^n`, already normalized. Thus its exact value is the accepted normal form.

The automaton has at most `2|V|` states after word expansion, and its only saturation prerequisite is the finite relation `B_i`. It can be exported as an exact one-ID residual language and recomputed after arbitrary finite prefix/suffix graph additions. This resolves the primitive POP/identity cycle without dropping its exact POP powers. It does not resolve mixed directed replay, and independent per-ID automata do not encode simultaneous tuple correlations. Keep the original labeled graph for those correlations rather than replacing it by the product of its marginals.

### Stronger multi-ID theorem: finite upward demand antichains

For any finite number `A` of actual attachment IDs, retain the simultaneous active-count vector `x` in `N^A`. This is a semantic vector of unbounded counts, not a complete registry of hypothetical future effects. Primitive one-sided append operations are monotone maps:

```text
PUSH_i: x_i -> x_i+1
POP_i:  x_i -> max(x_i-1,0).
```

An upward observable is a set `T` satisfying `x in T and y>=x => y in T` componentwise. Active membership of ID `i` is the upward set generated by its unit vector. A forbidden active-family witness is the union of unit-vector upsets for IDs whose fixed family fails the retained filter. These are source-grounded observables from `active_stack_items` and weighted filter checking. Intersection/union of such requirements also remains upward and retains simultaneous correlation across IDs.

For each vertex, maintain an upward set `U_v` of incoming vectors from which some finite continuation reaches an observer. Targets and guards are supplied as finite antichains of threshold vectors, or by an effective construction of those generators; the algorithm does not infer generators from an opaque predicate. The concrete active/filter targets above explicitly supply unit vectors. Initialize with the observer's upward target at its vertex and empty sets elsewhere. For an edge `v --t--> w`, add `pre_t(U_w)` to `U_v`; if that traversal also requires an upward guard `H`, add `H intersect pre_t(U_w)`. The latter is a generic guarded-observation extension. It does **not** assume a handler's concrete survival guard has that form: that use must be grounded in the actual output consumer. Filter violation needs no such added handler premise.

Represent each upward set by its finite antichain of minimal threshold vectors. For a generator `b`, exact preimages are:

```text
pre_PUSH_i(up(b)) = up(b with b_i := max(b_i-1,0))
pre_POP_i(up(b))  = up(b with b_i := 0       if b_i=0
                                          b_i+1   otherwise).
```

Other components remain unchanged. Union collects generators and removes dominated ones. Intersection takes componentwise maxima of every pair of generators and removes dominated ones. These equations follow immediately from `t(x)>=b`; they are exact, including POP at zero. Fixed finite words are handled by reversing their primitive preimage operations.

Termination follows from Dickson's lemma, with no numerical threshold cap. Here is the needed lemma's proof. Every infinite sequence in `N` has an infinite nondecreasing subsequence: either one value repeats infinitely, or every finite initial interval occurs only finitely and a strictly increasing subsequence can be selected. Apply this successively to each of the finitely many coordinates of an infinite sequence in `N^A`. The final subsequence is nondecreasing in all coordinates, so it contains an earlier vector below a later one. Thus `N^A` is well-quasi-ordered. Its antichains are finite; every element of a nonempty upward set lies above a minimal element by descending in its finite coordinate box. Every upward set consequently has a finite minimal basis.

More strongly, an ascending chain of upward sets stabilizes: otherwise choose a vector newly admitted at each strict increase. No earlier chosen vector can be componentwise below a later chosen one, since upward closure would already have admitted it. That contradicts the lemma. A finite product over vertices also has no infinite strictly ascending chain (some vertex would increase infinitely often). Every successful worklist update increases one of those upward sets; saturation must terminate. This is a mathematical finite-run proof, not a claimed polynomial resource bound.

Soundness is induction on saturation stages: initial demand is an actual observer; predecessor additions prepend one actual guarded edge to an actual finite witness. Completeness is induction on the length of any finite witnessing continuation: its final observer is initialized, and reversing its edges performs the exact preimages used by the algorithm. Consequently the least fixed point answers the observable exactly for **all** initial count vectors, including future concrete lower seeds. It does not assume a fixed finite seed population. A new finite source ID or edge changes the finite input system and can trigger a fresh exact saturation; no old arbitrary numeric cap is retained.

This theorem handles arbitrary cycles, simultaneous ID correlations and upward gates. It subsumes the active/violation conclusions above while the balanced construction separately gives exact one-ID normal-form languages. It still does not decide arbitrary non-upward observations, residual side placement after directed mix/swap, or complete full-context tuples. Runtime antichain sizes and thresholds can be large; termination is not a performance certification. No antichain implementation or executable verification is claimed in this producer note.

## 4. Exact self-edge omission: two different criteria

For a full semantic system, omission of a self-edge `e` is exact precisely when all its induced observations and obligations are already entailed by the retained graph, for every legal current/future insertion in the intended interface. This is semantic inclusion, not equality of endpoint representatives:

```text
Obs(G+e+H) = Obs(G+H) for every admissible future extension H,
```

together with preservation of registration, owner references, residual exports, and diagnostics required by the contract. Equality of canonical rows proves none of those conditions.

The walk subsystem gives a useful **proved sufficient rule**, rather than only that abstract criterion. A self-loop whose word contains POPs only, has no nontrivial filter/registration/owner side effects, and is observed only by existential active-family presence can be removed. Every traversal lowers each active counter. Delete those loop traversals from a witnessing walk. Every remaining append operation is monotone in the incoming active count, so the shortened walk has componentwise greater/equal active counts and the same final vertex. Any old active witness survives shortening. Conversely, every walk after removal existed before removal. All existential active observations are equal. This remains true after arbitrary future one-sided walk edges/seeds are added at the original graph interface. Vertices introduced solely to expand the removed edge's word are private and cannot acquire independent new source edges or observations.

This rule preserves **observations**, not exact residual contexts. It does not justify the baseline successor's unconditional same-row shortcut for a directed context carrying filters, output wrappers, Function swap, or future-lower obligations. A PUSH-only loop cannot use this rule: with an empty seed it creates activity that the zero-length walk lacks.

If instead the contract requires the self-edge transfer to equal identity on **each incoming contribution**, the one-ID left word qualifies exactly when `(p,n)=(0,0)`. If `n>0`, incoming zero separates it from identity. If `n=0,p>0`, incoming one separates it from identity. Thus even the primitive positive-active predicate distinguishes every nonidentity one-ID transfer from identity on some incoming state. Oracle's actual self-variable omission is an implementation fact; neither this theorem nor row canonicalization establishes its full successor correspondence.

## 5. Why full directed replay needs bracketed derivations

For one ID and All filters write weights as `(p,n,r)`, where `r` is the right POP count. The inspected `mix` appends right POPs to the left word, keeps a surviving active left PUSH on the left, and moves pure residual POPs to the right when both sides participate. Let

```text
A = right POP = (0,0,1)
B = left PUSH = (0,1,0)
C = left POP  = (1,0,0).
```

Then source replay gives

```text
replay(A,B) = identity
replay(replay(A,B),C) = left POP
replay(B,C) = identity
replay(A,replay(B,C)) = right POP.
```

The two final weights differ exactly. Applying `swapped` exchanges these residual-side observations, so side placement is not disposable metadata. The example uses one ID, one family, no filters, no unequal rows, and no overflow. It is a minimized algebraic counterexample, **not** a demonstrated source program producing both bracketings.

Therefore a regular expression of primitive path labels followed by an unspecified associative fold is insufficient for the full schema. A source replay bracketing invariant, an observational confluence theorem, or a representation retaining each actual bracketing is needed. The first two have not been derived here.

A finite derivation grammar retains exact bracketing without any such premise. Use nonterminals for finite kind-qualified endpoint-pair/bound slots. Primitive constraints supply constant leaves. Each possible row replay supplies a production `T -> replay(L,U)`; each Function child supplies its own `swap`, identity or `both_from_right` unary production; wrapper normalization supplies prefix/suffix productions; bound insertion supplies check/registration records followed by filter erasure. Keep occurrence/owner references as immutable operands. Define its reference meaning independently as all finite source-schema derivation trees evaluated bottom-up by the exact operations.

For fixed finite primitive endpoints and structural slots, construct all such syntactically possible productions by finite structural saturation. The construction terminates: each rule and nonterminal has a finite structural key, and adding a rule does not enumerate its values. Induction on an emitted rule proves every generated finite tree is a permitted reference derivation; induction on a reference derivation proves it is generated. Cyclic productions represent every finite replay power exactly.

This is a representation theorem, not a complete decision algorithm. A nonterminal's value set can be infinite. Checks may require evaluating predicates over that set. Also, source-level extrusion may add new endpoints and must separately establish finite endpoint construction before this fixed-graph theorem applies. Calling this grammar a finite memo and assuming every consumer terminates would merely move the original gap.

## 6. No finite exact contextual congruence, even one ID

Consider residual contexts `c_m=POP_i^m` for all natural `m`. They are all inactive when examined alone. For `m<n`, prepend `PUSH_i^(m+1)`. Composition gives an active PUSH under `c_m`, whereas `c_n` leaves no active PUSH. Thus every two residuals are separated by a legal source-algebra prefix and the inspected active-stack observer.

A finite primitive graph realizes the algebraic words using a PUSH self-loop at an entry vertex, an edge to a POP self-loop at an intermediate vertex, and an exit edge to the observer. The fixed graph therefore permits the required prefixes and all residual powers. It has only one attachment ID and one family. Any finite quotient claimed to preserve arbitrary future prefix composition must identify two `c_m`; the displayed prefix then refutes its exactness.

This is a sharp distinction: the observer itself has only two values, while the continuation-equivalence classes of residual contexts are countably infinite. The context-free algorithm in §3 still decides the observer for that fixed graph. Therefore neither finite observable range nor finite graph size proves finite contextual memo cardinality; nor does infinite contextual congruence prove undecidability.

A finite quotient is valid when its kernels are congruent under every retained constructor and its observers factor through it. That is the exact finite-abstraction condition. For an observation-only forward walk analysis, leading POP debt factors out by the proved append equation; for arbitrary future prepending it fails by the counterexample. A graph-derived finite PUSH budget is another sufficient snapshot condition, but no such budget was needed for §3 and none is claimed to follow from all source constructors.

### Actual residual consumers defeat an active-only cutover

Additional pinned-source inspection gives a concrete boundary, rather than only a hypothetical non-upward observer. `constraints/row_effect.rs:155–184,1190–1244` calls `subtract_row_items_from_left_stack_weight` with retained head families and transforms each active family's subtractability by removing those heads while retaining its ID and counts. Thus the immutable-family active-guard model is not closed under the whole row-residual operation. The normal-form automaton theorem retains exact counts for the fixed-family word fragment; it does not account for these evolving family payloads.

`compact/collect/mod.rs:1019–1043`, `compact_neg_row_upper_bound`, tests `cancelled.contains(fact.id)` before applying a subtraction fact to retained row items. Its `ConstraintWeight` is the alias of `StackWeight` in `constraints/mod.rs:3541`; the actual method is `crates/poly/src/types.rs:382–384`, `StackWeight::contains`. It checks ID-entry existence, including a pure leading POP entry, and directed-to-stack conversion preserves that entry. Identity and `POP_i` consequently have the same active vector zero but may produce different compacted residual support when fact `i` would filter a retained family. There is no full-support theorem from active-vector equality. The exact one-ID normal-form automaton does preserve identity versus nonzero leading POP and can answer their presence predicates; mixed contexts, fact incidence and changed family payloads still require their actual consumers.

The multi-ID antichain theorem therefore applies to active-stack/filter observations and explicitly supplied upward guards only. No complete handler subtraction, residual output, or principality conclusion is attached to it. The full consumer audit is a real correctness boundary, not a premise silently added to make the algorithm pass.

## 7. Transport, additions and publication

The finite graph/grammar must retain the construction facts already known at attachment formation. Canonical row equality reindexes coordinates; it does not merge two immutable attachment IDs merely because their rows or families coincide. Symbolic tails remain actual vertices and future lower routes. A fresh use alpha-renames attachment references and all endpoints consistently. Extrusion changes the row coordinates according to its owning polarity/level mapping, including coordinates inside retained words and tails. Intrusion unions distinct incident traversals and invalidates affected structural/query caches; it cannot replace an incident traversal by a row-global filter.

For §3, rebuilding the finite relations after a finite extension is an exact terminating operation. Incremental maintenance is possible but unproved here. This is not early callee resolution: a newly discovered Function adds its ordinary source-owned children when that comparison is actually reached. Full directed Function operations remain grammar nodes until their observation algorithm is established.

Rollback must restore the primitive graph, source IDs, bounds, filter registration, generation and derived relations together. The theorem concerns a committed immutable graph snapshot; it gives no automatic proof for an implementation's journal. No failed intermediate relation may be published. These statements preserve the task's invariants but are implementation obligations, not newly verified production claims.

## 8. Executable discrimination and next minimal gap

One lightweight Python process ran the independent candidate/reference probe at `/workspace/scratch/15155572c47b/proof_probe/path_observations.py`. It enumerated all 4,096 graphs on two vertices whose four ordered pairs independently carry any subset of epsilon/PUSH/POP edges, and both seed vertices: 8,192 graph/start pairs. Candidate finite `B/P` saturation matched literal reflected-counter walks enumerated to depth eight. Two focused words also passed: `PUSH PUSH POP` stays active, and `POP PUSH` becomes active. A separate tiny arithmetic probe found the exact three-weight nonassociativity example above. The exact normal-form automaton and antichain algorithms were proved here but were not implemented or run in this producer lane; any primary-owned executable evidence should be recorded separately. Neither probe invokes Oracle or the compiler. Depth-eight reference agreement is bounded consistency evidence; the unbounded claim rests on the mathematical proof, not that search.

No Cargo, compiler tests, builds, formatter, timing samples, Git mutations, children, or production edits ran. Direct source inspection used the fetched frozen Oracle objects. These experiments do not validate attachment source formation, output support projection, full mixed replay semantics, source soundness or principality.

The next minimal gap is concrete: integrate the inspected output consumer with the upward-observation theorem, and determine the observations required of mixed **bracketed** replay derivations. Then either prove those directed derivations admit a finite reachability analysis analogous to §3 or derive a source-owned replay/bracketing invariant reducing them to that subsystem. A test of associativity is now decisively insufficient; exact replay is already nonassociative. A wider finite count search cannot fix this gap. The source formation/owner/freshening and output projection gates remain explicit and must be integrated with the consumer, rather than assumed from the grammar's existence.

## Commit packet and dependency snapshot

Exact changed repository path: `notes/progress/2026-10-10-contextual-effect-path-theorem.md`. Research-only, unreviewed; own proof is not independent review. Writes are frozen at producer handoff. Shared task, design index and theory records are intentionally deferred to the primary. Suggested checkpoint message: `research: derive finite active-context observations and replay obstruction`.

Pinned baseline blobs:

```text
annotation-effect-hygiene-integration.md 4b7a8cba3c438ed1c1db914f7359e6da9fc43208
formal-filter-transition-contract.md     573e46b96f1f17754c92e74aa0296eb41479cd93
candidate_extrusion.rs                    0e10d00fc9db845c03d14537a4ae4bcd5fd81a5f
candidate_intrusion.rs                    ed363d7f0fea060eb19ce188294934e48589d591
lib.rs                                   2a43bea966b0ee78ec29f90a404e365710f0de97
```

The source-inspected algebra derives the natural-number composition equations and active-stack observer used here. Finite graph shape, actual incident source occurrences, and whether a particular full-source constraint can be represented by an associative walk are **not** inferred from canonical row identity. Full source correspondence remains unproved; no new premise is being promoted into language authority.

## Independent mathematical review and integrated executable

The `saturation_proof_review` compiler-referee pass independently checked the
normal-form decomposition/NFA, finite balanced saturation, exact antichain
preimages and termination, POP self-loop omission, and the pinned directed and
residual consumers. It found no blocking or major mathematical defect. The
primary applied its two minor corrections: explicitly supplied effective guard
bases and the actual `StackWeight::contains` source locator. The private
word-expansion interface and the short proof of Dickson's lemma are also made
explicit above. None of these clarifications broadens the theorem's scope.

The companion executable is
[`research_contextual_effect_saturation.py`](../../tools/research_contextual_effect_saturation.py).
It implements the exact one-ID automaton and simultaneous-ID upward demands;
the integrated verification/review record is
[`contextual-effect-saturation-results`](2026-10-10-contextual-effect-saturation-results.md).
The code is a research implementation, with no successor routing or second
production solver. Producer-era statements above that an algorithm was not
implemented refer to that lane's handoff; the companion records the later
implementation and its actual verification separately.
