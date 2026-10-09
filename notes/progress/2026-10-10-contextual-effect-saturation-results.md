# Contextual effect subtraction: cyclic algebra results and remaining consumer

Date: 2026-10-10
Branch: `research/simple-sub-intrusion`
Starting remote HEAD: `b69bb905983881506cdbb294805f2bdeacf77be9`
Integration base: `2a7cc93cdef1f55454814a0d0d01de7f5413c591`
Frozen Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Status: mathematical subsystem proved and independently reviewed; research
implementations verified; complete contravariant source integration remains OPEN
Authority: current direct user task and the existing annotation hygiene policy;
no new language choice, question-board bundle, numeric cap, or cutover
Mode: M3 for mathematical certification; M0 for shared-record synchronization

## Outcome

The exact POP/identity cycle has an unbounded family of contexts but admits a
finite **exact language representation**. A finite word graph with arbitrary
PUSH/POP cycles can also answer all future active-stack/filter demands by
terminating saturation. These results need neither a finite count bound nor
the assertion that only finitely many contexts occur. They resolve the cyclic
**one-sided append** subsystem, rather than reclassifying its termination debt.

They do not solve the complete directed contextual solver. In the inspected
Oracle algebra, normalized replay is observably nonassociative. Its real output
consumers additionally inspect pending POP presence and transform residual
families. Consequently neither a flat associative path fold nor an active-bit
or support-key quotient is justified for the whole source-owned attachment.
No production attachment datatype, partial constructor, fallback or parallel
solver was installed under an unproved correspondence claim.

The requested source and result remain unchanged:

```yulang
my f(cb: (int -> [io] 'c)): 'c = run_io: cb 1
```

```text
(int -> ['b, io] 'c) -> ['b] 'c
```

This result scheme is **not** an executed successor regression. Negative
explicit formal effects are still rejected by the actual candidate constructor.
No full source soundness/completeness, hygiene, principality or `yulang3` cutover
claim follows from these artifacts.

## 1. Fully proved statements and exact assumptions

The complete definitions and proofs are in
[the cyclic word and observation theorem](2026-10-10-contextual-effect-path-theorem.md).
They define reference semantics as actual finite walks and literal cancellation,
independently of the saturation algorithms. A finite graph and finitely many
currently formed attachment IDs are inputs; no solved callee, complete registry,
finite count envelope, or source-specific inference rule is assumed.

### Exact single-ID normal forms

For one ID, every left word has the unique normal form `POP^p PUSH^n`, with
natural counts. Let `B` be the least relation containing epsilon reachability
and closed under concatenation and `PUSH B POP`. It contains at most `|V|^2`
pairs, and each addition has an actual balanced-walk witness.

Literal matching factors every walk with that normal form as

```text
B (POP B)^p (PUSH B)^n.
```

The converse follows by concatenating balanced witnesses. A two-phase finite
automaton with at most `2|V|` states therefore recognizes **exactly all** normal
forms between the chosen endpoints. The finitely many states recognize a
language of arbitrarily long words; they do not identify arbitrary POP powers.
Both `p` and `n`, including pure pending POPs, remain observable.

This covers all cycle powers of `r --POP_i--> s --identity--> r`. It also covers
PUSH cycles, epsilon edges, empty walks, and finite graph additions followed by
recomputation. A separate one-ID projection is only a marginal; simultaneous
multi-ID correlation remains in the original graph.

### Simultaneous-ID upward demands

For fixed family payloads and active vector `x in N^A`, append PUSH increments
its coordinate and append POP maps it to `max(x_i-1,0)`. An active-ID observation
or a forbidden active-family observation is an upward set with explicit unit
generators. Finite conjunctions preserve correlation by taking componentwise
maxima of generators, rather than multiplying independent marginal answers.

Backward predecessor propagation uses exact thresholds:

```text
PUSH_i predecessor of b: b_i := max(b_i-1,0)
POP_i predecessor of b:  b_i := 0 if b_i=0, otherwise b_i+1.
```

Dominance removal preserves the represented upward set exactly. Every genuine
update strictly increases an upward set. The proof of Dickson's lemma and its
ascending-chain consequence in the theorem note establish termination on the
finite graph, without bounding threshold magnitudes or iterations. Induction
on actual finite continuations proves soundness and completeness. The final
answer covers **every** initial vector, including a later-arriving lower bound.
Generic upward guards/targets must have supplied finite generators; the source
active/filter cases derive those generators directly.

This is an observation summary, not an exact contextual congruence. It does
not erase the primitive graph or authorize support-representative replay.

### A concrete self-loop omission rule

A POP-only self-loop may be omitted for existential active-family observations
when it carries no filter registration, source obligation or other side effect.
Deleting the loop only increases the active vector, and subsequent append
operations are monotone. Every old observing walk has a shortened observing
walk; every retained walk already existed. Private word-expansion vertices
remain private under future extensions.

This proof preserves those observations, not the exact set of residual words.
It gives no permission to erase a self-edge before its source-owned checks or
to apply the rule to mixed Function contexts.

## 2. Refuted statements

[The reviewed counterexample packet](2026-10-10-contextual-effect-counterexamples.md)
contains exact derivations and distinguishes unrestricted algebra witnesses from
demonstrated source formation. Its published checkpoint is `dd6b02ad`.

| False unrestricted claim | Small discriminator |
| --- | --- |
| Equal nonzero support is exact future replay equivalence | `PUSH_i` and `PUSH_i^2` share the support key; right `POP_i` leaves identity versus one active push. A filter excluding its family distinguishes them. |
| Finite attachment IDs yield a finite exact context quotient | For `n<m`, a fixed continuation `swap; replay(PUSH_i^(n+1)); active check` separates `POP_i^n` and `POP_i^m`. Every pair is distinguishable over natural counts. |
| Normalized directed replay is associative | With `D=left POP`, `R=right POP`, `P=left PUSH`, `(D replay R) replay P=R`, while `D replay (R replay P)=D`. Another replay with `P` separates them by active-family checking. |
| Equal row endpoints justify dropping every contextual edge before checking | Under the uniform insertion contract, `x <: x` carrying filter `{E}` registers a future check; deleting it loses a later `F <: x` conflict. Oracle's own early admission is a different guarded contract, so this is not a claimed Oracle source bug. |
| Canonical row/family identity identifies attachment authority | Actual shared-tail/cached-row constructors select the same row but allocate fresh subtraction IDs. `PUSH_i;POP_j` does not cancel when `i != j`. |

The first three are exact mathematical statements about the inspected algebra's
natural-count lift. They are not claims that a complete source program generates
all their operation contexts. Oracle's finite-width saturating arithmetic is
not used as a theorem about unbounded counts.

## 3. Real source consumer boundaries

[The operational correspondence audit](2026-10-10-contextual-effect-source-correspondence.md)
records all seven requested inputs and the actual Oracle constructors/consumers.
It is an audit, not a replacement proof of the existing conditional transport,
owner or lifetime theorems.

The negative concrete attachment owns a fresh ID, a resolved annotation set,
an inner row with connected symbolic tails, a positive PUSH view, a filtered
negative view, and its matching output POP predicate. The enclosing output
wraps both Value and Effect. `NonSubtract` therefore participates in future
latent Function propagation; it is not an effect-only support bit. Function
argument/value and argument/effect ports use `swap`, result ports retain the
context, and the pure argument-effect branch has its distinct source rule.

Insertion consumes the left filter before storing a bound. The check and its
future-lower registration remain owned separately. No permit, emitted concrete
contribution, or subtraction authority can be inferred just from an allowance.

Two actual consumers prevent overclaiming the new theorems:

1. `row_effect.rs` replaces an active residual family `S_i` by `S_i \ H` after
   matching the retained heads `H`, preserving ID/count and introducing a
   residual `gamma`. The original annotation authority and the evolving
   residual payload cannot be silently treated as the same immutable set.
2. `compact_neg_row_upper_bound` observes `StackWeight::contains(id)`, including
   a pending POP. Identity and a pure `POP_i` both have active depth zero but
   can give different projected heads. With multiple declared facts this is a
   correlated conjunction of entry-presence conditions, not only an upward
   predicate of active depths.

For the latter boundary, appending POP maps `(p,n)=(0,0)` to `(1,0)` but maps
the larger `(0,1)` to `(0,0)`. Thus the exact predecessor of entry presence is
not upward in `(p,n)`. Adding the pending-pop coordinate to the existing
antichain algorithm does not establish a proof. This is a specific failed
extension, not an undecidability claim.

## 4. Implemented and verified work

Only research notes/checkers and navigation records are changed by this work.
The two algorithms run in
[`research_contextual_effect_saturation.py`](../../tools/research_contextual_effect_saturation.py).
The separate algebra vectors run in
[`research_contextual_effect_counterexamples.py`](../../tools/research_contextual_effect_counterexamples.py).
Neither is installed as a production constraint solver.

| Exact command | Verification and its limit |
| --- | --- |
| `timeout 10s python3 -B tools/research_contextual_effect_counterexamples.py` | 729 literal/count comparisons; 528 pair distinguishers; support, grouping, self-filter and separate-ID vectors. The universal arguments are proofs in the note. |
| `timeout 30s python3 -B tools/research_contextual_effect_saturation.py` | 256 cyclic word graphs; 15,182 bounded actual walks; 3,304 accepted normal forms decoded to literal witnesses; 12,348 complete finite-DAG observer queries; focused cyclic and identity controls. |

The saturation checker additionally queries exact powers as large as `10^30`,
including even/odd languages. This discriminates count truncation; it is not
the proof of unbounded exactness. It also checks simultaneous-ID correlation,
same-family ID independence, arbitrary later initial-count queries, row-coordinate
graph edits, and separate immutable-snapshot rebuilds. These are model controls,
**not** actual successor Function, intrusion, freshening or rollback tests.

The independent mathematical reviewer accepted the NFA and antichain proofs
with two minor precision repairs (effective guard inputs and the actual
`contains` owner). The independent executable review found that materializing
an edge iterator then rereading the exhausted input could omit observer edges
or bypass guarded-input rejection. The producer repaired both uses to read the
materialized snapshot and added iterator/list equivalence and guarded-iterator
rejection controls. The snapshot evidence label now says isolation, not rollback.
The final fresh `saturation_repair_review` pass independently closed both
findings, checked the exact two-dimensional basis `{(0,2)}`, and reran the
suite plus its own iterator controls without a new finding. The repaired
executable's SHA-256 is
`04d61ffe8adf411cfc766f47e04bb742b2178810dcd016e300f8bae5b0fcd9c9`.

No Cargo/Oracle/compiler tests or performance benchmarks are claimed. Existing
compiler sources and test contracts were not modified by this artifact, so
unchanged broad suites were not run. Bounded enumeration is consistency and
regression evidence; it is not substituted for a general proof. No process
timing samples were collected. Each checker invocation uses a single lightweight
Python process with an external timeout, which limits the experiment and does
not alter the algorithm's semantics.

## 5. Integration and next smallest research cut

The concurrent upstream `2a7cc93c` added ordinary inline colon-application
projection. It was fast-forwarded and inspected before integration; its own
[source bridge record](2026-10-10-colon-application-source-bridge.md) governs
its five HIR tests. Those changes/tests are not attributed to this work. The
solver algebra and annotation dependencies of this proof did not change.

The next smallest mathematical cut is **one authentic attachment ID with mixed
left/right replay and Function variance**, retaining the actual replay tree:
construct a terminating exact active-stack/filter observer for its cyclic
derivations, or derive a source-owned invariant that reduces them to the proved
append subsystem. Bracketing must not be discarded merely to use a path
semiring. This cut does not require complete Call semantics, but it does require
the real source constructor and consumed-filter records rather than assumed
generic contextual edges.

Changed residual families and complete support projection remain subsequent
explicit consumers of that representation. Production source construction,
journal coverage, genuine parent/copy intrusion, per-use freshening and the
requested callback scheme remain open. No existing proof-DAG node is changed
to CLOSED. Existing conditional hygiene/transport/owner/lifetime premises are
retained exactly; this work neither reproves nor silently strengthens them.
