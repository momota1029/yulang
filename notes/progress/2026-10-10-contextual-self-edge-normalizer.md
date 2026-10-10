# Constructive raw identity-self normalization

Date: 2026-10-10
Status: frozen producer research; independent review pending
Baseline: `f75c8d2fc27c8e5f61e13632b234d56314d2a62c`
Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Exclusive leases: this note and `tools/research_contextual_self_normalizer.py`
Scratch lease: `/workspace/scratch/15155572c47b/self_normalizer/`
Claim class: exact finite-grammar transformation theorem and reference checker
Production authority: none; no compiler or source-policy change

## Result and the gate actually closed by the construction

The identity self edge can be removed even when incoming facts are raw,
positive, recursively generated, and unbounded. Keep the original incoming
production `X -> E`, add `X -> mix(E)`, and remove the bare identity self
productions at X. Idempotence of mix replaces arbitrarily many self traversals
with the choice of zero or one mix at each incoming production. The exact set
of values at every original grammar vertex is preserved. This requires neither
normal stored facts nor solving the remaining recursion.

This is a constructive closure of the raw identity-self **representation**
problem. It is not a decision procedure for arbitrary recursive mixed-context
membership, global alternate-path redundancy, or the whole source inferencer.
The transformation is total on finite grammars even when their value sets are
infinite. A raw identity self is a mix transfer, so simple deletion without
factoring its incoming productions is still wrong.

Inputs: the reviewed unit theorem in
`2026-10-10-contextual-self-edge-erasure.md` §§2–4, frozen SHA-256
`7ac23eae82241f87f0922b32ae841c228cc018afb6a4c2c04a5ca5af3df443c9`,
and the immutable exact arithmetic operations/values in
`tools/research_mixed_debt_observer.py`, SHA-256
`c6f3d36462469494dcdaa5fd6e22029bcea0f5d48a258e5eb55bc41a65dfaf6c`.
The latter's restricted debt Grammar and clipped saturator are **not** used.
Its `operation` and `values(..., cap=None)` support the exact full DSL used here.
The proof has no finite-debt abstraction premise.

Governing source semantics remain annotation-effect-hygiene-integration §§1,4–6
and the active legacy-withdrawal policy. Root AGENTS, design-authority, testing,
research-lab and git-concurrency were read. This work neither selects a new
source restriction nor promotes this reference grammar to production routing.
The prior note's missing contextual formal constructor, attachment/filter
transport, full Call/hygiene, inference/principality and cutover obligations
remain at their actual owners.

## 1. Exact algebra and the recognizable raw transfer

Fix one actual attachment ID, one fixed family and the All replay label. Raw
contexts are natural triples `x=(p,n,r)`, with the exact leading left POP,
active left PUSH and right POP counts. An empty family does not erase counts
or entry presence. Write `I=(0,0,0)` and retain the prior note's equations:

```text
C((p,n),(q,m)) = (p+max(q-n,0), m+max(n-q,0))
R(x,y) = M(C(x.left,y.left), x.right+y.right)
M(p,n,r) = (p,n,r) if r=0 or p+n=0;
           (a,b,0) if b>0;
           (0,0,a) otherwise,
           where (a,b)=C((p,n),(r,0)).
```

M is idempotent. Every changed output has either zero right coordinate or zero
left pair; on either shape the next M is unchanged. An unchanged input already
has one of those shapes. Consequently `M^k(x)=x` when k=0 and `M(x)` when k>0,
for every raw x, without a count bound.

### Raw transfer recognition theorem

For each direction separately:

```text
(for every raw x, R(x,w)=M(x)) iff actual w=I;
(for every raw x, R(w,x)=M(x)) iff actual w=I.
```

Sufficiency follows because C has I as a left-pair unit and I adds no right
POP. For necessity restrict x to the normal subset, where `M(x)=x`, and apply
the reviewed maximal universal constant-unit theorem. That theorem quantifies
over raw constant w as well. Thus inspecting the actual I label recognizes
exactly the universal M transfer among constant replay labels.

It is incorrect to recognize any w with `M(w)=I`. The raw balanced nonidentity
`w=(0,1,1)` has `M(w)=I`, but for `D=(1,0,0)` both `R(D,w)` and `R(w,D)` are
`(0,0,1)`, whereas `M(D)=D`. Count cancellation inside an isolated label is not
the label's action when inserted into a later replay. The reference transform
therefore never normalizes a constant to decide whether it is I.

## 2. Grammar class and the finite transformation

A grammar is a finite set of named nonterminals with finitely many productions
`X -> E`. Expressions are finite, exactly bracketed tuple terms:

```text
const(p,n,r), ref(X), replay(E,F), mix(E), swap(E),
both_from_right(E), identity(E), prefix(p,n,E), suffix(r,E),
let(v,X,E), bound(v).
```

All counts are arbitrary naturals, including PUSH inside recursive productions.
Replay is directed and retains its written bracketing. Refs choose independently
unless a lexical `let(v,X,E)` chooses one value from X and binds that same
chosen value to every `bound(v)` occurrence in E. Nested bindings may shadow v
and restore the outer binding afterward. The chosen supplier itself has a
finite derivation; an empty supplier admits no let derivation even when the
body ignores v. These are the stable DSL's existing sharing semantics.

The semantics `L_G(X)` is the set of exact triples returned by **all finite
derivations** rooted at X. Infinite trees contribute no value. Equivalently it
is the least set solution of the monotone production equations. Rawness,
activity and debt are retained in these values. There are no guards, filters
or side-effect events inside this pure grammar semantics.

For a nonterminal X, identify these bare M-self productions syntactically:

```text
X -> replay(ref(X), const(0,0,0))
X -> replay(const(0,0,0), ref(X))
X -> mix(ref(X)).
```

Only the whole production is recognized. An identical-looking expression
nested below another operation is retained. A raw nonidentity constant remains
nonidentity even if M sends it to I.

**Algorithm N on an immutable original grammar:**

1. Record for each X whether it has at least one bare M-self production.
2. Remove every such M-self production.
3. Independently remove a plain reflexive alias `X -> ref(X)`. This ordinary
   no-op is vacuous on raw as well as normal values.
4. At each flagged X, replace every remaining original production `X -> E`
   by the pair `X -> E` and `X -> mix(E)`.
5. At each unflagged X, retain its remaining original productions unchanged.

Step 3 is needed for the promised elimination result: retaining a plain
`ref(X)` and applying step 4 would recreate `mix(ref(X))`. Such aliases can
arise when quotienting formerly distinct vertices. Their independent deletion
does not erase the actual M transfer of any identity replay.

Every retained E is unchanged, including its constant payload, ref occurrence
identity, bracketed operations and complete lexical let body. The new M sits
outside E. The algorithm does not push M inside E, normalize leaves, flatten
replay, split shared choices, identify attachment identities, or clip counts.
If X had no nonunit producer, X has no production afterward. Its empty least
language stays empty; this includes a self-only recursive vertex.

If X has `a_X` remaining original productions, the output has `2*a_X` at a
flagged X and `a_X` otherwise. Duplicates may be retained or removed using
exact structural equality; the supplied reference retains them. Every new
syntax wrapper has constant size and reuses the original immutable E object.
An implementation that copies expressions still increases total syntax size
by at most a factor two plus one mix node per wrapped producer. The transform
contains no loop over values or recursive derivation depth. On an already
validated grammar, this factoring pass has finite, linear syntactic cost in
the input syntax inspected. The reference's validation is separately finite
but is not claimed linear: it rebuilds the owner-name set for each production
and copies growing lexical scopes at nested lets. Those costs can be quadratic
and do not affect the transformation's output-size bound or exact-language
proof.

## 3. Exact preservation theorem and complete proof

**Theorem N.** For every finite grammar G in the class above and every original
nonterminal X,

```text
L_N(G)(X) = L_G(X).
```

No productivity, boundedness, normality, acyclicity, positivity exclusion or
known exact solution is a hypothesis.

### Inclusion from the original grammar to the transformed grammar

Take any finite original derivation rooted at X. Follow its initial chain of
bare productions which either are M-self or plain reflexive aliases. A plain
alias does nothing; each M-self applies M to its child result. Finiteness means
the chain ends at a nonunit original production `X -> E`. In particular, a
finite value derivation cannot end at a self rule without an eventual producer.

Recursively transform every proper nonterminal subderivation used to evaluate
E. This includes the supplier subderivation of a let and any ref occurrence
inside its body. The recursive calls have strictly fewer derivation nodes.
Preserve each chosen supplier value once and retain its binding across all
bound occurrences. By structural induction on E, the transformed evaluation
returns the same exact raw triple z as the original evaluation of E. Lexical
shadowing and independent siblings are unchanged.

If the removed root chain contained no M-self, choose the retained production
`X -> E`, returning z. If it contained at least one M-self, X was flagged and
the transformed grammar contains `X -> mix(E)`; choose it, returning M(z).
Idempotence says this equals the original chain's result for any positive
number of M-self traversals. Plain aliases interspersed in the chain change
neither case. This constructs a finite transformed derivation of the same
value. Induction proves original-to-transformed inclusion at every X.

### Inclusion from the transformed grammar to the original grammar

Take any finite transformed derivation. When its chosen production is the
retained E, recursively translate its proper nonterminal subderivations to G
and choose the original `X -> E`. Structural evaluation and explicit sharing
give the identical value.

When its chosen production is a generated `mix(E)`, its owner X was flagged.
There is at least one original bare M-self at X. Choose that original M-self
once, then choose the original producer `X -> E`, and recursively translate
all selected child derivations. The original self rule applies M exactly once
to the same E value, returning the transformed value. If a generated mix(E)
is syntactically also a retained production, either provenance choice supplies
a valid derivation. The transformation need not make grammar syntax injective.
Plain reflexive aliases need not be reinserted. This construction remains
finite and proves transformed-to-original inclusion.

Both constructions transport actual selected supplier values and preserve
their lexical correlation, rather than assigning fresh choices to repeated
bound occurrences. They work for arbitrary other recursive cycles because
they translate a supplied finite derivation, never enumerate the whole language.

### Infinite suppliers and nonunit recursion

For example, the raw supplier

```text
U -> const(0,1,1) | suffix(1,ref(U))
X -> ref(U) | replay(ref(X),I)
```

has `L(U)={(0,1,1+j):j>=0}` and
`L(X)=L(U) union {M(u):u in L(U)}`. N leaves the infinite U recursion intact
and changes X to `ref(U) | mix(ref(U))`, preserving that exact infinite set.
The checker verifies only this structural transformation; it does not attempt
to saturate the infinite supplier.

A nonunit recurrence such as `replay(ref(X),w)` for actual `w!=I`, or
`replay(ref(X),ref(X))`, is retained exactly. N neither decides its termination
nor asserts that all remaining self dependencies disappear. It eliminates
precisely the identified bare identity/mix self plus vacuous plain aliases.

## 4. Concrete observers using only active presence

The prior raw-separation argument used exact active-count observations. The
following stronger separation result uses only the boolean observation
`active(x) := x.n>0`, together with finite continuations from the same DSL.

**Theorem AP.** Any two distinct raw triples have a finite continuation whose
final active-presence bits differ. Identical triples agree in every finite
deterministic continuation. Thus all such boolean tests already distinguish
exact raw triples; an exact-count observer is not required.

For `x=(p,n,r)`, the extraction identities are:

```text
mix(both_from_right(swap(x))) = R_(2p) = (0,0,2p)
mix(both_from_right(x))       = R_(2r) = (0,0,2r).
```

Swap gives `(r,0,p)`, so both-from-right makes `(p,0,p)`, and M turns its two
POP locations into a right count 2p. The r extraction is the same calculation.
For a pure PUSH `P_k=(0,k,0)`, replay against `R_(2q)` is active iff `k>2q`.
If p differs between a and b, take `k=2*min(p_a,p_b)+1` and use the p
extraction. The smaller p passes and the larger p does not. If p agrees but
r differs, use the same threshold on the r extraction.

If p and r both agree while n differs, choose `K=p+r+1`. Exact replay gives

```text
replay(P_K,x) = P_(n+K-p-r) = P_(n+1).
```

Append the fixed left POP `D_t=(t,0,0)` by replay, with
`t=min(n_a,n_b)+1`. The smaller output is inactive and the larger remains
active. All chosen counts and continuations are finite. These calculations
use natural counts, not an a priori saturation threshold. Equal triples have
equal deterministic evaluation by structural induction, proving the converse.

For a nonempty fixed family, an Empty allowance sees these differing active
bits as different local filter-violation bits. An empty family still has the
algebraic active-presence bit; it cannot supply that particular Empty-filter
violation. This is an exact algebraic/local observer theorem. It does not
construct a whole source fixture or prove arbitrary source continuations are
admitted.

## 5. Future producers, quotienting, freshening and rollback

### Future production additions

Keep G as the original immutable snapshot and N(G) as its derived graph.
For a future original producer, form `G'=G plus (X -> E)` and recompute N(G').
Then Theorem N applies to the complete extended grammar directly. No universal
normal-fact restriction is needed for the newly added E. Appending E only to
the already-derived graph loses `mix(E)` when X's deleted self should have
acted on it.

The concrete mutation has old `X -> I | mix(ref(X))` and later
`E=const(1,0,1)`. The correct extended language contains I, `(1,0,1)` and
`(0,0,2)`. The old normalized graph plus the unwrapped new E omits `(0,0,2)`.
The checker tests this failure explicitly. The cheaper mutation with a balanced
raw seed whose mix is I would fail to detect this bug because I was already
present; the nonidentity debt output is intentional.

### Supplied SCC/alias quotients

A supplied vertex quotient maps every original ref and let supplier through
the vertex map and unions **original** producers at each merged owner. Apply
N to that quotient grammar afterward. This is a concrete algorithm; it does
not assume that old normalization flags alone survive a merge correctly.

For example, merge A and B into Q in

```text
A -> replay(ref(B),I)
B -> const(1,0,1) | ref(A).
```

The quotient creates a bare identity self and a plain alias self at Q. N
removes both and retains `const(1,0,1)` plus its mixed form, yielding exactly
`{(1,0,1),(0,0,2)}`. A second mutation merges an already flagged owner
`A -> I | mix(ref(A))` with originally unflagged B's raw producer. Quotienting
the already-derived graphs without refactoring B's newly merged producer
misses `(0,0,2)`. The test checks both seam failures.

The proof compares the **quotient original grammar** with N of that grammar.
It does not say that identifying vertices preserves the unquotiented
languages; merge is a separate semantic operation. Likewise this research
function receives a chosen quotient and makes no claim to implement actual
compiler SCC discovery, replay ordering, payload union or merge rollback.

### Fresh use and attachment identity

An injective row-vertex renaming commutes pointwise with N. A bare self stays a
bare self, a nonself stays nonself, I stays I, and each added `mix(E)` renames
to `mix(rename(E))`. The reference checker tests exact structural commutation.
Lexical binder names and constant payloads are left unchanged.

Within this one-ID theorem, fresh injective attachment renaming also commutes
exactly: it changes the actual ID's name and retains the triple and its fixed
family. Actual empty I remains empty, actual nonempty labels retain their
entries, and no operation here inspects an ID numerically. This is a statement
about applying the existing one-ID transfer under a lawful name map, not a
proof of arbitrary family-changing transport. The executable model has one
implicit actual ID; it does not erase an ID or recreate one from its family.
Row alias canonicalization is never an attachment renaming, and matching
family names does not license ID collapse.

### Rollback

Treat `(original G, derived N(G))` as one versioned pair. Restore the original
snapshot and its derived graph atomically, or restore G and recompute N(G)
before publishing. The reference uses immutable tuples and demonstrates
restoration of the saved pair. It does not implement the compiler journal.
Any associated origin, receipt, filter-registration, memo and attachment map
state must retain its own actual owner and participate in the real transaction.
An orphaned old flag or derived graph must not be reused after G rolls back.

## 6. Exact observations and the event boundary

The theorem preserves every original vertex's exact raw value set, and any
finite continuation on selected such values can evaluate identically. Explicit
let/shared selections can be transported consistently using the proof above.
The original nonunit expression is preserved whole; internal bracketing and
all named raw expression phases within it remain available in the corresponding
derivation. Unit chains are compressed by their exact resulting M value.

This does **not** preserve syntactic derivation shapes, the count of traversed
unit nodes, the number of duplicate propagation events, or arbitrary observers
of those deleted syntax occurrences. Intermediate original self-chain events
may have been repeated many times; the derived wrapper need only perform M once.
All-node traces indexed by original syntactic occurrences are therefore not
asserted equal as literal vectors.

The I recognized here is a pure residual context label with replay All.
Original source checks and persistent filter registrations are separate
obligations. Keep them at their actual owner/phase, outside the compressed
value-only self step; preserve already performed check results and later
registration duties. Once the same exact fact is supplied to the same retained
idempotent fact/check obligations, its result is the same. This permits exact
fact and set-of-check-obligation reasoning, not event-count erasure. A consumed
filter side effect hidden in an alleged I label is outside the recognized
pure grammar rule and cannot be discarded by this theorem.

The lower-self insertion's positive fact and complete endpoint/filter ownership
remain separate from this pure transfer. In particular the theorem does not
promote an upper-self transfer equivalence to generalized lower-filter ownership
equivalence. The actual production adapter must retain those facts/events and
their journaling. The prior reviewed source-owner bridge does not yet construct
the contextual formal payload and this note does not manufacture it.

## 7. Executable evidence and its limit

The reference function `factor_identity_self(rules)` is pure and validates a
full raw/PUSH tuple grammar. It imports the stable dependency without modifying
it, and checks that dependency's SHA-256 when running its tests. It preserves
each original constant tuple and retained E object. The representation has one
implicit attachment ID/family, so constants cannot accidentally be changed by
the separate row-vertex map.

Finite fixture comparisons use `debt.values` with **no cap**. The test helper
first checks a supplied finite pre-fixed witness under every production, then
iterates from empty to exact closure inside that finite witness. The witness
check proves finite termination of that fixture; there is no iteration cutoff,
hidden debt cap or claim to find finite witnesses for general recursion.
The infinite supplier example is deliberately never saturated.

Coverage includes raw seed plus I-self versus naive deletion; both replay
orientations and direct mix; the nonidentity balanced-label mutation;
unproductive/self-only and plain-reflexive grammars; retained nonunit self and
nonself recursion; late raw seeds; quotient-created self and newly merged raw
producers; injective fresh naming; immutable rollback; correlated children,
independent siblings and shadowed let binders; empty ignored let suppliers;
raw PUSH/prefix/suffix and bracketed replay wrappers; all 27 raw seeds with
coordinates 0..2 across the three M-self forms; and active-presence separation
of all 4,032 ordered distinct triples with coordinates 0..3.

Run command (single Python process, no children):

```sh
timeout 30s bash -c 'ulimit -v 262144; exec python3 -B tools/research_contextual_self_normalizer.py'
```

One preliminary run before adding the non-saturated infinite-supplier structural
checks passed 4,532 assertions and 99 finite fixture cases, with internal wall
time 0.0593 s. The final run passed **4,534 assertions, 99 exact finite fixture
cases and 4,032 active-presence separation pairs**, with internal wall time
0.0600 s. Both completed within the 30 s / 256 MiB budget; RSS was not separately
measured. Both of the two authorized Python-run slots are consumed. No Cargo,
broad tests, random
search, formatter, benchmark, source execution, production edit or Git mutation
is performed by the producer.

The comparison sides share the stable supplied arithmetic and set evaluator.
They check the transformation and named lifecycle mutations, not an independent
source-semantics oracle. The unbounded result follows from the constructive
proof, and the finite enumeration is supplementary consistency evidence.

## Commit packet and freeze boundary

- Leased paths: this note; `tools/research_contextual_self_normalizer.py`.
- Baseline/Oracle and both direct dependency hashes: above.
- New code SHA-256:
  `9eed7a25b97c8d7e94bbe29c706c8df263070605f07cc810aa07adc463b0196a`.
- Claim/review status: constructive exact-value theorem for finite unguarded
  grammars, producer-frozen and independently unreviewed; no production authority.
- Proposed checkpoint message: `research: factor raw identity self edges exactly`.
- Shared records intentionally deferred to primary/curator: record exact raw
  self factoring as the completed construction, distinguish it from simple
  normal-fact no-op erasure and the remaining arbitrary-recursion decision,
  preserve missing source/attachment/filter/lifecycle correspondence.
- Independent next action: review both derivation inclusions, shared-binding
  preservation, actual-I recognition, producer extension/quotient ordering,
  exact-check versus trace boundary, and the frozen executable reference.

No production/shared coordination file is changed. Writes stop at submission.
