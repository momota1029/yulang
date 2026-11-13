# Actual capture descent and the remaining source producer

Status: proof companion, partial result. No language decision or Step definition
is changed. This follows [the invocation-budget reduction](2026-11-13-point-class-invocation-budget.md)
and [the fixed-hole calculation](2026-11-13-hole-elimination.md).

The target remains accessibility of `GeneralNominalActualInspectionSteps.Step`
for every `Checked` registry and `InitialSource` satisfying `PointSource`.
`InstalledDepthBound` is **not discharged for that class**. The new results
derive the actual materialization-template bound, reconstruct historical
Paterson descent, prove static point/structural readback, and assemble a
sufficient finite-instantiation simulation into the existing accessibility
theorem. Constructing that simulation from the actual source is still open.
In particular, a conditional calculation is not a proof of source production.

## 1. Point readback and the fixed frontier

Use the existing `SourceFrontier.frontier S` as a finite, possibly redundant
list H. A `Walk` follows recorded structural children or nominal **type**
arguments whose endpoint identities coincide. Every traversed parent is
acyclic under the direct K2 relation. Its inspected vertices and terminal
vertex are distinct, so its length is less than the initial slot count.
Consequently all such origins occur in H. A cyclic terminal is allowed as an
opaque value; the path cannot inspect through it. This was the existing
finite-path theorem, not a new restriction on source recursion.

The missing semantic step for those paths is now proved. For a canonical
structural shape, two equivalent observations have equivalent payloads at
each common position. Pair and variant projections use their existing
inversion theorems. For a record, canonical labels are distinct. At every
finite observation depth, the field probe at label l sees exactly the
payload for l; transferring that probe across each direction of contextual
subtyping proves payload equivalence. No finiteness restriction is imposed
on the payload: it may be nominal or regular/recursive.

`actual_structural_readback` applies this inversion to the real normalized
state equation. Together with the existing point nominal-argument theorem,
`FrontierReadback.child_readback` represents each static edge by its actual
terminal source identity. `label_readback` transports observations through
an equivalent parent; induction gives `walk_readback` and `source_walk`.
`source_walk_survives` preserves this same identity and origin through every
actual-inspection Step, since each successor model is a predecessor model.

This proves readback of the specified static paths, **not** the assertion
that every later report is one of those paths. Initial pointness does not
force later observation descriptors to use point intervals. Report-to-path
extraction and readback of newly materialized inputs remain producer work.
Row parameters do not silently become type-origin paths.

## 2. A bound from the actual declaration producer

For inspection queries define the following syntactic costs:

* Variables, scalar, or deferred: 1.
* Structural node: 1 + shape arity + the sum of child costs.
* Nominal node: 1 + argument count + the sum of child costs.

Mutual induction on `schema`/`schemas` proves that a generated test has
origin projection level less than root level plus query cost, and arity
less than query cost. This is a theorem about the existing materializer.

The finite pattern menu of a declaration contains its associated RHSs,
the **normalized** where-argument patterns, and the where-output RHSs.
`request_menu` proves that every actual request comes from this menu,
using the real canonical emission permutation. The normalization in the
menu matches `inputRequests`; no normalization-idempotence assumption is
used. Duplicate requested output names or different target IDs do not
increase this maximum.

`SchemaVocabulary.recipe_vocabulary` additionally puts the actual recipe's
tests in one finite registry list: erasing origins from `schema`/`schemas`
leaves exactly the test vocabulary of the query, independent of mode and
target. `generated_vocabulary` and `request_menu` lift that equality to the
actual packet producer. This bounds the test values themselves, including
nominal names and record labels, rather than just their arities.

Let C be the maximum translated-query cost over all these menus in the
finite registry, with minimum 1. Constructor metadata and interpretation
are fixed along actual paths by the existing configuration theorem. Thus C
is source/registry-fixed. Define B(0)=1 and B(n+1)=1+C*B(n), and K=B(C).

A `Recipe` capture is a leaf. Each recipe node uses a test at its current
origin; descending to a child increases origin projection level by one.
It therefore cannot have constructor depth exceeding C. Induction on the
recipe yields both a finite enumerator membership and weight at most K,
where weight is 1 at a leaf and 1 plus the sum of child weights at a node.
The theorem `uniform_packet_weight` holds for every actual packet with a
visible declaration and the fixed constructor metadata/interpretation.
It assumes neither an invocation-depth bound nor a source budget.

`weight_bind` gives weight(t[σ]) ≤ weight(t)*M when M≥1 bounds all used
substitutions. Applied to an actual `OutputCertificate`, input uses are
single origin leaves and output-only binders use existing readbacks.
`uniform_certificate_growth` gives K*(previous+1). This proves finite local
growth over the retained input origins; it does not yet express those
origins over H.

## 3. Historical Paterson descent, including aliased expansions

For each finite actual execution prefix, `sites_lineage` reconstructs the
birth lineage of every registered site from the literal packet journal.
Initially there is just the root. An installation adds precisely its
clause children. The other transitions preserve sites and journal entries;
source formation excludes enqueueing an unregistered generated occurrence.
Each birth edge carries the visible declaration and the source seed used
by the existing invocation allocator. Hence it also gives `AtDepth`.

Here is the remaining *syntactic realization* required to apply Paterson.
Choose one finite pattern-vector label L(q) for every occurrence in the
whole finite journal, and one substitution σp for every installed packet p,
such that, after `counted`:

    L(parent p) = substArgs σp (head p)
    L(child p c) = substArgs σp (arguments c)

The same σp must serve the parent and every emitted child. These are exactly
the fields of `PatersonLineage.Instantiation`; the structure contains no
inequality or ancestry bound. The checked Paterson theorem then proves

    mass(L(child)) < mass(L(parent)),

where `mass` is `Roles.argsSize` after `counted`. Summing along the real birth
lineage proves d + mass(L(q)) ≤ mass(L(root)). This is `lineage_descent`;
`reachable_depth` connects it to every actual registered site.

Thus repeated expansion of aliased demands does not reset the birth depth:
every literal child still has its own strictly descending birth edge, **if
this coherent finite realization exists**. Labels may be reconstructed
retrospectively at each finite prefix; within that prefix they must serve
all historical packets simultaneously. Independently choosing a finite
substitution for each current report would not suffice.

No blanket “already aliased, skip installation” guard was added. Immutable
sites may request different associated names: `R(int,left=u)` and
`R(int,right=v)` still require realization of both equations even after
same-input merging. An implementation that physically expands a class once
needs a shared capture/child/output-binder arena and separate realization of
new requested names. Discarding the second packet wholesale is not that
implementation. No new infinite execution was established here.

## 4. Settlement height and substitution-tree growth

`SettlementHeight.Within state n q` measures **packet levels** of a genuine
`Discharged` proof. An alias step consumes zero levels. Suppose all packets
have the above realization and `AliasMass` holds: registered aliased sites
have equal label masses. Induction on the real `Discharged` proof gives

    Discharged state q → Within state (mass(L(q))+1) q.

At a packet node each child's bound is at most the parent's mass, by strict
Paterson descent. At an alias node the equality of masses transports the
same bound. The proof does not count or bound the length of alias chains.

`AliasMass` is explicit. Semantic input equivalence does not imply that
arbitrary syntax chosen to represent the inputs has the same size. The
producer must choose alias-coherent finite labels; an equality proof in the
model alone is insufficient.

For finite substitution trees define

    F(K,Q,0)   = Q+1
    F(K,Q,t+1) = K*(Q+1+F(K,Q,t)).

`SettledGrowth.Assembly` has input leaves of weight ≤Q+1 and composition
nodes with template weight ≤K. Induction using `weight_bind` proves weight
≤F(K,Q,t). Monotonicity in t follows from K≥1. `Assembly` is a syntax proof
tree, not another execution relation.

One further connection is essential: an actual settled output's
output-binder dependencies must be arranged into such a tree of bounded
height. A `Within` bound on where-dependencies does not automatically bound
arbitrary composition of entries in a trusted fact list. The correspondence
between binder uses, their producing children, and alias-shared output
realization remains part of the source producer. The local output growth
theorem above does not assume that correspondence has been proved.

## 5. The exact conditional budget now assembled

`SourceFactorization.Producer` is a sufficient finite-instantiation
simulation. It has no ancestry, accessibility, finite signature-cover, or
installation-count premise. Its data are fixed once for the source and
registry:

* A valid initial symbolic `Inventory`; its hole indices are `range |H|`.
* A finite test vocabulary and a fixed decoding from symbolic terms to
  finite pattern vectors.
* An invariant relating actual states to inventories.
* A `Realized` snapshot: a root term in the inventory, root-label agreement
  with its decoding, one simultaneous `Instantiation` for every historical
  packet, and `AliasMass`.
* Initial evidence and a local successor simulation: every actual Step
  extends the existing fixed-hole elimination trace and preserves both
  the invariant and a realized snapshot. Zero eliminations are allowed.

This interface intentionally separates syntax and semantics. `Data.holes`
fixes the **index set**, not a semantic interpretation of each hole;
`decode` is not itself a proof that a symbolic term denotes an actual input.
An actual source construction must supply those links in the invariant.
It must also justify which components stay opaque and which equations
really eliminate an existing unknown. This construction is not supplied.

Here is the fully proved numeric consequence. Let E(d) be the finite term
enumeration over the initial hole indices, fixed test vocabulary, and depth
d. Keep two different maxima:

    P(d) = max { mass(decode(t)) : t ∈ E(d) }
    Q(d) = max { weight(t)       : t ∈ E(d) }.

No equality or domination between expression weight and pattern mass is
assumed. Set G(d)=F(K,Q(d),P(d)+1), D(0)=initialDepth, and
D(n+1)=D(n)+G(D(n)). `assembled_replacement` converts an assembly with
height ≤P(d)+1 and the fixed vocabulary into exactly the depth bound G(d)
needed by the elimination trace. Its assembly and height are premises.

Each genuine elimination deletes one present hole and substitutes its
closed replacement **throughout** the inventory. The existing
`HoleElimination.Trace` theorem proves that there are at most h=|H|
eliminations, and that every resulting inventory term belongs to E(D(h)).
No monotonicity assumption on G is needed: extending the iteration adds a
nonnegative amount. The new `replay` composes these local traces along the
actual execution, while preserving the simulation invariant.

Therefore every root label has mass at most N=P(D(h)). Section 3 gives
ancestry depth ≤N for every prospective installing parent.
`SourceFactorization.installed_depth_bound` proves precisely the existing
`InstalledDepthBound` predicate, and `accessible` combines it with the
existing allocation, report, occurrence and signature-cover construction.
The final measure is missing signatures in that finite cover, with the
already proved accessibility of administrative steps when this measure
does not decrease.

`ClassPProducer` names the single remaining **simulation premise** in
`class_p_accessible` and `sourceBudget_of_producer`. This is not presented as
a logically weaker consequence of `InstalledDepthBound`: it is sufficient
to imply that bound and has more explicit obligations. Nor does packaging
those obligations into a structure establish them from `Checked` and
`PointSource`.

## 6. Remaining proof work and scope

| Link | Result in this change | Still needed from actual execution |
| --- | --- | --- |
| (a) Capture/readback | Canonical structural and point nominal paths represent actual terminal IDs; preserved by all Steps | Extract all relevant dynamic report paths and finite labels |
| (b) Producer over H | Actual schema recipes and local output growth have uniform syntax bounds | Interpret holes, read new IDs over H, maintain simultaneous labels and alias coherence |
| (c) Refinement history | A local fixed-hole simulation implies the global bounded trace | Construct that simulation for installation, aliasing and observations; separate genuine elimination from retained observation |
| (d) Descent and growth | Checked instantiated Paterson descent; historical depth; alias-aware packet height; template/substitution bounds | Connect actual output-binder readback trees to the packet-height bound |
| (e) Finite identities/reports and Acc | The existing complete reduction is now composed with the simulation | Discharge `ClassPProducer` |

The hard link remains semantic source extraction, rather than arithmetic or
enumeration. No semantic gap or new counterexecution was found; no owner
question or new guard is warranted by these results. Strict intervals retain
the local structural projection and template bounds, but point endpoint
readback cannot identify their interior actual origins. The actual-origin
plus facet invariant is still required there.

All new Lean work is additive. The primary constructed the proofs directly;
no `prover` launch role was available in this checkout. An independent
reviewer checked theorem scope and the alias/readback issues without editing
the proofs. Kernel compilation and the new standalone audit are the proof
checks; neither substitutes for the unconstructed source bridge.

## 7. Validation

Final commands, all run with working directory `lean/`:

| Command | Exit code |
| --- | --- |
| `lake build Yulang.GeneralNominalSourceFactorization Yulang.GeneralNominalFrontierReadback Yulang.GeneralNominalSchemaVocabulary` | 0 |
| `lake build Yulang` | 0 |
| `lake env lean Audit/GeneralNominalDepthBound.lean` | 0 |

The audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
`git diff --check` from the repository root exits 0. A byte-prefix check
verified that the aggregator only gained imports and that no other tracked
Lean file changed. All nine new modules are imported; prohibited proof-token
scanning passed. Frozen paths, branch, and HEAD are unchanged. No commits or
ref updates were made.
