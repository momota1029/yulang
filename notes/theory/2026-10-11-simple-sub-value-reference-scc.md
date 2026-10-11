# Simple-sub variable values, references, and copy-family cycles

Status: unreviewed research-only source characterization and bounded derivation
Reference baseline: `simple-sub-reference` at `9bae772624c23b52a93c1b226157e16898b4d9db`
Yulang baseline inspected: `330d5432aff4b1f9655d501e17a9eefb7e75e098`
Output lease: this file only; leaf assignment, no delegation
Authority: current user correction that vertices are Value variables and edges
are references in their values, plus the parent/copy decision below
Promotion boundary: no parent inference theorem, intrusion correctness,
soundness, principality, or implementation conformance is closed

## Frozen question and scope

For each finite snapshot of the pinned reference's mutable `SimpleType`
representation, identify the variable references actually stored in a
variable's bounds, including references nested in structural values. Derive
the effect of the real storage and copying constructors on those references;
give one source-term cycle and one bounded copy-family cycle. A comparison
obligation `a <: b` is not itself a graph edge. Preserve the original variables,
their identities, bound slots, levels, and polarity of each copy.

The Scala reference calls its vertices `Typer.Variable`; it has no separate
`Value` kind, assigned-value field, retained extrusion-parent field, SCC
routine, or intrusion operation. The graph below is the exact occurrence graph
available from this representation. Its identification with the successor's
user-intended Value-reference graph is an **open bridge**, not a definition of
successor semantics. No effect/provider/witness/residual lineage is modeled.
The copy-family example is an operation trace, not a claimed parsed-source
witness. Arbitrary custom contexts, invalid manually edited states, and all
source completeness/termination/principality claims are excluded.

## Exact source owners

All Scala locators are under `shared/src/main/scala/simplesub/` in the pinned
reference checkout `/home/momota1029/rust/simple-sub-reference`.

| Owner | Locator | Relevant responsibility |
| --- | --- | --- |
| Bound/value representation | `Typer.scala:192–233` | `SimpleType`, `Function`, `Record`, `Primitive`, mutable `Variable` lower/upper lists; immutable level |
| Explicit reference traversal | `TyperDebugging.scala:14–32` | Variable children are both lists; structural children are function ports and record fields; `getVars` follows actual children with a visited set |
| Source constructors | `Typer.scala:48–84` | Recursive placeholder, lambda, application, field selection, record, let, scheme use |
| Accumulation and propagation | `Typer.scala:87–128` | Branch-selected stores and comparisons against opposite bounds |
| Extrusion | `Typer.scala:131–159` | Cache by original variable and polarity, lower-level fresh copies, selected bound copying and original-to-copy insertion |
| Instantiation | `Typer.scala:166–188`, `199–207` | Freshen quantified variables and both bound lists; reuse unquantified variables |
| Recursive output | `Typer.scala:238–257` | Follow polarity-selected bounds, detect repeated `(variable, polarity)`, emit recursive type binder |
| Compaction | `TypeSimplifier.scala:49–83`, `102–157` | Distinguish bound-only cycles from structural recursion; close variable-only selected bounds before structural traversal |

The `parents` set in `TypeSimplifier.scala:55–72` is a traversal ancestry set,
not retained extrusion genealogy. `constrain`'s cache contains comparison
pairs, not adjacency or an SCC computation. The inspected shared Scala sources
contain no Tarjan/SCC/intrusion implementation.

Governing Yulang sections: `2026-10-10-parent-copy-scc-intrusion.md`, “Direct
decision”, “Selected operation and compiler responsibility”, “Retained
boundary”; `2026-10-11-yulang-inference-top-level-principles.md` §§1–3 and
“Authority and integration”. The approved operation retains actual copy
parents and equates qualifying parent/copy variables in the same SCC. This
reference characterization does not replace that operation.

## Reference occurrence relation

Let `occ(t)` return the variable objects occurring in the finite structural
payload `t`, stopping at each variable rather than expanding its bounds:

```text
occ(Variable b)     = {b}
occ(Primitive _)    = ∅
occ(Function(l,r))  = occ(l) ∪ occ(r)
occ(Record(fields)) = ⋃ occ(fieldType)
```

For a snapshot, retain labeled references
`a --(lower/upper, bound slot, structural port path)--> b` exactly when `b`
occurs at that path in that stored bound of `a`. The ordinary directed graph
for mutual reachability forgets these labels only for the SCC query:

```text
a →ref b  iff  b ∈ ⋃ {occ(t) | t ∈ a.lowerBounds ++ a.upperBounds}.
```

This contracts structural nodes between successive variable objects in the
literal `children` relation. Expanding a target variable's bounds makes a
longer reference path; it does not add a new direct edge. A function-domain
reference remains an owner-to-contained-variable reference even though
subtyping flips variance at that port. Cache entries, reverse inequality
directions, scope membership, and copy genealogy contribute no extra edges.

There is also a distinct **consumer traversal**: at `(a,+)` inspect lower
bounds; at `(a,-)` inspect upper bounds, flipping polarity in function domains
and preserving it in codomains/record fields (`coalesceType:247–255`). This
explains output meanings and recursive binders. The vertex set requested by
the user remains variables, not comparison pairs or polarized obligations.
An SCC in the unpolarized occurrence graph alone need not produce a recursive
output binder or justify equality.

## What the constructors actually store

For distinct variables `a,b`, the first matching `constrain` branch controls
the store. If `level(b) ≤ level(a)`, it stores `b` in `a.upperBounds`, giving
`a →ref b`. Otherwise it stores `a` in `b.lowerBounds`, giving `b →ref a`.
At equal levels, only the first store occurs. It does not automatically store
both directions. Later propagation may create other stores, but those must
be traced through their own matching branches. Same-object comparison returns
before storing (`Typer.scala:93`).

For structural bounds, the same owner-to-occurrence rule applies: storing
`Function(b,c)` in `a.upperBounds` creates references from `a` to `b,c`, not
an inequality edge between function endpoints. Pure structural comparisons
create no bound reference at that step; they recursively compare ports.

Extruding original `p` at target level `d < level(p)` creates copy `c` with
level `d`, registering `(p,pol) -> c` **before** traversing bounds:

```text
positive: p.upperBounds ::= c; c.lowerBounds = map(extrude +, p.lowerBounds)
negative: p.lowerBounds ::= c; c.upperBounds = map(extrude -, p.upperBounds)
```

Both insertions are physical references `p →ref c`; the negative one does
not become `c →ref p` because its comparison meaning is `c <: p`. Copied
payloads may refer to cached copies, fresh copies, or retained lower-level
variables. Their actual contents determine references out of `c`. The local
cache is discarded after its extrusion call; it is not a permanent parent
record. Opposite polarities have different cache keys.

Freshening registers its new variable before recursively copying **both**
lists. Hence it preserves cycles among freshened variables and sharing within
one instantiation; variables at or below the scheme limit remain the original
objects. Stored lists alone do not prove that every future consequence is
activated. Opposite-bound propagation is explicit in `constrain:117,120`;
extrusion/freshening list assignments perform no such propagation themselves.

## Source-term cycle and its instantiation

Take the source AST `Let(true,"p",Rcd(List("next" -> Var("p"))),Var("p"))`
at level 0. `typeLetRhs` allocates `p₁` at level 1 and gives the RHS a
monomorphic binding to that very object. The RHS record therefore has payload
`Record(next:p₁)`. Its final comparison against `p₁` stores that record in
`p₁.lowerBounds` (`Typer.scala:50–55`, `62–63`, `79–83`, `118–120`).
Consequently `p₁ →ref p₁` is an actual structural self-reference.

The body instantiates `PolymorphicType(0,p₁)` at level 0. Freshening creates
`p₀`, registers `p₁ -> p₀` before copying, and sets
`p₀.lowerBounds = [Record(next:p₀)]`. Thus the reference survives
generalization/instantiation as `p₀ →ref p₀`; it is not a cache-pair artifact.
Positive output traversal revisits `(p₀,+)` through a record field and can
emit a recursive binder. This is a manual derivation from source constructors,
not an executed parser or inference test.

## Bounded uncle/nephew cycle from real operations

Start with empty `P` at level 2; each extrusion below uses its own empty cache.
Names denote exact returned/new objects, not copies chosen independently.

1. `extrude(P,false)` at level 1 returns `C`. It stores `P.lower=[C]`;
   `C.upper=[]`.
2. `extrude(P,true)` at level 0 returns `U`. It registers `P,+ -> U`, inserts
   `U` into `P.upper`, and copies `P.lower=[C]`. Recursing on `C,+` creates
   `N` at level 0, registers `C,+ -> N`, inserts `N` into `C.upper`, and copies
   the empty `C.lower`. The result is `U.lower=[N]`, `N.lower=[]`.
3. `constrain(Record(next:U),N)` stores `Record(next:U)` in `N.lower`.
   Its structural level is 0, the RHS variable branch matches, and `N.upper`
   is empty, so there are no further comparisons in this step.

Complete bound/reference snapshot:

| Variable | Level | Lower bounds | Upper bounds | References |
| --- | --- | --- | --- | --- |
| P | 2 | C | U | P → C, P → U |
| C | 1 | empty | N | C → N |
| U | 0 | N | empty | U → N |
| N | 0 | Record(next:U) | empty | N → U |

The extrusion genealogy is `P` parent of `C,U`, and `C` parent of `N`.
Therefore `U` is `N`'s uncle, and their actual value references form SCC
`{U,N}`. Neither genealogical edge nor the judgment in step 3 was substituted
for a reference. The return reference is the stored record field. In positive
output traversal the cycle passes through a record and is structural recursion;
`compactType` resets its traversal-parent set there (`62–64`).

All bound levels in this example satisfy the reference's declared invariant.
Thus that invariant does **not** rule out family SCCs: an uncle and nephew
can be copied to the same level. No exact AST emitting this entire operation
trace has been derived, and the example does not establish intrusion eligibility
for direct parent/copy `P/U` or `C/N`.

## Level argument, applicability, and remaining bridge

The narrowly valid implication is: **if** all bounds in a snapshot satisfy
`Typer.scala:221–222`, every occurrence edge defined above satisfies
`level(target) ≤ level(owner)`. Structural levels are maxima; taking each
structural occurrence gives the inequality. Along a cycle all these levels
are equal. This implication concerns only ordinary stored-bound occurrences.
It is not a proof that every caller of the public APIs preserves the declared
invariant, and it does not constrain any additional successor Value payload,
representative, retained-parent, or transport edge class.

For the traced extrusion stores, the direct original-to-copy insertion strictly
decreases level; copied bounds refer to target-level copies or retained
lower-level variables. Genealogy is separate from adjacency. The uncle/nephew
example satisfies the implication and still forms a cycle. Inferring that the
approved successor cannot have qualifying parent/copy SCCs would require an
unestablished identification of its exact value-reference edges and level
behavior with these ordinary reference edges. No such conclusion is made.

In this exact four-object trace, the parent/copy pairs are `P/C`, `P/U`, and
`C/N`. They are event-derived annotations: the Scala objects retain **none**
of them as parent records. None belongs together to SCC `{U,N}`. Moreover,
any extension of this snapshot using bound operations that preserve the
declared nonincreasing-level condition still cannot create a return path
from the lower-level member to its higher-level parent. This conditional
obstruction applies to these exact event pairs and ordinary occurrence edges,
not to the user's selected operation. It is a concrete reference-to-successor
operational mismatch/open issue: the pinned reference neither constructs nor
consumes a qualifying parent/copy SCC by that mechanism. It provides no
normality or semantic-success certificate for the successor.

The next required bridge is a constructor/consumer correspondence that names:
the successor Value-variable payload and its direct reference fields; which
source/extrusion/freshening operations emit each edge class; how parent identity,
polarity and levels survive copying; and the graph actually consumed by SCC
processing and equality. It must explain the user's parent/child and
uncle/nephew cases on those exact objects. Inequality direction, stored
comparison IDs, and provenance alone cannot supply missing references.

Independent review and a source-qualified copy-family witness remain pending.
Complete Call, effects/hygiene, joint lineage, all-source inference, soundness,
principality, and F5 replacement are outside this bounded result.

## Checks and dependencies

Read-only `git rev-parse`, `git status`, `git ls-tree`, `nl`, `sed`, `rg`, and
`sha256sum` established the pinned checkout, exact source locators and hashes.
`git diff --no-index --check /dev/null <leased-path>` emitted no whitespace
diagnostics (exit 1 denotes the new-file difference); dependencies were
rehash-checked unchanged before handoff.
No tests, builds, probes, Oracle runs, Git mutations, or child jobs ran.
Local work was bounded file inspection and this note's construction; no
measurement budget was consumed. Runtime requested by routing policy:
GPT-6.1 Sol/high; observed model/effort metadata unavailable to this leaf.

Direct dependency SHA-256:

```text
Typer.scala          f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9
TyperDebugging.scala  8f0088c5ff729bb2f787ab2304529c0df5ed0711b29f10bef5398e41cb8a2d6a
TypeSimplifier.scala 618b63f63e71c31890eb36cb18be474bfd31732173c159132306f0e14dc37d2b
parent-copy decision 8ae4348a93dce6df1852a34b2294ebc5e4e256d8b018c1f6eaad42c502470a8e
top-level principles edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389
```

No dependency was changed by this leaf. Shared task/theory/index records are
intentionally deferred to the primary; proposed delta: link this unreviewed
reference characterization and keep the selected Value-reference/SCC bridge
and parent inference theorem OPEN.
