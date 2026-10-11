# Static Value-reference semantics for Simple-sub intrusion

Status: Draft; mathematical design proposal; Apply-result ownership in §3
selected by the user on 2026-10-12; source construction, transport proofs and
implementation remain open
Scope: Value ownership, source references, and their transport through extrusion/fresh use
Baseline: `3fa72e768c5a31e12ff44061d119102efca9aef3`, `research/simple-sub-intrusion`
Authority: `2026-10-10-parent-copy-scc-intrusion.md`, Value-reference SCC clarification and selected operation; `2026-10-11-yulang-inference-top-level-principles.md`

## 1. Candidate interpretation and established discriminator

One candidate is a **static source-value graph**: a Value variable owns a
source value description, and a reference edge records a resolved Value
reference occurring in that description. This is independent of a runtime
provider and inferred type. It is not a heap graph of one execution or a graph
of possible outputs. The user-selected Apply result-row equation is recorded
in §3 and the authoritative parent-copy design. This document remains a draft
for the other Value constructors, their native row correspondence, and
transport; it is not selected as the complete native semantics.

The accepted examples `host → outer`, `outer → x`, `g → outer`, and `g → g`
establish that source references can cross lexical scopes and include a
self-reference. The user's `odd`/`even` example adds a stronger discriminator:
the outer `odd` body references the locally bound `even`, while `even`'s
initializer references the outer `odd`. Thus the source-owner graph contains
`odd → even` and `even → odd`, so the two binders share a nontrivial SCC even
though they are introduced at different lexical levels. Any strict ranking
that must increase along every Value-reference edge is impossible for this
graph. This source graph does not by itself identify native solver rows or
prove an extrusion parent/copy pair qualifies for intrusion.

The two interpretations differ on minimal sources:

| Source | Candidate static source-value graph | Runtime output-object graph |
|---|---|---|
| `id x = x` | The Lambda's owned body contains a resolved Name of `x`, so `id → x`. | The closure does not capture its formal at construction; after a call, its returned value aliases that call's argument. |
| `konst x = 0` | The body is a literal, so there is no `id`-like edge to `x`. | The closure has no formal capture; after a call, the output is the literal, even though argument entry still runs. |
| `f x = g; g y = f` | The owned bodies give `f → g` and `g → f`. | Recursive closure environments can also point both ways; this example alone does not distinguish the models. |
| `odd` contains local `even`; `even` calls outer `odd`; `odd` then calls local `even` | The source-owner edges are `even → odd` and `odd → even`, crossing lexical levels in both directions. | Actual runtime existence of either function closure depends on evaluation; the static references are present before that execution. |
| `invoke f = f 1` | The source description has the resolved Name reference to `f`, independent of provider choice. | The Apply output may be a literal or a closure with different captures for same-typed providers; its edges cannot be known from the Apply type alone. |
| `host` whose body initializes local `outer` then returns `outer` | The source body has `host → outer`, as in the accepted example. | At closure creation, `outer` does not yet exist as a runtime object, so no such capture edge exists. |

The cross-level example establishes the source-reference edges at the
source-owner level. Whether and how those edges are represented by native Value
rows remains a separate construction and transport obligation. Runtime output
objects remain relevant to complete Call typing and effect witnesses, but the
accepted operation does not equate them with SCC adjacency.

The graph is not the source binder graph alone: its vertices remain actual
solver Value variables, including extrusion copies. A constructor must retain
the correspondence from each owned source description and reference occurrence
to the actual Value-variable identity in that solver history. The definition
below fixes that correspondence as part of the redesigned algorithm; proving
its realization and implementing its consumer remain open.

## 2. Mathematical state and four separate relations

Let a source value fragment be a resolved expression tree with stable source
occurrence identities. A binding initializer owns its fragment. A nested local
initializer is a separate fragment and is excluded from the enclosing
fragment; the enclosing block's final expression remains in its fragment.
Lambda bodies remain in the Lambda value fragment. This is the ownership rule
that yields the accepted `host/outer/g` edges.

Each fragment `d` is introduced with an actual native Value row `owner(d)`.
The fragment is a static source-value description, so it exists before a
callee has a concrete provider and while an Apply is pending. Each resolved
Name occurrence `o` in `d` has its original binder target `target(o)` and a
native target row `row(o)` in the same inference history. Then:

```text
Own_h(v,d)       iff constructor history h assigns fragment d to Value row v
Ref_h(v,o,w)     iff Own_h(v,d), o is a resolved Name in d, and row(o)=w
v ->_h w         iff some actual Ref_h(v,o,w) exists
```

All `Own` and `Ref` witnesses come from one construction history and one
correlated source scope/use. Simultaneously present owners may contribute
multiple outgoing references to a row. Mutually exclusive Call alternatives
must remain correlated; their edges are not unioned into one graph. A Value
row with no source-owned reference is an isolated vertex unless a later
source-value constructor or a justified extrusion transport gives it refs.

Keep these distinct:

| Relation | Meaning | Does not create a Value-reference edge |
|---|---|---|
| `v ->_h w` | Name reference in `v`'s owned static source-value description | Type port, scope containment, provider possibility |
| `a <: b` | Simple-sub constraint | Its direction or successful propagation |
| `Stored(v, side, t)` | Physical lower/upper bound incidence | The choice of lower versus upper lane |
| `Parent(c,p,pol,k)` | Actual extrusion event and retained parent | Parent metadata alone |
| `Provider(v)` | Actual semantic value/provider in a Call witness | The provider's runtime heap edges |

Structural type terms may carry paths used to transport a typed Name target,
but traversing a type constructor never creates a Value edge. Effect rows are
separate and are not vertices of this Value graph.

## 3. Source constructor laws

Every constructor allocates/retains its type rows and Value ownership
separately. The reference clauses are:

| Constructor | Owned Value description and edges |
|---|---|
| Value/formal introduction | Introduces one source-owned Value site and its native owner row. A formal is a binding target; it has no outgoing edge merely because it has a type port. |
| `Name(o,b)` | The Name value row owns `Ref(o,b)`. Its target is the actual row for the resolved binder `b`, not a spelling match or the occurrence's type endpoint unless the constructor proves they coincide. |
| Literal | Owns a literal description with no outgoing Value references. |
| `Lambda(x,body)` | Owns its code/body fragment, excluding nested declaration initializers. Every resolved Name in that fragment contributes an edge to its resolved binding row, including formal Names. Formal/domain type ports alone contribute none. |
| `Apply(f,a)` | **User-selected 2026-10-12:** the result row owns the static Apply source fragment and its resolved Names in the callee/argument fragments, before and after Call dispatch. For `konst 1`, this gives `r → konst` even when the returned provider is literal `0`. These source-reference edges do not claim that the runtime result object points to the callee or argument. The actual output provider and result tuple remain in complete Call for typing/effect meaning; they do not replace the static fragment. |
| Record/projection/group/block | A constructor owns its actual value fragment and the Name occurrences in that fragment. Group forwards the child owner description. A block owns its final expression; each initializer has its own owner. Structural subexpressions and declaration containment do not themselves add edges. |
| Recursive binding | The original recursive binder row is the Name target throughout its initializer. A recursive Name contributes a self-edge; mutually recursive resolved names contribute their actual cross-edges. No polymorphic recursion or local mutual group is added. |

Examples:

```text
id x = x       : id's Lambda value has id -> x
konst x = 0    : konst's Lambda value has no edge to x
f x = g; g y = f : f -> g and g -> f
invoke f = f 1 : the static value fragment refers to f; the Apply type result
                 does not acquire a runtime-provider edge merely from dispatch
```

The first two differ even though their Function type ports include the formal
`x` in both cases. This is the required discriminator between actual source
references and formal type structure. The mutual-recursion edges are the
source-value example already accepted by the user. These are source
construction laws; native row correspondence is still a separate proof.

## 4. Simple-sub constraints do not mutate reference ownership

The ordinary two-Value-port Simple-sub state is:

```text
Type ::= a | Primitive | Record(label:Type,...) | Function(Type,Type)
Store = (level, lower bounds, upper bounds, pending comparisons, comparison cache)
```

For a comparison, the solver installs a level-safe bound and activates every
opposite bound as in the original algorithm. Function arguments reverse
comparison polarity and results preserve it. These transitions add/remove
typing obligations but do not create, reverse, or delete `Ref_h` witnesses.
`Value` ownership and references are construction facts; constraints are type
facts. An unresolved row may carry pending source-reference incidences before
any concrete provider or type solution exists.

For Yulang, the native Function type is `Function(V-, E-, E+, V+)`. The two
Value ports can be different polar views of one source Value variable after
extrusion. The two Effect ports retain their full separate hygiene/interface
data and do not become Value edges. The extra Function ports do not alter the
source reference clauses above.

## 5. Extrusion and reference transport

An extrusion event `k` creates a fresh typed copy `c` from actual parent `p`
at target level `ell`, with polarity-specific key `(p, polarity, ell)` and the
selected ordinary directed constraint/bound copying. It also records
`Parent(c,p,polarity,k)`. The copy's owned Value description is the parent's
source description transported through the **actual typed paths visited in
that event**; it is not inferred from the newly stored comparison or parent
record.

Represent each reference occurrence with its original source identity,
binder/scope, native target, and typed route `path(o)`. Let `pol_k(path(o))` be
the composed polarity on the actual Value-port route. The event-local map
`M_k` is the exact map used by extrusion on that route. Define:

```text
target_k(o) = M_k(row(o), pol_k(path(o)), ell)  if that route was visited
target_k(o) = row(o)                            only under a proved shared-frame law
Ref_k(c,o,target_k(o))
```

If one source occurrence is represented at both positive and negative paths,
retain both path incidences and apply each event-local map; do not collapse
them into one polarity-free target. Function contravariance determines the
composed type-path polarity, but it does not reverse the Value-reference edge.
References may cross levels and extrusion-family branches when the actual
constructor/transport produces those endpoints.

Fresh use is distinct from extrusion. One use allocates one shared map for all
generic rows in that complete source graph; equal rows inside that use remain
equal, different uses receive independent generic rows, and nongeneric anchors
remain shared. The same source-reference occurrences are transported through
that use map. Initializer effects are not rerun. Repeated recursive Name uses
retain the original monomorphic binder row until an approved generalization
boundary.

## 6. Intrusion and required proof

For each finite successful construction history `h`, compute SCCs on the
actual Value rows using only `->_h`. For each actual retained `Parent(c,p,...)`,
if `c != p` and `c` and `p` are mutually reachable, merge their type-variable
identities in solving and later uses, and transport every typing and source
reference obligation. SCC membership is only the guard; it is not the proof
that equality is sound.

The proof must establish, for the original supported source scope and jointly
shared observations, that each qualifying extrusion pair admits a witness
preserving the same source typing, complete Function/Call interface, effect
hygiene, future uses, and required principal scheme after equality. Multiple
merges must preserve one joint witness, and later constraints/generalization
must retain the equality. If this fails, present the first source-qualified
counterexample; do not weaken the selected equality rule.

## 7. Status and implementation handoff

This draft uses source-owned static references as a candidate model, not as a
settled native definition. The `odd`/`even` example establishes that lexical
levels cannot rule out a Value-reference SCC: the source references cross
levels in both directions. It does **not** determine what content an Apply
result row owns. Complete Call determines and types an actual result when one
is produced, but that fact alone does not define a static row-content law for
an unresolved callee. This draft does not prove the new native algorithm or
establish that the existing candidate implements it.

The smallest open construction law is the joint source-to-row and row-to-path
map for every Value constructor, especially `Name` resolution through Lambda,
recursive roots, `Apply` output rows, polar extrusion, and fresh use. Existing
source HIR records retain useful binders/occurrences, but the bounded audits do
not establish that all reference occurrences map to the particular Value row
whose value owns them, or that the extrusion consumer sees exactly this graph.
The corresponding equality-preservation theorem is also OPEN.

The Apply result-row ownership equation is selected and recorded, but no SCC
scanner may be implemented from this proposal yet. First prove and independently
review the remaining constructor-to-row mapping, reference transport through
extrusion and fresh use, and equality preservation for an actually qualifying
parent/copy pair. These proof obligations cannot be closed by this proposal
alone. Then construct the smallest standalone reference transition system
directly from the approved rules, rather than repairing the current candidate
by assumption. Complete Call, contextual effects, full soundness/principality,
normal inference progress, and F5 replacement remain OPEN.
