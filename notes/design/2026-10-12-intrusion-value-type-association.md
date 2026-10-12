# Intrusion qualification through value-to-type association

Status: Authoritative clarification of the user's selected operation and
extrusion-event qualification
Scope: the graph domain, extrusion occurrence identity, and the connection
from Value SCCs to type intrusion
Approved-by: user, direct clarification in the working conversation
Approved-at: 2026-10-12; exact message timestamp unavailable
Reviewed-by: independent compiler_referee, no findings, 2026-10-12;
transcription and applicability withdrawal only, not equality-preservation proof
Supersedes: interpretations that require an extrusion type copy itself to be a
Value-reference graph vertex or to have incoming Value-reference edges

## Direct clarification

> 型変数は値変数に結びついていて，値変数のSCCが等しくなった場合，対応する型変数がintrusionされる

This clarifies the [selected parent/copy operation](2026-10-10-parent-copy-scc-intrusion.md).
The values whose references define SCCs and the type variables changed by
intrusion are distinct mathematical objects. A solver row of kind Value is a
type coordinate; its name does not establish that it is a semantic value
variable.

## Approved extrusion-event qualification

The user selected qualification by the actual extrusion occurrence:

1. Give each extrusion occurrence an identity and retain with it the source
   Value at the extrusion origin, the receiving Value, and the actual retained
   type-variable parent/copy pairs produced by that occurrence.
2. If the origin and receiving Values belong to the same component of the
   approved Value-reference graph, intrude that occurrence's retained
   parent/copy pairs.
3. Do not infer a permanent single Value owner from a type-variable ID, assign
   every suboccurrence of a function description to its enclosing function, or
   copy/retarget Value-reference incidences. Freshening alone is not an
   extrusion occurrence.

For the recorded nested `f/g` discriminator, the source is `G` and the
receiver is `F`. The actual pairs `(C,B,+,1)` and `(D,R,-,1)` belong to that
extrusion occurrence. Since `F` and `G` share a Value-reference SCC, its
qualified operation adds `C=B` and `D=R`.

This selects the occurrence identity and its two Value endpoints; it does not
choose an encoding, caching policy, SCC scheduling point, or transport scheme
for every compiler path. Those must faithfully retain the actual occurrence
and its produced pairs through sharing, memoization, polarity-specific copies,
scope and generalization. It also does not prove that adding the qualified
equalities preserves soundness, required principality, normal progress or
termination. Those proof gates remain open, and no implementation or F5
cutover is approved by this decision.

## Qualification

Let `G = (V, Ref)` be the approved graph of value variables and actual references
in their values. Let `T` be the type-variable domain. Source construction must
retain the association between these domains. For an actual retained extrusion
pair `(alpha_copy, alpha_parent)`, use the value variables associated with that
pair's type occurrences, `v_copy` and `v_parent`. The qualifying comparison is

```text
SCC_G(v_copy) = SCC_G(v_parent).
```

The selected operation then equates the corresponding extrusion-related type
variables. It does not compute SCC membership of `alpha_copy` and
`alpha_parent` in a graph of type coordinates. It does not equate arbitrary
types merely because their associated values lie in one SCC.

The extrusion-event record must come from the actual source/type construction
and be preserved through its operations. No one-to-one association or
assignment of every Function port to one permanent Value owner is inferred.
Polarity-specific parent/copy pairs remain distinct members of their actual
extrusion occurrence; they must not be replaced by requiring an incoming
reference edge into a freshly allocated type row.

SCC equality does not require a nontrivial component. When actual associations
select the same value variable, that vertex belongs to the same component as
itself. Conversely, allocating a type copy does not by itself determine whether
the two type occurrences associate with the same or different values.

## Consequences for the current research

The nested `odd`/`even` example still gives value-root paths `O -> E` and
`E -> O` across lexical/inference levels. Applying intrusion additionally
requires the actual type-variable associations and retained extrusion pair.
It does **not** require those type-copy rows to become vertices of this SCC.

The finite graph calculation and codomain lemma in the
[copy-qualification note](../theory/2026-10-12-odd-even-copy-qualification-proof.md)
do not establish nonqualification of the corresponding type variables under
this rule. Their application treated type copies as graph vertices. The
[constructor/installer inventory](../progress/2026-10-12-value-edge-constructor-inventory.md)
does not repair that application: attaching a type coordinate to an existing
value requires neither installing it as a source binder nor giving the type
coordinate an incoming value edge. Retain their bounded source and abstract
graph facts as historical evidence, while withdrawing their applicability to
the original intrusion qualification gate.

The [copied-description decision](2026-10-12-value-reference-copied-row-ownership.md)
still states that copying a type description does not copy value incidences or
retarget resolved Names. This is compatible with associating the copied type
occurrence with a value in the existing graph. It does not supply the actual
association or prove that any pair qualifies.

## Implementation and proof boundary

At inspected baseline `a823deba1a0a6c944e4c67099cb6cd3c0f4fa728`,
`candidate_intrusion.rs::settle_candidate_intrusion` constructs a graph of
Value/Effect solver endpoints by walking bounds and Function ports, then checks
the component IDs of the type parent/copy endpoints directly. That consumer
does not implement the qualification above. Existing runtime regressions and
mechanism reviews do not establish this corrected source correspondence.

The next owning work is to construct and retain extrusion occurrence identity,
its actual origin/receiver Values and produced polar parent/copy pairs through
recursive sharing and generalization. Construct the approved Value-reference
graph independently, then prove that the occurrence-qualified equalities
preserve the original source typing conclusions and required principality. Do
not modify the frozen candidate merely by reversing bound edges or adding
type-copy vertices.

Soundness, required principality, normal progress, termination of the combined
algorithm, complete Call, effect hygiene and F5 replacement remain OPEN. This
clarification records the graph domain and activation criterion; it supplies
no proof of equality preservation and approves no new transport convention.

## Earlier source-construction discriminator

The following source characterization established the discriminator that led
to the approved occurrence rule. An independent `compiler_referee` audit
identified the missing constructor at App-demand generation and extrusion.

Use the minimal original-Simple-sub term

```text
let rec f = lambda x.
  let rec g = lambda y. f y
  in g x
in f
```

The original `Typer.scala` at `9bae772624c23b52a93c1b226157e16898b4d9db`
introduces outer recursive `o` at level 1, inner formal `B` and inner App
result `R` at level 2 (lines 48–72). Monomorphic lookup returns `o`; it does
not copy it. The demand `o <: Function(B,R)` invokes negative extrusion of
the high-level demand to level 1 (lines 115–156), creating actual polar pairs
`(C,B,+)` and `(D,R,-)` and storing `Function(C,D)` in `U(o)`.
These ordinary consequences reuse the existing
[nested-call derivation](../theory/2026-10-12-odd-even-copy-qualification-proof.md#3-native-construction-producing-the-exact-finite-pairs);
the withdrawn part of that note is its application of type-copy graph
nonreachability, not these original operations.

The approved source root references put `F` and `G` in one Value SCC. Formal
`Y` and inner result value `R_value` are different values. Two candidate
association conventions illustrate the decision that is still missing:

| Actual type pair | Immediate operand/result convention | Enclosing description-occurrence convention |
| --- | --- | --- |
| `(C,B)` | parent associates with `Y`, copy with `F` | parent occurrence associates with `G`, copy occurrence with `F` |
| `(D,R)` | parent associates with `R_value`, copy with `F` | parent occurrence associates with `G`, copy occurrence with `F` |

The second convention qualifies these pairs from the known `F/G` SCC. The
first does not follow from that SCC; in the graph generated by the shown
root/Apply incidence rules alone, `Y` and `R_value` are outside it. This is
a discriminator between the old conventions, not a nonqualification theorem
for the final algorithm. The approved occurrence rule selects the extrusion
source and receiver Values, rather than assigning each pair endpoint a
permanent owner by either convention.

Source Generalize's `Desc` introductions and `Build` preserve each original
declaration and scope; containment in a complete function description does
not establish an additional describing-value association. Nor does storage
of `Function(C,D)` on `o` establish the proposed copy-to-`F` association for
its suboccurrences. Both conventions require an explicit source/extrusion
occurrence construction, including its copied-port pairs. The approved answer
resolves this discriminator for the displayed extrusion; general source
construction and transport remain proof obligations.

The owning proof must establish original source soundness, required
principality and normal progress for the selected construction. Preservation
of every arbitrary pre-intrusion solver assignment/client fiber is not an
additional required theorem without an independently established source
contract. Independent fresh-use description frames remain distinct;
freshening itself creates no extrusion parent pair.
