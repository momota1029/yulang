# Intrusion qualification through value-to-type association

Status: Authoritative clarification of the user's selected operation
Scope: the graph domain and the connection from Value SCCs to type intrusion
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

The association must come from the actual source/type construction and be
preserved through its operations. No one-to-one association, assignment for
every Function port, or transport rule for polarity-specific copies is inferred
solely from this clarification. These are the next concrete construction
obligations; they must not be replaced by requiring an incoming reference edge
into a freshly allocated type row.

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

The next owning work is to construct and retain value identities, their
reference graph, and the association of actual type occurrences with those
values, including recursive sharing, polar extrusion and fresh use. From that
construction, prove parent-qualified equality preservation and derive the
smallest faithful implementation. Do not modify the frozen candidate merely
by reversing bound edges or adding type-copy vertices.

Soundness, required principality, normal progress, termination of the combined
algorithm, complete Call, effect hygiene and F5 replacement remain OPEN. This
clarification records the graph domain and activation criterion; it supplies
no proof of equality preservation and approves no new transport convention.
