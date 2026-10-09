# Source-owned annotation to ordinary Any root — one-case design

Date: 2026-10-10
Status: Draft; reviewed-design target only; no implementation authority
Scope: source expression `my widened = 0 as Any`
Claim class: bounded owner/interface design; source acceptance unverified
Authority: approved `source-annotation-typed-root-bridge/q1/d1`

## 1. Objective and selected boundary

Design one proof-only expression annotation case. It should retain the value
and provider supplied by the operand, check the current typed endpoint against
the written target at the exact annotation boundary, and make the target the
completed expression root. The candidate source is:

```yulang
my widened = 0 as Any
```

The syntax reader shows integer atoms, contextual `as` with one full
`TypeExpression`, and identifier type primaries. HIR association applies the
annotation tail to the completed operand and preserves the annotation node.
This exact program has not been parsed or compiled; acceptance is therefore an
unverified source-reading inference. Current ordinary semantic lowering has no
annotation form and `lower_simple_chain` accepts only a childless value.

The approved q1/d1 selects **source-owned formation** with conditional Direct
consumption. The source annotation owner elaborates the written type and owns
the boundary result. Direct consumes already supplied roots and a finite proof;
it neither resolves type syntax nor creates a target root. This file proposes
one owner interface only. It does not authorize implementation, production
routing, a public API, failure/resource policy, or F5 cutover.

## 2. Actual target and proof-only interpretation

For this case the written type should resolve to the completed ordinary Value
descriptor `Any` at the annotation's original lexical scope. The semantic
boundary is:

```text
operand endpoint/root: u_Int : ordinary Value(Int)
written target:        v_Any : ordinary Value(Any)
local proof:           p_top : V(Int, v, p, e, xi) -> V(Any, v, p, e, xi)
boundary certificate:  Direct(u_Int, v_Any; Value(p_top))
```

The existing hereditary Top case is the local law for `p_top`: it carries the
same value/provider and the complete ordinary membership evidence, guards and
scope tuple from Int to Any. It is proof-only. It does not execute conversion
code, allocate a new runtime value, or assert anything about Function
admission. Ordinary Any is a Value target, so it has no Function inlet,
receiver, or invocation equations.

The conditional premise is important: the reviewed native projection proof
uses the actual ordinary Any root at `q` as a supplied premise and derives the
Value/Top proof conditionally in its selected `id` export scope. It does not
produce that root or a written-Type elaborator. The hereditary proof is
evidence for the local Top law, while the root-production interface remains
open here. A source-owned producer must bind the actual written `Any`
occurrence to a complete scoped target-root record.

## 3. Owner dataflow

Use these owner records conceptually; this document does not prescribe Rust
types, IDs, allocation or caching.

| Owner | Required output | Invariant |
|---|---|---|
| Source association | annotation occurrence `q_as`, complete operand subtree and complete written Type subtree `q_type`; exact range and lexical scope `sigma_q` | The tail belongs to the completed literal operand, not an interior or recovery node. |
| Operand formation | ordinary root `u_Int`, same value/provider origin, prior evidence `E_in`, and its exact source incidence | Literal formation supplies the endpoint; annotation does not replace or re-evaluate it. |
| Written-Type formation | resolved semantic target `Any` tied to `q_type` in `sigma_q`, plus a completed Value-typed contract | No unresolved name, fresh inference variable, or endpoint-derived target is accepted as the written type. |
| Ordinary-root formation | complete root `v_Any` with actual `Any` interpretation, typed operands, original scope map, guards, evidence telescope and a source link to `q_type` | Direct receives a real ordinary root, not F5 negative `Top`, an endpoint, or a scalar type tag. |
| Boundary proof formation | finite hereditary `p_top` at the exact `(u_Int,v_Any)` roots and original tuple | The proof preserves same value/provider and all original complete membership fields. |
| Direct consumption | `Direct(u_Int,v_Any;Value(p_top))` bound to those exact roots | A mismatched root, scope, source occurrence or law fails validation. Direct does no elaboration. |
| Annotation completion/publication | selected target endpoint `Any` and accumulated evidence `E_out = E_in + E_top`, attached to the original annotated source result | The final definition root follows the annotation target; it does not publish interior `Int`. |

The source owner produces the type/root packages before asking Direct to consume
the proof. The dependency is one-way:

```text
source TypeExpression + scope -> typed Any contract -> ordinary v_Any root
literal operand             -> ordinary u_Int root + E_in
u_Int, v_Any, E_in, Top law -> finite p_top -> Direct -> E_out / Any result
```

No output is inferred by success of Direct. In particular, an opaque
`"Any-checks"` boolean is not a supplier for either root or the proof.

## 4. Root and law completion boundary

The smallest unresolved design obligation is the producer for `v_Any`. Its
signature must connect the actual written type occurrence to a completed
ordinary root and provide the interpretation of that same root as `V(Any)` at
the source scope. The root schema must expose every operand the Top eliminator
uses, including original guards, hereditary evidence binders and scope maps.
It must not borrow the PE `id` root under a different source identity or erase
the written annotation provenance.

The Top law must be an independently registered ordinary Value law whose
signature is checked at those exact roots and tuple. The proof transforms the
complete `V(Int)` membership evidence into complete `V(Any)` membership for
the same value/provider. If this target-root producer or its lawful Top
interpretation requires a genuinely new semantic clause, stop for a separate
narrow decision before adoption. The current design does not claim that the
existing F5 positive scheme or negative-bound constructors provide it: the
positive `ClosedValueScheme` grammar has no standalone Top case, and a
negative algebraic Top is not an ordinary public target root.

## 5. Failure and preservation

Do not expose `v_Any`, the boundary certificate, or the annotated final root
until type resolution, ordinary-root formation and exact Direct checking all
succeed. On failure, `E_in` remains evidence about the operand only; it cannot
certify the Any target. Keep failure classification, diagnostics, retry,
resource limits and retention policy open for their own implementation gate.

Preserve the actual literal value and provider. If the chosen source boundary
later denotes an executed conversion, that needs a separately selected source
constructor with its own execution effects/result handle; it cannot be encoded
as this Direct proof. The current selected proof-only case performs no such
conversion.

## 6. Review request and non-claims

Review with M2 `compiler_referee` for root/proof ownership, same-value
preservation and evidence completeness, and `spec_auditor` for q1/d1 scope,
ordinary Any/Top conformance and exact conditional limits. Convergence requires
no blocking/major findings and an identified producer or explicit open input
for every root, law and evidence field. A semantic clause not supplied by the
existing selected law is a design stop, not something to hide in an
implementation API.

This candidate does not establish exact source parse acceptance, semantic
`Any` name resolution, an ordinary Any source-root constructor, compilation,
diagnostic behavior, arbitrary annotations, inference principality, executed
conversions, production Direct wiring, F5 replacement or cutover. No tests,
builds or measurements were run for this research design.
