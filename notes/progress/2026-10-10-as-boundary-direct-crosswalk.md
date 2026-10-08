# Expression annotation boundary to Direct: owner crosswalk

Date: 2026-10-10
Status: non-authoritative bounded crosswalk; compiler-referee and spec-auditor
reviews closed; one minor HIR owner-locator correction delta-verified
Baseline: `8f7f28d88` on `research/simple-sub-intrusion`
Scope: approved expression `as Type` boundary, selected native Direct checker
operands, and current parser/HIR/solver path
Production implementation, semantic change, gate promotion, and F5 cutover:
none

## Result

The approved expression `as Type` boundary supplies an authentic source
checking occurrence `q`. This corrects the broader wording in the preceding
[caller/resource-schedule cut](2026-10-10-native-caller-resource-schedule-cut.md):
the published unannotated `id` plus monomorphic Alias example does not itself
contain `q`, but the separately approved `as Type` form does.

The occurrence alone does not satisfy the selected Direct checker input. The
remaining gap is the source annotation owner's production of the exact current
endpoint/root, completed target/root, original scope correspondence and
realization evidence. The target syntax is a source contract, not automatically
the native public-root record. An executed cast/adapter at the annotation is
also not a proof-only Direct inclusion.

## Authority and owner mapping

The approved `source-annotation-boundaries/q1/d1` selects expression
annotations as included boundaries. At each such boundary, check the current
endpoint directly against the annotation target; on success export the target
endpoint plus local realization evidence, preserving earlier boundary
evidence. It rejects implicit intermediate concrete adaptations without a
source boundary. Its receipt records that the approved handoff has not yet
been applied to a durable authority record; it does not authorize compiler
implementation.

The selected Source Generalize notation `view(h,q,V)` is a source
checking/annotation occurrence, and Direct consumes submitted ordinary roots
and proof evidence. The current crosswalk is:

| Field | Selected owner/meaning | Existing representation and gap |
|---|---|---|
| `q` | The actual expression `as Type` annotation boundary | Parser emits `TypeAnnotationTail`; association retains its source node. Shadow inventory assigns an artifact-branded `AnnotationId` and CST position, but labels correspondence `PendingTypedPortAndProfile`. |
| Current endpoint | The endpoint delivered by the annotated expression, including a prior boundary's exported target | No production annotation elaborator emits the endpoint or ties it to an ordinary PE public root. The ordinary associated tree is later rejected by current simple-chain lowering. |
| Annotation target | The written source contract at `as` | The parsed Type is syntax only. Source written types, inferred public schemes and internal evidence-rich views are explicitly distinct. No current typed target/public-root record is emitted. |
| Original scope | The source handle's description instance, annotation scope, typed paths and shared evidence | Structural occurrence identity is retained only by shadow HIR; no completed typed scope/profile/correspondence is supplied. A view does not freshen a new description tuple. |
| Realization evidence | Prior boundary evidence plus this boundary's local proof or source-authorized realization | No production annotation evidence owner was found in the inspected route. A selected concrete cast/adapter remains an executed realization at the source boundary, not a Direct proof node. |
| Enclosing endpoint | The annotation target and accumulated realization evidence after success | Current production lowering has no annotation variant in `ResolvedExpr`; it publishes `UnsupportedExpression` before solver constraints. |
| Direct operands | Exact ordinary public roots `u,V`, complete typed records, and a finite proof for `Direct(u,V)` | Neither `AnnotationId` nor parsed Type nor a failed `ResolvedExpr` supplies these operands. A genuine producer and identity-preserving bridge remain required. |

The selected Direct direction is therefore usable only for an annotation case
whose authentic realization is a proof-only inclusion with matching ordinary
roots and scopes. If the source annotation resolves by executing an adapter,
the annotation semantics still apply, but that route is not represented by
Direct's inclusion proof.

## Concrete current-code path

The parser recognizes contextual `as` and constructs `TypeAnnotationTail` with
the full Type expression (`crates/yu-syntax/src/expression/operator_chain.rs`
and `crates/yu-syntax/src/expression/tails/type_annotation.rs`). Association
places the annotated expression first and preserves the annotation tail as an
outer structural node (`ChainParser::expression`'s `TypeAnnotationTail`
branch and `ChainParser::structural_continuation` in
`crates/yu-hir/src/lib.rs`).

This is not semantic HIR. `lower_simple_chain` in
`crates/yu-hir/src/module.rs` accepts only a childless integer/name leaf;
an annotation has children and takes the `UnsupportedExpression` route. The
ordinary `ResolvedExpr` enum has no annotation/check variant, so solver
collection receives an error instead of the inner endpoint, target or
evidence. The separate shadow inventory retains a source-position
`AnnotationId`, not a typed port, annotation permission, endpoint or target
root. No test, build or runtime probe was run.

## Smallest next evidence

Trace one actual `as Type` occurrence whose operand already has an authentic
native ordinary public root. Require its owning annotation elaborator to
produce and relate:

1. the exact annotation occurrence `q` and current handle/root `u`;
2. the completed target contract and exact public-root record `V` at its
   original scope;
3. the proof-only inclusion or, separately, the executed-conversion owner;
4. the complete prior-plus-local evidence and the exported target endpoint.

For a proof-only case, verify the supplied Direct certificate remains bound
to those exact roots and scope. For an executed conversion, retain its source
constructor and resulting handle without manufacturing a Direct proof. Do not
substitute the annotation's written syntax for `V`, use a pre-annotation
synthesis root after target export, or equate parser/shadow IDs with semantic
evidence.

The exact typed producer's API and placement remain unresolved. If no current
source case has an authentic public root before `as`, identify the earlier
root/publication owner first; do not infer one from F5 rows or select an
internal synthetic check. Existing Hreg no-repeat and pending literal/Result
ownership boundaries remain untouched.

## Review and verification

This is a bounded owner crosswalk, not a new source rule, proof, or compiler
design approval. A compiler referee reviewed root, conversion and evidence
ownership; a spec auditor checked the approved annotation/Direct boundary.
The compiler referee's one minor HIR owner-locator finding was corrected and
delta-verified. No actionable findings remain. A future implementation gate
still requires its own reviewed durable authority and approval.

Primary inspection covered the applicable approved annotation and Direct
answers/receipts, source-annotation and concrete-compatibility decisions, SRC
§3.4, PE §6.1, the core checking fragment, parser/association, `ResolvedExpr`,
simple-chain lowering, and shadow annotation positions. No pending question
bundle was read or used. No tests, builds, benchmarks, or executable probes
were run. Git status/diff and dependency-hash reads were used for repository
state verification; no Git mutation was performed for this artifact.
