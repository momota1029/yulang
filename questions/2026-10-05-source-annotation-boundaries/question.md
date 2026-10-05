# Source annotation boundaries in the inference replacement

Question ID: `source-annotation-boundaries`
Question revision: `q1`
Predecessor/history: none; follows the approved non-composition rule for successful concrete checks and the current source-coverage audit
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): `a38e79e6157f641674103073ce1527831d3480eb` (current source-coverage audit); `80b5749f0` (concrete transitivity obstruction); governing concrete-compatibility design unchanged through current HEAD
Task/thread locator: unavailable; the active objective is to complete Yulang inference theory and replace the inference implementation
Governing source/section: `notes/design/2026-10-03-concrete-compatibility-boundary.md` §1; `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` §§1–4; `notes/design/2026-09-09-successor-expression-structural-tails-draft.md` sections “as Type” and “Type exit and continuation”; `notes/design/2026-10-02-typed-computation-core-elaboration.md` §6

## Requested scoped decision

Define which annotation forms belong to the inference replacement's source-typing envelope, and whether a successful annotation check changes the endpoint exported to the enclosing expression. Also decide whether concrete checks may occur successively without a corresponding source boundary.

This decision concerns source typing/elaboration and evidence flow. It does not change the one-query endpoint-dependent solver, grant transitivity to successful concrete comparisons, or authorize implementation by itself.

## Background and confirmed facts

- The approved concrete-compatibility boundary allows transitivity on variable edges but does not allow composing successful concrete comparisons to establish another concrete inequality. Local adapters/casts are resolution evidence for an individual comparison.
- A current proof obstruction shows why an unrestricted preorder assumption cannot stand for the concrete solver: `A={foo?:string} <: B={} <: C={foo?:int}` succeeds link by link while `A <: C` fails. The Name source rule that exports only its original anchor cannot reconstruct the two comparisons from a target of `C`.
- The current parser admits expression syntax `x as Int` and HIR associates an annotation boundary, but semantic lowering rejects it as `UnsupportedExpression` before constraint generation. `ResolvedExpr` and `yu-core` currently contain no annotation/cast realization.
- The `x as int as str` parser witness is one annotation whose target is a type expression with applications; it does not establish two semantic conversions.
- Existing binding-annotation fixtures establish current behavior only. They do not authorize a permanent exclusion from the replacement.
- No inspected Authoritative source decides expression annotation semantics, the complete replacement envelope, or arbitrary implicit successive concrete adaptations. The candidate pure source-adequacy rules assume a preorder and are not authority for this gap.

## Options and consequences

### 1. Explicit checking boundaries export their targets

Name the annotation forms included in the replacement (for example, binding annotations, parameter annotations, and expression `as Type`). At each included boundary, check the current expression endpoint directly against that annotation target. On success, the boundary exports the target endpoint together with its local realization evidence to the enclosing expression. Nested or repeated checks remain separate source-boundary derivations; the solver does not compose their concrete successes into a new comparison. No intermediate concrete adaptation occurs without a source boundary.

Consequence: the replacement must retain the endpoint and evidence at each authorized boundary. A later check consumes the endpoint exported by the prior boundary and records its own evidence; it cannot erase the earlier realization. This enables a source-adequacy proof only for the named boundary forms.

### 2. Explicit annotations validate without replacing the expression endpoint

Name the annotation forms included. Each included form checks the original expression endpoint against its annotation target, but the enclosing expression keeps the original endpoint. Intermediate concrete checks remain unavailable unless a separate source construct defines them.

Consequence: annotations do not create successive adapted endpoints. The replacement must prove that this validation-only behavior matches the selected source contract for every included form.

### 3. Initially exclude expression `as Type` from the replacement envelope

Include only explicitly named non-expression annotation boundaries, with their endpoint behavior stated under option 1 or 2. Preserve current rejection of expression `as Type` as the initial replacement boundary, without treating that restriction as permanent language authority. Concrete checks without source boundaries remain unavailable.

Consequence: adequacy is explicitly scoped and cannot be reported as complete for all parsed source forms; a later gate must decide whether expression annotations enter the envelope.

### 4. Permit intermediate concrete adaptations without a source boundary

Specify the exact adaptation-search rule, how intermediate endpoints and evidence are elaborated, how ambiguity/coherence/principality are handled, and how resource bounds are enforced.

Consequence: this is a broader semantic decision requiring new proof obligations. It cannot identify all concrete successes with a transitive preorder or silently reuse the rejected direct-composition rule.

## Required answer

Choose one option or give an exact alternative. For every included annotation form, state whether success exports the target endpoint or retains the original endpoint, and what realization evidence survives. State whether an ordinary expression can undergo an intermediate concrete check without a corresponding source boundary.

## Affected and independent work

Blocked scope: complete source adequacy for annotation-bearing expressions, the recursive-group adequacy step when it relies on unrestricted `Sub` transitivity, and production source elaboration for those boundaries.

Independent work continues: conditional structural/residual projection proofs, mixed effect-descriptor work, source-generated callback results, and any inference-cutover inventory that does not assume annotation semantics.

This question selects no compiler implementation, solver carrier, expected-output change, or permanent unsupported-source policy. Keep this question directory unstaged and uncommitted until a complete approved handoff is validated by the questioning primary.
