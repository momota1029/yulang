# Ordinary HIR admission for structurally associated applications

Status: Draft revision 2 after spec review; not adopted and grants no implementation authority.
Scope: a proposed next HIR design gate for recovery-free unary application
expressions in ordinary binding bodies. It does not define semantic Call typing,
constraint generation, effects, solver acceptance, or the original Call theorem.

Drafted by: Luna primary, session `current-session`.
Independent source/projection input:
`notes/theory/2026-10-17-accepted-call-hir-projection.md`,
SHA-256 `0c1a29f3d590f68064e980459a4373400702034a2366591dae32fe7b1572e25f`.
Compiler review: CLEAN within that frozen conditional analysis; reviewer
`/root/accepted_call_hir_projection_compiler_review`, requested
gpt-6.1-sol/medium, observed UNKNOWN; 100 seconds charged.
Original inference parent: unchanged; no theorem premise discharged.

## 1. Problem and current contract boundary

The authoritative association contract fixes structural postfix and left-to-
right ML application. For the exact previously attempted source, under the
artifact's explicit CST-shape premise, the body associations are:

```text
id:     V(x)
apply:  M(V(f), V(1))
answer: M(V(apply), V(id))
```

The prior one-shot test had no structural recovery but failed the required
zero-HIR-error assertion before `CandidateInference::solve`. The independent
source projection account locates the cause in each current HIR owner:
`SimpleBodyProjection::Unsupported` makes both application bodies emit
`UnsupportedExpression`; ordinary `lower_simple_chain` independently rejects
both. The opt-in shadow `ResolvedExpr::Apply` path also attaches
`UnsupportedExpression`, and its inventory expects nonempty error IDs. Thus
neither removing an assertion nor enabling the shadow switch is a mechanical
repair.

Current approved HIR scope excludes application syntax in the simple-module
slice and preserves its unsupported-expression diagnostics. The ordinary source
carrier decision explicitly leaves existing HIR admission, errors, diagnostics,
and occurrence identities unchanged. Association and retained source structure
do not supersede either rule. The current error-free test gate can change only
under an approved HIR admission decision; this draft does not change it.

## 2. Non-negotiable properties for any future choice

Any selected route must preserve the original supported ordinary source
behavior and keep source structure separate from semantic Call judgment. It
must not infer callable role, argument type, result/effect, source T, or solver
success merely because an `Apply` node exists.

A structural application representation must retain the exact associated
callee/argument order and distinct source occurrences. Every node must be tied
to the owning artifact and source key; text equality or token range equality is
not identity. Existing module `DefId`s, parameter identity, root ordering,
recovery attachment, and ordinary occurrence allocations remain stable. If
post-ordinary structural occurrences are needed, allocate them after ordinary
lowering and from the same artifact, without changing previously observable
ordinary IDs or publishing a partial tree.

Recovery-bearing and unsupported forms retain their existing causes and do not
resolve hidden operands. A bounded source projection must reject atomically on
its actual dimension and must not inherit a shadow-only limit as a global HIR
promise. A parser/source-owner audit must establish the exact CST forms and
trivia-bearing ranges before the concrete fixture is promoted as source-to-HIR
correspondence (TODO HIR-APP-CST-1).

Any representation change must audit all `ResolvedExpr::Apply` producers and
consumers, especially the shadow resolved-call inventory's current requirement
for authentic unsupported error IDs. It must specify operand-error ownership
without duplicating, dropping, or silently clearing errors.

## 3. Unselected choices

| Choice | HIR behavior | Compatibility and consequence |
|---|---|---|
| **A. Admit recovery-free associated applications in ordinary HIR** | For an explicitly bounded structural grammar, ordinary lowering returns an `Apply`-shaped expression with exact callee, argument, source form, ranges and identities. Structural support itself emits no `UnsupportedExpression`; malformed, unresolved, ambiguous, resource-refused, and unsupported children keep their owning errors. | This changes the September 19 unsupported-application admission rule and the October 10 unchanged-admission boundary within an explicit successor scope. It can satisfy the present zero-HIR gate for the fixed source if the exact shapes are verified. It still does not establish that `CandidateInference` types, propagates or consumes Call correctly; later gates may fail. Requires audit and revision of the shadow Apply error invariant, source-ID allocation, recovery and diagnostics. |
| **B. Keep ordinary HIR's current refusal and continue only through a separate experimental source carrier** | Ordinary HIR continues to report `UnsupportedExpression`; an independently specified consumer may inspect a source-backed carrier under its own provisional boundary. | Preserves current HIR diagnostics and avoids immediate ordinary API change, but it does not meet the current zero-HIR-error vertical gate. It cannot be presented as that source being accepted by ordinary HIR or as successful solver inference. It needs a separate solver/source-carrier contract and may not bypass original Call proof obligations. |

No third option is “ignore `HirModule::errors()`” or “remove the assertion.” Either would erase the failed gate without specifying an admission rule. Choice A is the shortest route to the existing test's stated HIR condition; it is not selected here. Choice B preserves current error behavior but leaves that condition unmet. The user must decide whether to supersede the current HIR admission boundary before implementation.

## 4. Proposed next contract if Choice A is selected

A narrow successor contract would add structural admission for the already
associated unary ML/Call forms, recursively preserving the authoritative
left-associated tree. It would state:

- admitted source grammar and the exact supported nested/group forms;
- behavior for every existing parser recovery class, unsupported operand,
  unresolved/ambiguous name, annotation, and depth/size boundary;
- `ResolvedExpr` representation and whether the outer Apply reuses the existing
  root occurrence ID; allocation of child occurrences and exact source-key
  mapping; stable `DefId`/parameter/root ordering;
- ownership and order of diagnostics and causal error IDs, including the
  transition from “unsupported application” to structurally admitted while
  leaving semantic Call errors to their actual later owner;
- all Apply producers and consumers, including the shadow inventory;
- atomic rejection and measured work/space bounds;
- focused future HIR regressions for left association, callee/argument identity,
  module/formal resolution, nested calls, recovery, malformed groups, and
  resource boundaries.

The exact fixed literal is a minimum regression, not a new source-language
support limit. The contract must explain general supported application forms
without restricting ordinary inference to this specimen. A separate later
source-to-solver gate must prove that the source constructor emits the Call
constraints and that propagation reaches the actual consumer; a HIR node alone
cannot close those obligations.

## 5. Open premises and approval

- `HIR-APP-ADMISSION-1`: choose and specify ordinary admission/diagnostic and
  representation behavior; owner: user for the superseding decision, then
  Luna/HIR design and implementation owners for its bounded contract.
- `HIR-APP-CST-1`: exact parser/CST/source-key constructor audit for the fixed
  literal and trivia-bearing ranges; owner: parser/HIR source owners. The
  existing proof artifact expressly keeps this conditional.
- Source `Apply` to generated constraints, accumulated constraints,
  propagation/transport and solver consumer: OPEN; owner: original Call source
  and solver gates. No source T or Call theorem follows from either HIR choice.
- Original A/B, F1/FK1, N-Transport, OPRESP, soundness, principality and
  termination: OPEN and unchanged.

Required sequence before any Choice A implementation: first, the user may select
the direction A (ordinary structural admission) as a design target. That
directional selection does **not** approve unspecified details. Luna must then
write the complete successor contract covering exact supported grammar, recovery
and unsupported behavior, representation, diagnostic ownership, identity and
allocation, consumer audit, and measured resource limits. Audit the exact parser
and source-key constructors. Fresh independent compiler and spec review (plus
architect review for the HIR boundary) must review that concrete contract; repair
all blocking/major findings. Only then obtain and record the user's explicit
approval of that reviewed contract and its exact supersession of prior HIR
admission clauses. Code and tests may start only after that final approval and
an exact implementation lease. Earlier user approval suffices only where its
recorded scope already decides those exact details.

If the user selects B, Luna must similarly define and independently review the
separate provisional source-carrier and solver boundary before any implementation;
that choice does not make the ordinary HIR gate pass. This Draft remains a
proposal for selecting a direction, not the final superseding contract.
