# Callback expected-context delivery before literal-body elaboration

Status: Reviewed
Date: 2026-10-03
Scope: bounded source elaboration for one unannotated Function literal passed to a known Function-valued callback formal
Approved-by: none; user approval pending
Drafted-by: primary
Reviewed-by: architect, compiler_referee, and spec_auditor (2026-10-03); no unresolved findings
Supersedes: none

## 1. Purpose and authority boundary

The user has selected the source-level order

```text
function literal + expected context
  -> receiver role (pure / handler)
  -> Function interface elaboration
  -> effect-port interpretation
```

The role clauses are selected: an ordinary unannotated literal without a
handler-capable expected context is Pure; an explicitly Function-annotated
literal has a Handler boundary; and a literal in callback position receives
Handler from its expected callback context. Charter §21 independently selects
the parameter-entry role from parameter syntax. Neither role is recovered from
effect-port spelling.

This proposal makes one bounded step toward realizing that order: deliver an
already resolved and instantiated callback formal to its function literal
before generating the literal body's constraints. It does not decide the
Rust API, where declared interfaces are stored, how imports or members are
resolved, or how a complete role-indexed Function interface is formed. It has
no compiler implementation authority.

## 2. Bounded source judgment

Assume source application/literal structure and declaration resolution have
already supplied a known callback formal. Write `F_cb` for that formal's
already instantiated Function interface, `β` for its static callback-slot
template, and `Slots(β)` for its original profile. For an unannotated Function
literal `λ x -> e` in that slot, the proposed source derivation is:

```text
Γ ⊢ callee : Value(Fun(... Value(F_cb) ..., ...))
Γ ; expected-callback(F_cb, β, Slots(β)) ⊢ λ x -> e
```

The checking order is:

1. Obtain the callee's declared Function-valued formal and the already
   instantiated contract for this source use, preserving the original static
   slot identity/profile. Scheme instantiation itself is outside this gate.
2. Pass that expected callback context to the literal before generating any
   body constraint.
3. Select Handler receiver role from that expected context.
4. Independently generate the parameter interface and entry behavior from
   syntax under charter §21.
5. Elaborate the body under the resulting parameter environment and synthesize
   its result using core §6's `Result(I_b)` rule.
6. Form the literal's complete Function interface under the selected role.
   Compare that interface with the expected callback contract by ordinary
   `A <: B` obligations. A cast or adapter, if any, is evidence/realization
   from resolving a concrete inequality in that same solver.

Step 6 is an obligation, not a defined port rule here. In particular, the
literal's interface is not stipulated to equal `F_cb`, and `F_cb`'s ports are
not copied into the literal. The derivation must preserve one shared source
assignment and existing source-owned occurrence/incidence, `K,D`, `Rel_C`,
`Flow`/`Observe`, and directed-weight/subtraction evidence. It introduces no
new evidence carrier.

The judgment is bounded to an unannotated literal, a known callee, an ordinary
`Value(F_cb)` callback formal, and a supplied instantiated `F_cb`. It excludes
an explicit literal annotation, annotation/callback overlap, unknown callees,
retained `Computation` formals, import/member lookup, and general source
acceptance. The overlap remains a separate open source rule; retain both
original descriptors when deriving it later.

## 3. Source-order and runtime invariants

The expected context affects static introduction and constraint generation; it
does not move runtime effects. Whole-argument construction remains inert. At
execution, the ordinary Value-entry receiver is established and receives the
argument before its designated force and body. For argument computation `D`
and body `B`, the invocation retains the source sequence

```text
receipt; Force(D) >>= (v => B(v))
```

A retained Computation-entry formal instead binds the carrier without forcing
it unless its body explicitly consumes it. Receiver role and parameter-entry
role therefore remain independent.

`β` and `Slots(β)` describe the static callback declaration/use. The dynamic
receiver boundary `b` is created only when the receiver activation occurs.
This proposal preserves that distinction and does not mint a runtime boundary
while elaborating the literal.

## 4. Consequences and non-consequences

This proposal makes the callback role available before body constraints, which
is necessary to derive the handler-specific interface and its ports. It does
not itself prove

```text
Fun(a, never, b, c) <: Fun(a, d, [b,d], c)
```

or

```text
Fun(a, never, never, b) <: Fun(a, e, e, b)
```

Those remain joint Function-inequality obligations over role-derived complete
views. `never` remains a value bottom, distinct from the empty effect row and
polarized solver extrema; none receives an effect-position interpretation.
`Any` likewise remains a value type. Covariant rows remain canonical flat
forms; contravariant concrete-bearing descriptors retain only structure
needed for a witnessed partial reversal using existing subtraction evidence.

The source transition `Force(D) >>= B` supplies conditional invocation support
for a Value-entry callback over reachable post-force outcomes. It does not
license unconditional row union, independent port subtyping, or a new
subtraction/provenance calculus.

## 5. Candidate implementation seam, not selected API

Current HIR does not expose the required source inputs: `ResolvedExpr` has no
application node; `HirParameter` and `HirItem` carry no typed interface;
`SemanticImports` is empty; and `ConstraintBatch::collect` receives only an
`Arc<HirModule>`. The current collector also emits lambda body facts without
an expected-context input.

Two responsibilities are required but need not be implemented as separate
products:

- an immutable declaration/interface input that supplies the resolved formal,
  its instantiated `F_cb`, and original slot/profile identity;
- a source-owned contextual traversal that reaches the literal with that input
  before emitting body facts.

A transient context threaded through collection is the smallest candidate seam
only if collection owns or receives resolved application/literal structure and
the declaration input. A separate elaborated source product remains possible
if later evidence shows the collector cannot own that traversal. This draft
does not select between them, because current code contains neither required
input and provides no implementation comparison.

An unavailable formal must not silently cause a known callback-position
literal to fall back to Pure. Lookup failure, unsupported source structure, and
later interface incompatibility are distinct outcomes; this draft selects no
new diagnostic or recovery behavior.

## 6. Required review and next gate

Review this bounded contract for preservation of §21 entry/runtime order and
conformance with the single `A <: B` solver and charter §24. The proposal can
advance only if reviewers find no blocking or major defect. User approval is
required before any compiler implementation or durable API decision.

After approval, the next proof gate is to derive the complete role-indexed
Function interface for this supplied-context case and show where its two effect
views project into the existing `Rel_C`/`ν`, `K,D`, occurrence/incidence,
`Flow`/`Observe`, and subtraction evidence. Only an exact source fact not
representable there can justify additional evidence structure.
