# Callback expected-context delivery before literal-body elaboration

Status: Authoritative
Date: 2026-10-03
Scope: bounded source elaboration for one unannotated Function literal passed to a known Function-valued callback formal
Approved-by: user, 2026-10-03 (bounded source contract only)
Drafted-by: primary
Reviewed-by: architect, compiler_referee, and spec_auditor (2026-10-03, including §4 and §8 deltas); no unresolved findings
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

## 4. Contextual introduction and existing-value adaptation are distinct

The callback-position literal rule and the intended pure-function lift concern
different source paths:

| Source path | Source role | Required semantic check |
|---|---|---|
| An unannotated literal appears directly in a known callback slot | Handler from the expected context, before body constraints | Elaborate that literal under the supplied callback boundary; do not first construct it as Pure and repair it afterward. |
| An already constructed Pure function value is supplied to a handler-capable callback slot | Preserve the value's actual Pure introduction and its §21 entry | Resolve the concrete inequality between the actual value interface and the checked callback interface; any adapter is evidence/realization from that one query. |

The first path selects how a new literal is introduced. It does not prove the
second path's concrete inequality. Conversely, success of that concrete
inequality cannot be composed with another successful concrete comparison to
establish a third one. Both paths use the same endpoint-dependent `A <: B`
solver, but their source derivations have different premises and obligations.

The stable-core fixture anchors the first path: the public signature for
`std.control.var.ref.update` declares callback shape `('c -> ['b] 'c)`, and
`r.update (\old -> old + "!")` places an unannotated literal in that callback
slot. The expected context selects Handler even though the literal body is
pure string concatenation. The public implementation is not present here, so
this fixture does not derive the complete callback transition, source
challenge domain, or the pure-value adaptation.

For the second path, §21's actual entry and the original decorated behavior
must remain executable under the handler-capable slot view. For a Value-entry
call, `receipt; Force(D) >>= B` conditionally places requests from both the
forced argument and reached body states in the common invocation. Relating
those events to the target profile still requires typed receipt/`Flow`,
event-specific `Observe`, occurrence/incidence, and both complete-domain
clauses under one `Rel_C` fiber and `ν`. This source support does not establish
that either port can be interpreted independently, that a row union is
unconditional, or that the intended inequality is proved.

## 5. Consequences and non-consequences

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

## 6. Candidate implementation seam, not selected API

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

## 7. Required review and next gate

Review this bounded contract for preservation of §21 entry/runtime order and
conformance with the single `A <: B` solver and charter §24. The proposal can
advance only if reviewers find no blocking or major defect. User approval is
required before any compiler implementation or durable API decision.

The next proof gate for the intended pure-to-handler inequality must use an
already constructed Pure value as its source premise, not the Handler-role
literal in §2. Derive one complete callback `CallView` and show
`D_checked(ν) ⊆ D_actual(ν)` and `P_actual(d) ⊆ P_checked(d)` under one
`Rel_C`/`ν` fiber, then project its effect views through `K,D`,
occurrence/incidence, `Flow`/`Observe`, and existing subtraction evidence.
Only an exact source fact not representable there can justify additional
evidence structure. This proof-only work does not select a compiler API or
authorize implementation.

## 8. Smallest discriminating source witness for the Pure-value lift

The smallest useful source-shaped witness keeps the callback value separate
from its introduction context:

```text
f = \x -> x                  // introduced Pure; §21 gives Value(A) entry
pass_existing_callback(f)    // witness specializes its shared A to Int
```

Use an already constructed `f`, not an inline callback literal. The
higher-order receiver receives `f` at its callback slot and invokes it during
that same receiver activation, while the slot's handler-capable boundary is
still live. Invoke the callback view with an inert argument carrier `D_req`
that emits one declared request, resumes with an `Int`, then returns. Under
the source call schedule, the candidate order is:

```text
activate the callback-slot receiver boundary
receive existing Pure value f through the typed callback slot
inertly construct D_req and establish f's actual invocation
receive D_req at f's Value(A) entry inside that invocation
Force(D_req) >>= (n => execute f's actual body with n)
```

The source proof must distinguish the slot's receipt of `f` from `f`'s
invocation receipt of `D_req`. It must establish that the handler-capable
boundary is active throughout the actual invocation and before
`Force(D_req)`, the request has a typed path to the target's complete
observation view, receipt does not change `f`'s actual entry, and resumption
continues the same rebind/body suffix. This witness does not cover a callback
that escapes the receiver and is invoked after its boundary ends; that case
needs its own live `CallView` derivation. The corresponding checked challenge
and its actual execution must share one nonempty, jointly well-formed `ν`,
`K,D` assignment, with `A = Int`. For this witness the body is identity; this
does not remove the general obligation to cover body effects `b` at every
post-force state.

Pair it with a pure-diverging argument carrier of the same result endpoint.
This second challenge has empty request support but never reaches the body. It
distinguishes Value-entry execution and challenge admission from an argument
row that records only requests. Empty support therefore cannot stand in for
the complete domain or receipt/entry proof.

These are proof witnesses, not asserted accepted programs or test fixtures.
The checked-to-actual domain inclusion must establish both challenges as
admissible; the actual-to-checked observation inclusion must preserve the
request, response dependency, current state, and pending suffix. If the
slot-view rule cannot admit the request carrier without changing the Pure
value's entry or boundary authority, this candidate lift fails. If it can,
the request path must be projected through existing `Receive`, `Flow`,
`Observe`, occurrence/incidence, and subtraction evidence before the target
flat output view `[b,d]` can be justified. No claim here interprets `never`,
proves either complete-domain clause, or derives the intended inequality.
