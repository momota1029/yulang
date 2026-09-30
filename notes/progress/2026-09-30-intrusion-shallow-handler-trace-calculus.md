# Shallow handler trace semantics: first candidate

Date: 2026-09-30
Status: exploratory semantic candidate; non-authoritative; proof incomplete
Scope: ordinary algebraic effect requests, shallow catch, exact finite traces
Implementation authority: none
Oracle: frozen Yulang2 `main` at `a58eefc3`

## 1. Why this slice

The user directed that Oracle weight propagation and left/right routing be
characterization evidence only, and that effect meaning be derived independently
before retaining or transforming weights. The current source-level probes also
show that handler semantics cannot be reduced to a family-set subtraction:
shallow resumption may expose an operation again after one request has been
handled.

This note defines a small trace model for the direct, non-higher-order fragment.
It does not define provider ownership / hygiene, a finite principal row syntax,
SCC transport, or a sound/principal weight calculus. It is a proof target for
those extensions, not a change to the language contract or implementation
instruction.

## 2. Semantic objects

For a value domain `V`, a computation is a free resumable tree:

```text
C ::= Return(v)
    | Request(op, payload, k)

k : OperationResult(op) -> C
```

`Request` stores the continuation after this particular request. Sequential
composition is defined by:

```text
Return(v)       >>= f = f(v)
Request(o,p,k)  >>= f = Request(o,p, \x -> k(x) >>= f)
```

A trace observation is a finite path through this tree. Its effect support is
the set of operation-family labels on requests along that path; the bound for a
computation is the union of supports over its possible paths. In the finite
set-row fragment, order is inclusion, so the least bound is the union of the
actual supports. Payload types and values remain attached to requests and are
not erased by this support projection.

Handler activations have fresh identities. For this first direct fragment,
`eligible(h, request)` means the active handler `h` has a matching operation
arm and the request is not masked by an ownership guard. The direct fixtures
below have no imported callback provider, so the matching catch activation is
eligible. The precise ownership-guard rule is deliberately open; no Oracle
weight constructor defines `eligible`.

## 3. Shallow catch transformer

For a catch `H` with a value arm and operation arms, define its action on one
computation tree as follows:

```text
H(Return(v)) = evaluate the value arm on v

H(Request(o,p,k)) =
    evaluate the matching operation arm on (p, k)   if eligible and covered
    Request(o,p, \x -> H(k(x)))                     otherwise
```

The matching arm receives the raw continuation `k`. It does not receive
`x -> H(k(x))`. Therefore resuming a matching request does not automatically
reinstall that same catch. An unmatched request is forwarded with the catch
wrapped around its continuation, so if an outer handler handles it and resumes,
this catch still sees later requests.

This is a declarative shallow-handler rule. It agrees with the frozen source
contract's documented shallow behavior, but its truth here does not come from
`StackWeight`, `SubtractId`, row routing, or their implementation.

## 4. Two trace lemmas

### Lemma 1: one handled request can have an empty residual

Let:

```text
C1 = Request(ping, 1, \n -> Return(n))
```

and let the matching arm resume with the payload, `arm(p,k) = k(p)`. Then:

```text
H(C1) = k(1) = Return(1)
```

so the exact outward effect support is empty. This follows by one application of
the shallow transformer and the definition of `Return`; no row subtraction
law is assumed.

### Lemma 2: a later request can escape shallow resumption

Let:

```text
C2 = Request(ping, 1,
       \x -> Request(ping, 2, \y -> Return((x,y))))
```

The first request matches. Its arm receives the raw continuation and resumes it,
so `H(C2)` evaluates to the second `Request(ping, 2, ...)` without applying `H`
to that matching continuation. The outward effect support contains `choose`.
A least family-set upper bound therefore retains `choose` for this example.

These two cases rule out unconditional subtraction of a handled family from a
whole computation effect: the residual depends on the continuation after the
specific request. The family label alone does not determine it.

## 5. Frozen-Oracle characterization

The following source probes use the prebuilt CLI from the disposable frozen
Oracle checkout. They are observations of its acceptance, inference, and
runtime, not semantic authorities.

### One request, continuation resumes, no later request

```yu
act choose:
  our ping: int -> int

my shallow_one() = catch choose::ping 1:
  choose::ping n, k -> k n
  v -> v
shallow_one()
```

`check` succeeds; `run --interpreter --print-roots` returns `[1]`. The inferred
`shallow_one` Function scheme nevertheless has `ret_eff = Row([choose])`.
The more precise annotation
`my shallow_one(): [] int = ...` is rejected with
`effect filter mismatch: choose is not allowed by []`. By Lemma 1, an exact
finite-trace support semantics gives this closed computation an empty residual.
Under the finite-trace support order defined in §2, `Row([choose])` is strictly
above the least valid support `Empty`: this continuation has no later request.
This is a concrete counterexample to principal projection relative to this
candidate order and the source-level shallow semantics. It is not an
unsoundness claim; Oracle's overapproximation remains a valid upper bound. The
compatibility difference is precise: frozen Oracle rejects
`shallow_one(): [] int`, while the successor should accept it if the
occurrence-sensitive continuation analysis is proved. Source lowering at
`control.rs:1603–1629` assigns the continuation the whole scrutinee effect,
which explains this overapproximation; no left/right weight transformation is
isolated as its cause.

The rejected annotation is important. A previous top-level binding annotation
such as `my result: int = ...` constrains the stored value type, not the
initializer's computation effect. Its value-only poly scheme cannot prove that
the computation was inferred pure.

### Two requests, first continuation resumes into the second

```yu
act choose:
  our ping: int -> int

my shallow_two() = catch (choose::ping 1, choose::ping 2):
  choose::ping n, k -> k n
  v -> v
shallow_two()
```

The inferred Function scheme has `ret_eff = Row([choose])`. The interpreter and
evidence VM report `unhandled-effect` at the second `choose::ping`. This matches
Lemma 2 and the shallow handler contract. Its pure effect annotation is rejected.
Thus the correct successor must retain the residual for the second request even
while improving the one-request case.

A higher-order variant uses `twice(x,y,f) = (f x, f y)` and passes
`\x -> choose::ping x` beneath the same catch. The inferred handler result also
retains `[choose]`, and runtime leaves the second request unhandled. Prior
instrumentation observes two per-call pushes sharing one frame pop in this
helper shape. Since the direct two-request program has the same shallow trace
without a callback, this runtime behavior does not establish a weight-routing
fault. The helper case is retained as a mandatory encoding test: it must agree
with the direct trace after provider visibility and the shared boundary have
been modeled.

### No resumption

If the operation arm ignores `k` and returns `n`, Oracle accepts
`my handled_without_resume(): [] int = catch choose::ping 1: ...` and runtime
returns `[1]`. The compiler therefore distinguishes a clause that does not
resume from one whose continuation may produce more effects, but its current
continuation effect is too coarse to prove the exact empty suffix in the
resuming one-request case.

## 6. What this establishes and what it does not

Established by the independent trace calculation:

- Shallow semantics requires the matching arm's continuation to retain the
  effects of its actual suffix, without rewrapping the same handler.
- An exact one-request suffix is pure after resume.
- A second request in that suffix escapes unless a different/outer handler
  handles it.
- A family-only row summary may lose the distinction; a suffix-sensitive
  semantic object can preserve it.

Characterized in the frozen Oracle source:

- `control.rs:1562–1629` assigns the continuation Function's return effect to
  the whole `scrutinee_effect`.
- The `k n` arm body's effect flows into the handler result.
- Consequently the one-request example retains `choose`, while a non-resuming
  arm can be pure. A pure effect annotation for the one-request case is rejected.
- The direct two-request effect residual is consistent with shallow semantics.

Not established:

- A formal soundness or principality theorem for the successor.
- That the counterexample extends beyond the finite direct fragment or proves a
  global Oracle principality failure. It depends on the candidate order in §2
  and exact suffix denotation; higher-order effects remain open.
- Any unsoundness in Oracle weight propagation or any causal role for a
  left/right weight transformation in these examples.
- The provider-ownership rule for callbacks, thunks, nested handler activations,
  or runtime guard identities.
- Projection of shared residual variables for arbitrary weights.

If the successor adopts exact finite-trace support for this fragment, record
its compatibility difference precisely: accept a pure (`[]`) effect annotation
for `shallow_one`, which frozen Oracle rejects as `choose`-effectful; continue
to expose `choose` for `shallow_two`. Preserve shallow request semantics in
both cases. This delta improves final well-typed acceptance without changing
runtime handler behavior. It becomes authoritative only after independent
semantic/specification review and a proof of the stated envelope.

## 7. Next proof obligations

1. Define path/suffix denotation and an effect order for values, operations,
   latent functions, thunks, and open outer assignments.
2. Prove that projection from trace sets to finite family rows returns a least
   representable bound for the finite direct fragment.
3. State the exact source/lowering relation that constructs the request tree and
   continuation suffix; prove correspondence for one, repeated, and
   non-resuming operation clauses.
4. Add provider identity / handler eligibility without conflating it with
   operation-family identity. Cover a global delayed thunk forced under a catch,
   an outer-owned callback crossing an inner same-family catch, and an
   inner-owned callback.
5. Only then define any weight as an encoding of this visibility/suffix
   relation. Prove every left/right transformation preserves it, including
   repeated pushes with one shared pop, nested frames, incomplete handlers, and
   shared residual fan-out.
6. Compare the encoding against the Oracle characterizations and record each
   accepted compatibility delta before moving to SCC parent transport.

No code, inference implementation, or weight rewrite is authorized by this
candidate. Method selection, roles, and implementation resolution remain the
later gate recorded in the redesign charter.

## 8. Focused commands

Commands were run with `/tmp/yulang-intrusion-oracle/target/debug/yulang`:

```text
/tmp/yulang-intrusion-oracle/target/debug/yulang --no-prelude --no-cache check /tmp/yulang-intrusion-weight-shallow-one-pure.yu
/tmp/yulang-intrusion-oracle/target/debug/yulang --no-prelude --no-cache check /tmp/yulang-intrusion-weight-shallow-one-inferred.yu
/tmp/yulang-intrusion-oracle/target/debug/yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-weight-shallow-one-inferred.yu --poly-raw
/tmp/yulang-intrusion-oracle/target/debug/yulang --no-prelude --no-cache run --interpreter --print-roots /tmp/yulang-intrusion-weight-shallow-one-inferred.yu
/tmp/yulang-intrusion-oracle/target/debug/yulang --no-prelude --no-cache run --evidence-vm --print-roots /tmp/yulang-intrusion-weight-shallow-one-inferred.yu
/tmp/yulang-intrusion-oracle/target/debug/yulang --no-prelude --no-cache check /tmp/yulang-intrusion-weight-shallow-inferred.yu
/tmp/yulang-intrusion-oracle/target/debug/yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-weight-shallow-inferred.yu --poly-raw
/tmp/yulang-intrusion-oracle/target/debug/yulang --no-prelude --no-cache run --interpreter --print-roots /tmp/yulang-intrusion-weight-shallow-inferred.yu
/tmp/yulang-intrusion-oracle/target/debug/yulang --no-prelude --no-cache run --evidence-vm --print-roots /tmp/yulang-intrusion-weight-shallow-inferred.yu
/tmp/yulang-intrusion-oracle/target/debug/yulang --no-prelude --no-cache check /tmp/yulang-intrusion-weight-shallow-nonresume.yu
/tmp/yulang-intrusion-oracle/target/debug/yulang --no-prelude --no-cache run --interpreter --print-roots /tmp/yulang-intrusion-weight-shallow-nonresume.yu
/tmp/yulang-intrusion-oracle/target/debug/yulang --no-prelude --no-cache check /tmp/yulang-intrusion-weight-repeated-pure.yu
/tmp/yulang-intrusion-oracle/target/debug/yulang --no-prelude --no-cache run --interpreter --print-roots /tmp/yulang-intrusion-weight-repeated-pure.yu
/tmp/yulang-intrusion-oracle/target/debug/yulang --no-prelude --no-cache run --evidence-vm --print-roots /tmp/yulang-intrusion-weight-repeated-pure.yu
```

## Independent review

A `spec_auditor` checked the transformer rules and both trace examples against
the frozen source contract and the successor charter. No conformance findings
were reported. A `compiler_referee` checked the one-request source lowering and
runtime continuation: the base continuation returns the resumed value, while
lowering assigns `k` the whole scrutinee effect. This supports the localized
overapproximation explanation; it does not establish a weight-routing defect or
a global principality failure.

Expected observations: the pure one-request annotation rejects with a `choose`
filter mismatch; inferred `shallow_one` has `[choose]` despite runtime `[1]`; a
non-resuming clause has an empty effect and returns `[1]`; the repeated case
retains `[choose]` and both VMs report the second request unhandled. All scratch
sources stayed under `/tmp`; no frozen-Oracle checkout files were modified.
