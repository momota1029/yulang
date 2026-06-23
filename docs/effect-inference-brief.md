# Hygienic Effect Inference in Yulang

Status: outward-facing draft, 2026-06-23.

This is the short version of the claim Yulang can make today. It is meant for
README links, research introductions, and article drafts. It is not the formal
solver specification; use `docs/infer-solver-invariants.md` for the working
contract and `research/effect-mini-language/directed_stack_weight_letrec_complete_ja.tex`
for the theory draft.

## Safe Headline

Yulang aims to keep effectful programs easy to write while preserving hygienic
handler boundaries and principal-style public signatures.

The conservative wording matters:

- "handler hygiene" is a concrete property of the current implementation;
- "principal-style public signatures" describes the user-facing result without
  claiming the public projection is already fully formalized as a principal
  type theorem;
- the stronger theorem belongs to the hidden weighted scheme and still needs
  careful presentation.

## What Is New

Yulang combines four pieces that are usually explained separately.

1. Algebraic effects are inferred as ordinary effect rows.
2. Handler visibility is tracked internally with directed stack evidence.
3. Public types hide that evidence and show ordinary residual rows.
4. Annotations can constrain a function skeleton and effect visibility without
   choosing concrete value types or fixed effect-family sets.

For direct code, a handler looks like row subtraction:

```text
alpha [console; beta] -> [beta] alpha
```

For higher-order code, plain row subtraction is not enough. If a callback or
stored field performs an effect, an inner handler must not steal that effect
just because it has the same family name. Yulang tracks which effects are
visible at each handler boundary and subtracts only those.

## Mechanism in One Page

Internally, subtype constraints carry directed weights:

```text
T @L <: @R U
```

An effect row upper bound is split only by the effect families visible through
the left weight:

```text
alpha @L <: [K; beta]
J = K intersection Common(L)
alpha <: [J; gamma]
gamma @ (L minus J) <: beta
```

This is the reason a handler can consume its own visible operation while
leaving caller-supplied effects alone. The directed evidence is not source
syntax and should not appear in hovers, diagnostics, or public signatures.

## Main Examples and Canaries

The first two examples are the clean introduction. The remaining examples are
canaries that keep the implementation honest.

1. Higher-order inference:
   `examples/effect-hygiene/01_higher_order_inference.yu`

   ```text
   apply : (a -> [e] b) -> a -> [e] b
   ```

   The latent effect of the function argument remains visible in the caller's
   result.

2. Effect-only handler skeleton:
   `examples/effect-hygiene/02_local_sub_handler.yu`

   ```text
   sub.sub : a [sub c; e] -> [e] a | c
   ```

   The handler consumes the visible `sub` effect and preserves the residual
   row. The same handler is used at `int` and `str`, and a separate `note`
   effect remains visible in the residual row.

3. Data-position private evidence:
   `examples/effect-hygiene/03_data_position_private_tail.yu`

   A stored effectful function needs hidden evidence internally, but the public
   method type should expose only ordinary residual rows.

4. Standard parser choice:
   `std.text.parse.choice`

   Parser backtracking uses handlers and continuations, but the public type
   keeps parser effects as ordinary rows and role constraints.

5. Reference update:
   `std.control.var.ref.update`

   This is the canary for private evidence leakage. The public signature should
   keep the reference residual and callback residual while hiding `ref_update`
   stack evidence.

## What Not To Claim Yet

Do not present the current public projection as a finished principal type
theorem. The better claim is:

```text
The solver computes a hidden weighted scheme, then projects it to a
principal-style public signature.
```

Open questions remain around:

- the exact generality order for public projected schemes;
- formalizing same-boundary replay-cycle subsumption;
- naming the relationship between data-position private tails and local
  wildcard handler evidence;
- proving termination for the full implementation graph rather than the core
  calculus.

## Useful Internal Links

- `docs/infer-solver-invariants.md`
- `docs/hidden-effect-evidence.ja.md`
- `web/docs/reference/effects.md`
- `web/docs/reference/type-theory.md`
- `notes/research/consultation/technical-brief.md`
- `notes/diagnostics/2026-06-23-ref_update.md`
