# Paired annotation PUSH bridge into the nested callback effect

Date: 2026-10-10
Status: source bridge and bounded Oracle trace reviewed; source-owner map and
successor correspondence open
Successor baseline: `3bb355b56`
Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Authority: user-selected polarity-sensitive effect-hygiene policy

## Source-owner result

Distinct allocation of the annotated callback's outer return-effect variable
`t` and inner wildcard return-effect variable `h` does not prove global
separation. Reannotating the same monomorphic callback formal with symbolic
row tails can transport the original attachment ID `i` between these owners.

The important syntax is a row tail after the semicolon, for example `[; 'e]`.
`['e]` is parsed as an effect-type atom; it is not the row-tail bridge and can
allocate a fresh Empty-family attachment. The candidate below locates the
source construction, but its original wildcard form is not accepted. It parses
and then fails lowering with `WildcardEffectRowInTypePosition`. Replacing `[_]`
with `[; 'h]` produces a different source that parses and lowers successfully;
it is useful for this trace, but does not establish equivalence to the wildcard
source.

```yulang
type io
my loop(x: ((int -> [io] (int -> [_] 'c)), int)) =
  \(f, _) -> {
    my a: int -> [; 'e] (int -> [; 'e] 'u) = f;
    my b: int -> [; 'd] (int -> [; 'd] 'v) = f;
    (f 1) 2;
    (loop x) x
  }
```

For one local annotation, let `e` be its shared symbolic effect tail. The
paired formal comparisons generate:

| Endpoints | Context | Origin |
| --- | --- | --- |
| `t <: e` | left `PUSH_i[{io}]` | Original callback positive interface against the added annotation's negative outer Function result |
| `e <: t` | identity after `{io}` filter check/registration | Added positive outer Function result against the original callback negative interface |
| `h <: e` | left `POP_i` | Original positive returned Function's `NonSubtract` wrapper |
| `e <: h` | identity | Added positive inner result against the original callback negative inner result |

`annotation/constraints.rs:132–153,363–389,430–470` constructs the two
interfaces; `constraints/machine/propagate.rs:26–34,207–271` decomposes
Function ports and normalizes the lower `NonSubtract` with a left prefix.
`[; 'e]` takes the direct variable-tail route at
`annotation/constraints.rs:430–439`, so it introduces no new `SubtractId`.
The local name resolves to the same monomorphic formal value:
`lowering/name_ref.rs:146–153`, `lowering/expr/tail.rs:855–858`, and
`lowering/expr/block_local.rs:570–578,899–932`.

The graph therefore carries same-ID PUSH evidence from `t` through `e` to
`h`; this is not global separation of the two source owners. It does not by
itself establish a distinguishing admitted context at `h <: E`.

## Replay and alias admission

The existing recursive cycle supplies `h <: E` under right `POP_i²`, and
repetition offers right `POP_i³`. The annotation's `h <: e` has a **left**
`POP_i`, because `NonSubtract` is normalized by `with_left_prefix`
(`propagate.rs:26–34`). Composing through `e <: h` and the existing `h <: E`
path offers:

```text
e --identity--> h --right POP_i²--> E
  => e --right POP_i²--> E

h --left POP_i--> e --right POP_i²--> E
  => h --right POP_i³--> E
```

This is additive POP count, not cancellation. At the same `h/E` endpoints,
right POP² and POP³ share Oracle's alias key `([], [i])` and one candidate is
suppressed before replay. Which representative survives depends on actual
admission order.

The ordered trace for the `[; 'h]` variant does not establish the proposed
named `e/E` suppression. For Pos33/TV20 → Neg69/TV50, left POP1 is inserted
before left POP2, and the POP1 bounds subsume the later POP2. For Pos4/TV5 →
Neg69/TV50, right POP2 is inserted before right POP3 and POP4, which are
subsumed. These are endpoint-specific observations. The instrumentation does
not retain annotation occurrence-to-TypeVar or extrusion/freshening ownership,
so TV50 cannot yet be identified as the named source `E` from this trace.

The log contains no admitted bound, replay offer, or enqueue attempt with both
a positive PUSH count and a positive POP count. Thus it does not establish a
mixed PUSH-bearing replay parent. This is limited to normalized contexts
visible to the instrumentation and does not exclude transient unlogged
composition.

Two annotations add a distinct symbolic coordinate and permit a graph-level
walk carrying `left (POP_i PUSH_i²)`. This does not show that it is admitted:
the alias key retains attachment ID, leading-POP presence, family and
PUSH-presence on the left, while forgetting counts. An earlier same-pair
`left (POP_i PUSH_i)` bound can subsume the doubled-push candidate. Same-
endpoint self-edge omission is a separate rule. The source graph walk is not a
counterexample to Oracle's guard.

The missing evidence is an ordered trace through `(loop x) x`: canonical
endpoint IDs after extrusion, candidate weights, first surviving records,
bound dispositions and replay parents, beginning at the `e/E` slot. It must
show whether POP²/POP³ and any
potentially distinguishing mixed PUSH context reach source-identified `h/E`
before alias suppression. The original wildcard source is rejected during
lowering; the changed symbolic-row variant succeeds in the pinned Oracle
harness but does not establish the intended callback scheme, runtime behavior,
guard soundness, successor portability or whole termination.

## Verification and provenance

An independent compiler-referee confirmed the source bridge and reviewed the
ordered trace, correcting the predicted suppression direction: at the first
logged endpoint, POP1 survives and suppresses POP2. A bounded instrumented
Oracle harness build and two source runs established parse/lower status and
the endpoint events above. The harness was built with one Cargo job, a 3 GiB
process-group RSS cap and 180-second wall cap; peak sampled build RSS was about
2.27 GB. The original source parsed but failed lowering; the symbolic-row
variant lowered with zero errors. No successor build/tests or performance
study ran. This source-research checkpoint closes no effect-hygiene,
complete-Call, termination, soundness/principality or cutover gate.
