# Authentic effect operation source: next implementation gate

Date: 2026-10-10
Branch: `research/simple-sub-intrusion`
Current committed baseline: `477a5d15476a8187ea883ed9402e59bb6fd9d7ba`
Frozen Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Status: constructor correspondence and parser witness; implementation pending
Mode: bounded read-only explorer/architect mapping, M0 primary synchronization

## Actual source witness

The existing runtime fixture is
`tests/perf/runtime/v0/effect_operation/shallow_tick_10000/main.yu`.
Its operation is declared by the owning Act and referenced by qualified path:

```yulang
act tick:
    our next: () -> int

my run x = tick::next()
```

A primary-owned scratch Rust executable linked the existing unchanged
`target/debug/libyu_syntax.rlib` and parsed exactly this newline-separated source.
Syntax diagnostics were `Ok([])` and structural recoveries were empty. The CST
retains `ParenthesizedTypeGroup` at 24..26, `PathTail` at 50..56 and empty
`CallTail` at 56..58. The scratch input and output reside under
`/tmp/yulang-operation-cst-primary/`; they are not repository artifacts.
This is parser evidence only, not HIR, inference or operation execution evidence.

## Unit is an existing primitive

The frozen Oracle constructors resolve the earlier provisional representation
question. Empty parentheses use primitive Unit, not a zero-field Record or a
zero-element Tuple:

- `crates/infer/src/lowering/expr/chain.rs:590` dispatches parentheses to
  `expr/block_local.rs::lower_paren`; its empty branch at 17 calls `unit_expr`.
- `expr/tail.rs:728–733` constructs exact-pure effect, primitive `unit` type
  and `Expr::Lit(Lit::Unit)`.
- `expr/tail.rs:95–105` constructs the same Unit argument for an empty call
  and routes it through ordinary `make_source_app`.
- `annotation/builder.rs:265–277` selects `BuiltinType::Unit` for an empty
  type group; multiple elements have the separate Tuple constructor.
- `act_resolve.rs:175–183` retains Unit in Act operation signatures.
- `lowering/neg_signature.rs:187–199` retains Unit in ordinary signatures.
- `lowering/mod.rs:783–807` constructs the positive/negative nominal primitive
  `Con(["unit"], [])`.

The separate `lowering/record_lit.rs::synthetic_record_value` is not the empty
parentheses owner. The earlier provisional zero-element-tuple recommendation
is withdrawn. No new user semantic decision is required for ordinary compatible
Unit support; public enum extensions still require pre-write conformance review.

## Coupled implementation responsibilities

1. Add positive/negative Unit constructors and ordinary comparison, including
   the owning `yu-types`, solver endpoint/shape and source carrier seams.
   Preserve kind, polarity, capture/freshening/extrusion and diagnostic behavior.
2. Retain Act operation declarations, their actual declaration-owned identity,
   visibility and signature. Do not accept an Act body while discarding it.
3. Resolve `tick::next` through the admitted family and operation namespaces.
   Field access `tick.next` and unqualified lookup are separate owners.
4. Lower explicit Unit and the empty call's implicit Unit at actual source
   occurrences, then use ordinary Apply constraints. Looking up the operation
   remains pure; its family support is latent at the invocation interface.
5. Preserve operation declaration and use provenance, independent instances,
   annotation support versus emitted contribution, and attachment ownership.

The current opt-in HIR rejects Act bodies, qualified operation paths and empty
calls; its annotation/value carriers and `yu-types` have no Unit constructor.
The concrete/co annotation implementation is a separate moving lease. Serialize
the shared HIR/solver seam until that artifact freezes and is integrated; do not
certify against unfinished dependencies or add a full registry prerequisite to
basic source constraint generation.

Construction of an operation request and its execution remain distinct. Existing
complete Call authority treats `ApplyValue(Operation)` as constructing a request
thunk, with source-demanded Force executing it. Four-port constraints alone do
not certify this contract or full runtime effect emission.

No production code changed. No Cargo command, backend test, semantic proof or
benchmark ran for this lookup. One scratch parser process was executed; timing
measurement budget consumed: zero samples/processes. Complete Call, hygiene,
soundness, principality and default/public F5 replacement remain open.
