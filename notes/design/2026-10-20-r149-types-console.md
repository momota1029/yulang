# R149: unchanged Yulang2 Types and Console examples

Status: Reviewed
Scope: Preserve the pinned Yulang2 Web `Types` and `Console` examples in the
Yulang3 CLI and Web playground, including inferred public types, evaluation
order, and captured output.
Drafted-by: Luna primary
Reviewed-by: compiler/source reviewer, spec reviewer
Supersedes: none

## Goal

Run the exact two source templates below without prefix extraction, source
rewriting, or injected `main` definitions. Keep the broader goal of running
unchanged Yulang2 Web examples; this pair is the next capability increment,
not a reduced compatibility target.

Oracle identity: repository `yulang2-oracle-capture`, commit
`a58eefc31e22141574b6f20c6a5748151c6d79f1`; file
`web/playground/src/main.ts`, blob
`e6bec9fe44d673ccbf98af078ef4562c9267ef6c`.
The pinned library blobs are `lib/std/core/fmt.yu`
(`fd7b6607094c9ad70bde1fd41890363fa8bd6b31`) and
`lib/std/io/console.yu` (`8c8eabe69755d28bc66a850745f5ea72c136cd74`).
The resolution path also includes `lib/std/prelude.yu`
(`e31685be6f17a516b47c3c29c3a124d7ff1c3682`) and `lib/std/io.yu`
(`4e1852f94f9d5c5c2c47f65bc7b75374a9418f93`), which provide the unqualified
Console imports and re-exports; `lib/std/core/ops.yu`
(`575e6fb15ce2d91a39004bbc7b842fedb2d83fdf`) and `lib/std/int.yu`
(`198b8c2d1ba157e3a9507d1f9353f1bc8df9520c`) provide the `+` and integer
display primitive leaves.

| Example | UTF-8 bytes | SHA-256 | Required observable result |
|---|---:|---|---|
| Types | 142 | `8cbfb97a8df8e5dc4916313769c39a84626ae124f91f8a9672f1ad8b866f98e6` | Types pane entries include polymorphic `id`, `answer: int`, `name: str`, and `pair: (int, str)`; separately, host write payload is `(42, Yulang)\n` |
| Console | 92 | `ada6174d8795ddb10a8c533c812b771d9dddced816762e0e246022467499a076` | Captured writes in source order: `hello from Yulang\n`, then `3\n` |

The templates are the complete bytes in the pinned file, including comments
and trailing newline:

```yu
// our and pub bindings appear in the Types pane.

our id x = x
pub answer = id 42
pub name = id "Yulang"
pub pair = (answer, name)

pair.say
```

```yu
// println is a library effect handled by the host.

println "hello from Yulang"
say: 1 + 2
```

## Proposed behavior

1. Tuples are ordinary positional product values. Tuple construction,
   destructuring, type inference, and evaluation preserve element order and
   element types. The Types example infers `(int, str)` for `pair`.
2. `.say` resolves through the standard `Display` role implementation. The
   pinned Yulang2 `std/core/fmt.yu` defines pair display by recursively calling
   `show` on both elements and joining them with `, ` inside parentheses. The
   role implementation remains ordinary source/library resolution; the
   compiler and evaluator do not recognize the spelling `say` specially.
3. The Console example resolves `println` and `say` through the standard
   library. The pinned `std/io/console.yu` defines `println` by calling
   `out::write` with a newline-terminated string, and defines generic `say`
   through `Display` and the same host write operation.
4. A whole-module run consumes the existing mixed source schedule of
   computation definitions and expression roots in source order. It preserves
   lazy value materialization, cached successful values, forward demands, and
   computation definition initialization; it completes with unit when the
   schedule is exhausted. A schedule may not silently omit a computation
   initializer that the source interface marks for execution.
5. The host handles only the actual imported `out::write` declaration whose
   resolved type is `str -> ()`. It checks the declaration identity, string
   payload, and unit response, captures the payload once, and resumes the
   exact saved continuation once. Other unhandled operations remain errors.
   Capturing output does not erase effects from typing or execution.
6. Host write payloads are concatenated in source evaluation order by the CLI.
   Web output retains each write event as a separate ordered result. For Types,
   the single payload is `(42, Yulang)\n`; for Console, the payloads are
   `hello from Yulang\n` and `3\n`.
7. Public type display is derived from the same accepted inference result as
   execution. Failed inference produces no output or Types pane entries.

## Proposed decisions for review and user approval

- Support the tuple arities accepted by the pinned Yulang2 grammar and runtime,
  with tuple inference and evaluation preserving arbitrary finite element
  order. Do not impose a pair-only language limit for this example.
- Load and resolve the actual pinned standard-library source definitions,
  including `prelude.yu`, `io.yu`, `io/console.yu`, `core/fmt.yu`, `core/ops.yu`,
  and `int.yu`. Integer display and integer/string `+` follow the resolved
  standard-library wrappers to their actual primitive owners. Do not add
  intrinsic name checks for `say`, `println`, `show`, or `out::write`.
- Add an explicit whole-module execution entrypoint that consumes the retained
  mixed source schedule without requiring a selected `DefId`; retain the
  selected-definition entrypoint. The Web playground uses whole-module mode
  for these exact examples; CLI exposes the same mode explicitly.
- Host write payloads are concatenated in source evaluation order by the CLI.
  Web output retains each write event as a separate ordered result. For Types,
  the single payload is `(42, Yulang)\n`; for Console, the payloads are
  `hello from Yulang\n` and `3\n`.
- Inference publication: specify that the exact module's public types and
  output become visible only after the same module's inference result is
  accepted; no partial output on rejection or resource exhaustion.

The independent reviewers must check these alternatives against current Y3
authority, the pinned Y2 source/library, parser and HIR owners, effect
semantics, and existing runtime admission. User approval is required before
implementation because the proposal adds tuple semantics and a module-output
execution surface.

## Explicit exclusions

This proposal does not close Simple-sub/evaluator A/B, R70/R71, general
source/native correspondence, full standard-library compatibility, or the
remaining Yulang2 Web catalog. It does not alter error examples, frozen main,
or expected outputs. No R148 instrumentation or 120-second remainder carries
forward.
