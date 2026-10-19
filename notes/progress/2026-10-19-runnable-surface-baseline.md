# Runnable surface baseline: ordinary Apply and one handled effect

Date: 2026-10-19
Branch baseline: `bfedb3ddfb341aa8d1156d48b9446f7fc7c88986`
Status: exploratory runtime evidence from `yu-playground`; no production or theorem gate closes.

## Ordinary source-to-runtime path

Command:

```sh
CARGO_BUILD_JOBS=2 timeout 120s cargo run -q -p yu-playground -- --run answer --steps 100000 -
```

Input:

```yu
my identity x = x
my answer = identity 42
```

Result: exit 0, stdout `42`. This demonstrates the existing experimental candidate inference plus provisional evaluator for one ordinary curried Call/Apply path.

## One effect capture/resumption path

Command:

```sh
printf 'act io:\n    our tick: int -> int\nmy relay (thunk:[io] int) = catch thunk { io::tick(p), k -> k 11 }\nmy main = relay (io::tick 7)\n' | CARGO_BUILD_JOBS=2 timeout 120s cargo run -q -p yu-playground -- --run main -
```

Result: exit 0, stdout `11`. The source exercises one `[io]` Computation receiving path, matching `tick` handling and one continuation resumption. It is finite runtime evidence for this candidate route only; it proves neither general effect hygiene nor native/source correspondence.

## Role-call boundary observed

`--run` on the R85 proposed `SecondInt::second 1 2` shape and on the checked-in `attached_impl_pick` stable-core fixture both stopped at structural syntax diagnostics in this experimental CLI. This is evidence about `yu-playground`'s current source path only; it does not establish a language-wide parser or production compiler defect. The first example also depends on the still-unadopted R85 semantic offer.

All six effect-hygiene frontiers remain OPEN. P1–P4, source/native correspondence, parent/evaluator A/B and R50 remain open as recorded in `tasks/agent-loop/current.json`. No source/test code or existing expected output changed during these commands. Cargo emitted existing dead-code/unused warnings.
