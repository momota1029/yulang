# R255 result — called callback effect remains in the result

Status: solo test-only result; unreviewed. R252's corrected language meaning
and all source/native and production gates remain unchanged and open.

## Parent correction

The user clarified that a contravariant `[io]` annotation means `[io,'e]`; an
actual `[state]` callback does not violate it. The repository's unified design
plan, `docs/yulang-unified-design-and-proof-plan-ja.pdf` and `.docx`, §5.3,
also requires the effect of a callback that is actually called to appear in the
enclosing result. R252 covered acceptance but not that residual check.

## Regression added

`tools/inference-playground/tests/cli_higher_order_effect_mismatch.rs` now
checks both sides through the ordinary playground CLI:

- `accept (f: int -> [io] int) = f 0` accepts a `[state]` callback when the
  enclosing result is annotated `[state] int`.
- The same call conflicts when the enclosing result is annotated `[io] int`,
  showing that the open tail does not erase the callback's actual effect.
- R252's direct positive mismatch control and unused/called/inline negative
  formal acceptance cases remain intact.

The focused command passed:
`cargo test -p yu-playground --test cli_higher_order_effect_mismatch`
(one integration test). This is finite CLI evidence, not a source/native proof,
runtime trace, effect soundness theorem, or independent review. `git diff
--check` and `python3 tools/agent_sprint.py check` also passed; the latter is
static consistency evidence only.

## Frozen scope and remaining work

Contract: `tasks/agent-loop/sprints/contravariant-open-effect-residual-20261021-r255.md`.
Baseline commit: `78a0df7b1`. Only the CLI regression file was changed; no
compiler or language semantics changed. The solo author performed no
independent review. Parent proof, full ordinary test coverage, Y2 sample
execution, and production admission remain open.
