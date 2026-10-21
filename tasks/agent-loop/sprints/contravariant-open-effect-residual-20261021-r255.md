# R255 — retain effects from a called contravariant callback

Status: solo test-only result; no independent review. No compiler semantics or
production gate changed.

## Parent and accepted meaning

The unchanged R252 correction is that contravariant `[io]` denotes `[io,'e]`;
a `[state]` callback is accepted. The unified design plan §5.3 additionally
requires a called callback's actual effect to remain in the enclosing result.
R252's CLI regression checked acceptance but did not check this residual.

## Exact scope

- Baseline: `78a0df7b1` on `research/simple-sub-intrusion`.
- Dependency: `notes/theory/2026-10-21-r252-open-effect-tail-correction.md`.
- Leased path: `tools/inference-playground/tests/cli_higher_order_effect_mismatch.rs`.
- Change: only add CLI regression cases; do not alter solver or language behavior.
- Budget: 300 seconds, charged in full, no carryover.

## Evidence

The called callback with actual `[state]` passes a covariant `[state]` result
annotation. The same call conflicts with a covariant `[io]` result annotation.
The existing direct positive mismatch control and unused/called/inline
contravariant acceptance cases remain in the same test. This verifies the
finite CLI examples; it is not a source/native proof or a general effect
soundness result.

`cargo test -p yu-playground --test cli_higher_order_effect_mismatch` passed
(1 integration test). `git diff --check` and `python3
tools/agent_sprint.py check` passed at closeout. Independent review, proof
closure and production remain OPEN.
