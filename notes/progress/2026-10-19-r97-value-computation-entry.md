# R97 closeout: finite §21 Value/Computation entry matrix

R97 adds one six-cell test to `tools/inference-playground/tests/runtime_control.rs`. The cases cross the formal shapes `x`, `(x:int)`, `(x:[] int)` with an effectful `signal::ping()` argument and a pure recursive `loop ()` argument. Existing helpers, tests, assertions and names remain byte unchanged. The test invokes the ordinary `machine()` helper and makes no special path around parse, LocalSource, CandidateInference or RuntimeProgram construction.

The single authorized command passed once:

`CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-playground --test runtime_control section21_outer_annotation_selects_entry_for_ignored_arguments -- --exact --nocapture`

Result: exit 0; one test passed, 12 filtered. All six assertions were reached. The implicit and `int` Value formals exposed the request and exhausted finite fuel for the recursive input. The `[] int` Computation formal returned `9` for both inputs, including the effectful ping case. That last cell passing shows candidate preparation accepted that exact fixture. It is evidence about this candidate path; it does not establish a general effect compatibility rule. Finite fuel exhaustion is not a divergence theorem.

A fresh pre-edit and post-freeze spec reviewer was CLEAN. A fresh compiler/source reviewer was CLEAN for finite source/runtime correspondence with no blocking or major findings. The reviewer recorded one minor documentation inconsistency in the implementation handoff: an earlier generic sentence says no Git command ran, while a later explicit deviation reports one pre-edit read-only `git status --short`. The latter is the accurate receipt. There was no mutation and no post-edit Git. This procedural deviation is preserved, not hidden.

The implementation handoff hash changed after the proof note's original handoff pin, from `247e66658fbf616046e4e41442f85e280213e23af508aa17f82db0e9acfbe4f3` to final `b6d9b8206ca433839ab48b9822f8546bf89d40099a2e8e763da1cb6d210ec39d`, solely to disclose that deviation. The proof/test bytes did not change; the spec review assessed both snapshot identities. Current state pins the final handoff. The post-delta spec receipt also has its own final hash recorded in current state.

This result supplies only a finite ordinary-entry correspondence. It can support method/role work only when a future method path preserves the authentic executable binder, annotation, whole-argument label and same receiver invocation. It does not prove member production, method typing, lookup, dispatch, role-call compatibility, full §21, effects soundness, original Simple-sub/evaluator quantifiers, A/B, R50/R85 adoption or production promotion.

## Breadth ledger

R97 advances the **§21 Value/Computation entry** front. The five other effect-hygiene fronts remain independent and open: ordered handler priority; wrong/sibling permission; unmatched outward request plus suspended suffix; continuation capture/resumption; static-to-runtime projection. R96's sibling owner/view comparison and R95's method/role source identity bridge remain bounded candidates. R92's runnable effectful program remains separately verified to CLI stdout `23`.

## Frozen evidence

- R97 contract: `2a9e65fd973e4d9c7f0916440fe8438eb6e9a8b8cd7969dc8f89025d9cf1b1ce`
- test: `2619e4c8bb006e2d98cf81887091ae372cb1ae3731de76e7b707a97db577009c`
- proof: `77b4ea777a2fd413b356b5128cc55362f1126e6298bcb7c310f776cfd53b4b98`
- proof handoff: `6a84958c082f6ec9575cb13962ad395c4246a5e7636df6921429399503eabdfb`
- implementation handoff: `b6d9b8206ca433839ab48b9822f8546bf89d40099a2e8e763da1cb6d210ec39d`
- compiler/source review transcript: `tasks/agent-loop/inbox/20261019-r97-compiler-review.md`
