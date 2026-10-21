# R253 — native ordered tuple terms and comparison

Status: ACTIVE; Luna primary working solo. No delegated workers or active external writers.
Branch / baseline: `research/simple-sub-intrusion` / `5596b1598`.
Authority: R149 unchanged Yulang2 sample semantics; R168 §§3–6 construction relation and M5–M7 consumer obligations; R251 ordered source carrier.
Contract revision: 1. Resource envelope: 1200 seconds, no carryover.

## Original outcome and success evidence

The unchanged Yulang2 Types and Console samples must infer, display, and execute according to R149. This packet advances the Types path by giving the native solver a distinct arbitrary-arity ordered Tuple term and a correct live comparison rule. It does not close source/native proof, public closed-type export, runtime, or either sample.

R168 relation: positive Tuple children retain their original order and duplicates; `Tuple+(a[0..m)) <: Tuple-(b[0..n))` first requires `m=n`, then enqueues every indexed `a[i] <: b[i]`. Tuple child positions are covariant; Function polarity remains governed by existing Function ports. Tuple/other and unequal-arity comparisons report incompatible shape. No pair encoding, zip truncation, first-child projection, or silent fallback.

Success evidence: unit coverage for arities 1–3; zero-length Tuple remains distinct from Unit and is rejected, order/duplicate preservation, positive/negative polarity validation, interning, equal-arity per-position propagation, unequal arity, and Tuple/primitive or Tuple/Function mismatch; ordinary solver checks pass. Source construction remains explicitly deferred until the native child and resource protocol is verified.

## Open premises and boundaries

- R168-SOURCE-ARITY-1 mapping: R251 selected `()` Unit, `(x)` Group, `(x,)` singleton Tuple, and multiple real direct children Tuple; semicolon/recovery refused. This is source mapping evidence, not independent semantic review.
- R168-NATIVE-POSITION-1 remains OPEN across candidate source, extrusion/capture/scheme, closed types, and runtime.
- No production or public sample-support claim follows from native term tests.
- Independent review is absent; all proof, source/native and production gates remain OPEN.

## Work envelope

Exact writes: `crates/yu-solver/src/term.rs`, `crates/yu-solver/src/lib.rs`, `crates/yu-solver/src/shadow_apply.rs`, `tasks/agent-loop/current.json`, this contract, and `notes/theory/2026-10-21-r253-native-ordered-tuples.md`.
No other file is authorized without a primary scope update. Existing frozen review bytes remain unchanged; primary re-leases the listed solver owners for this new packet. No user sample or expectation edits.

Proof method: constructor/dispatch case analysis against R168 M5–M7, with arity/order falsifiers and parent application recorded in the result note. Implementation: TermView/TermNode native tuple, checked child ownership/polarity and retained storage, endpoint identity, exact arity gate, all indexed constraints. Preserve rollback, memo, diagnostics and resource accounting. Do not use unaccounted nested vectors or clone-only retained-byte estimates.

Checks: focused solver tests and `cargo test -p yu-solver --lib`; compare formatter output against HEAD drift; `git diff --check`; sprint checker. At most one heavy Cargo process. Stop on the first resource/accounting invariant that cannot be made exact; report the concrete blocker and continue on another authorized Types/Console path in a later packet.

Git: Luna alone stages explicit paths, commits and pushes after checks; keep the worktree clean. This result is unreviewed and cannot close R149 or any production gate.
