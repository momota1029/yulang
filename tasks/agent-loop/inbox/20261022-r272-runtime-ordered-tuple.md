# R272 primary handoff — ordered Tuple runtime construction

Contract: `tasks/agent-loop/sprints/runtime-ordered-tuple-20261022-r272.md`.
Baseline: `9f5abce08`.
Status: implementation checkpoint complete; provisional, primary-only and unreviewed.

Parent: unchanged Yulang2 playground examples plus proof-backed inference/evaluation. R270/R271 retain Tuple children in candidate construction and the source Value graph. R256 identifies the runtime stop. R149 fixes arbitrary finite ordered products and left-to-right evaluation.

The packet implements source Tuple compilation, iterative ordered evaluation, preservation of `ReceivedValue` including views, immutable prefix storage across continuation frame copies, and recursive tuple rendering. Candidate-backed effectful tuple tests resume two ordered children and produce values `(42, 10, 20)`; nested source order and received views also pass. It does not close public types, pattern matching, host output, imports, R149 samples, source/native proof, A/B, soundness, principality, or production.

Checks: `cargo test -p yu-playground --test runtime_resume` (21 passed), `cargo test -p yu-playground --lib tuple` (2 passed), static sprint consistency, and `git diff --check`. Independent review unavailable under the user's solo-work instruction. The exact R149 Types/Console outputs and all parent proof/production gates remain OPEN.
