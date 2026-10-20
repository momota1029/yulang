# R167 whole-module runtime implementation handoff

- Sprint: `source-authenticated-module-run-20261020-r167`; contract SHA-256 recorded on freeze.
- Assignment: `R167-WHOLE-MODULE-RUN`, revision 2; Luna primary, proposed only, no code lease. Revision 1 remains preserved in commit `148666e52`; its review found a shared proof/implementation evidence path, corrected here.
- Baseline proposed: `fa5fd3a0fb055226875534754646e81e921fa557`.
- Proposed code paths: `tools/inference-playground/src/runtime/program.rs`, `runtime/machine.rs`, `runtime/mod.rs`, `tools/inference-playground/src/lib.rs`.
- Proposed evidence: `notes/theory/2026-10-20-r167-module-runtime-simulation.md` and this handoff only.
- Objective: implement the R149-authorized whole-module entrypoint consuming the proof-reviewed complete ordered schedule and returning an honest module-level completion without selected/fabricated DefId or SourceSite; preserve selected-definition behavior and lazy cached values.
- Activation condition: proof lane establishes applicable source-owned classification for every constructor used by the new entrypoint. Missing law means stop before enabling module mode; no plumbing-only substitute.
- Exclusions: imports/stdlib, tuples, roles, primitives, host writes, CLI/Web changes, tests/builds/sample execution, all Yulang2 activity and sample compatibility claims.
- Review: fresh independent code/source correspondence review after freeze; Luna cannot self-certify.
- Budget: proposed 1200s within 3600s; no carryover/descendants.
- Writer state: proposed only; no code edit or run authorized until CLEAN prospective review and exact grant.
