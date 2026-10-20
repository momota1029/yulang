# R166 runtime-completion refactor handoff

- Sprint: `native-consumer-lineage-and-runtime-completion-20261020-r166`; contract SHA-256 recorded after freeze.
- Assignment: `R166-RUNTIME-COMPLETION-SEPARATION`, revision 1; Luna primary implementation, prospective only.
- Baseline: proposed `dbdf179986ac80608347dfc72c95d90b5ab9dfb7`.
- Exact code lease proposed: `tools/inference-playground/src/runtime/machine.rs` only.
- Evidence leases proposed: `notes/theory/2026-10-20-r166-completion-simulation.md` and this handoff only.
- Objective: separate schedule traversal exhaustion from the existing selected-definition completion step, preserving all current selected-run transitions and externally observable behavior.
- Preserve: ordered roots, selected cell/cache behavior, fallback initializer evaluation, initialization markers, handler/invocation-owner checks, continuation/resume, requests, values and source provenance.
- Exclusions: changes to `program.rs` schedule/classifier, Case classification, module completion/public API, fabricated DefId/SourceSite/Unit, tests/builds/sample execution, all Yulang2 activity, new language semantics or sample-support claims.
- Proof obligation: state-transition correspondence for schedule exhaustion when selected is cached and when fallback evaluation is required; preserve cache/ownership invariants. Stop if a transition requires new semantic information.
- Budget: proposed 600s primary implementation within R166 2520s total. No code write before CLEAN prospective review and explicit Luna grant.
- Review: independent final source/diff review after freeze; no self-certification.
- Writer stop: prospective; no code change or run currently authorized.
