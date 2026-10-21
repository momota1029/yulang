# R225 — Apply/LocalFreshRoute design-debt audit

Status: CLOSED_DESIGN_DEBT_AUDIT; Luna solo primary, no subagents.
Baseline: `031ad45f6` on `research/simple-sub-intrusion`.
Parent: original computation-forwarding preservation theorem; R71 and R72 remain OPEN.

## Why this boundary

R221-R224 used four distinct views (WorkBound, source-call facts, LocalFreshRoute rows, and retained route terms) and repeatedly stopped at the actual-provider to callback-formal edge. Per `rules/compiler-engineering.md`, pause proof variants and classify the missing premise as A/B/C/D before trying another reconstruction. R224 found source route terms Term(413) and Term(386), provider Apply argument Term(452), no actual-route-to-argument fact/function path, and a callback-to-formal path only through generic IntNegative Term(1) and FactId(44).

## Audit question

At the existing source Apply owner, solver Apply consumer, and LocalFreshUse commit owner, determine which phase already knows the source argument identity, actual typed endpoint, route term map, and relation/use context. Inspect `RetainedFreshUseMaps.scoped_relations`, `context_remap`, `terms`, route source/use owner, slot-4 relation, and callback WorkBound lineage for exact joins. Classify the missing theorem premise A/B/C/D under the authoritative inference design and proof-obligation-economy rules. Decide whether the current gap is (1) semantic/algorithmic, (2) a required ordinary-inference behavior, or (3) reconstruction debt caused by a known owner fact not being retained. Do not add a production relation, public API, language rule, or theorem premise in this audit.

A valid result identifies the first missing owner-side fact and a falsifier for the classification. Equal IDs, shared generic leaves, accepted solve, and test success are not a bridge.

## Exact paths and checks

- `crates/yu-solver/src/candidate_scheme.rs`
- this contract
- `notes/theory/2026-10-21-r225-apply-local-route-design-debt-audit.md`
- `tasks/agent-loop/current.json`

Use ordinary candidate mode and the exact R221 source. Run one focused R225 test and `cargo test -p yu-playground` if interpretable. Finish with sprint check, 57 tooling tests, `git diff --check`, serialized state limit, exact-path commit and push. 600 seconds, no carryover. Solo primary; no independent review claimed. Preserve R71/R72 and the parent theorem as OPEN.

## Outcome

R225 found a provider Apply-to-expected-function comparison and the slot-4 result-effect edge, then isolated the first missing owner fact: callback formal registration is absent from the source-origin relation used for later route reconstruction. Classified as D reconstruction debt. See `notes/theory/2026-10-21-r225-apply-local-route-design-debt-audit.md` for the owner-qualified evidence and falsifier. No production behavior changed; R71, R72, and the parent theorem remain OPEN.
