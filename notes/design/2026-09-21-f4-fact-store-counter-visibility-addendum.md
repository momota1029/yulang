# F4 fact-store counter visibility addendum

Status: Authoritative
Scope: public visibility of the F4 fact-store rebuild counter
Approved-by: user
Approved-at: 2026-09-21
Drafted-by: primary agent
Reviewed-by: spec_auditor, performance_auditor
Supersedes: only the ambiguous interaction between F4 §12's exact public accessor list and §13's per-container rebuild accounting

## Decision

`fact_store_rebuilds` remains an internal accounting lane. It is not a public
`ProductionCounters` accessor.

The internal lane still contributes to the public aggregate
`constraint_store_rebuilds` together with canonical-map, provenance, and
consumed-receipt rebuilds. Tests may inspect the internal lane from the owning
module, but public scale evidence uses the aggregate accessor and the exact
public list approved by F4 §12–§13.

This preserves per-container measurement without expanding the public API.
No other counter visibility, formula, resource contract, or F4 semantic rule
changes.
