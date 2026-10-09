# Review: upper self retention through negative extrusion

Date: 2026-10-10
Reviewed artifact: `upper-self-filter-observer.md`
Artifact SHA-256: `fcec986a1416f06105cf6528d86861a263c823bd60c56565d576f3e960f0f22f`
Baseline: `566310fa8a1076d5e518af3fb50585005194afdc`
Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Reviewer: independent compiler referee

## Result

No blocking, major, or minor finding in the bounded owner-trace scope.

- Negative extrusion records parent metadata, maps a deeper row to a copy,
  inserts the parent-to-copy lower directly, and copies selected-side bounds
  without invoking opposite-bound replay.
- Parent metadata alone is not an SCC edge. Intrusion merges a parent and copy
  only when an actual shared-SCC dependency exists.
- Scheme capture preserves bound sides and restoration compares opposite
  bounds. If both rows are fresh at the same level, the induced relation is an
  upper at the fresh row. If the left row remains an outer anchor, level
  selection can instead store a positive lower at the deeper row.
- The prior Empty-filter observer checks positive lowers; it does not inspect
  copied uppers. The local fixture therefore does not distinguish upper-only
  retention under its stated no-lower hypotheses.
- The artifact keeps the required limits: no admitted source construction,
  original-row scheme reachability, contextual-payload transport, production
  defect, or semantic-retention claim is established.

Inspected: selected hygiene §§1,4,6; concrete annotation implementation gate;
prior discriminator and review; `candidate_extrusion.rs`,
`candidate_intrusion.rs`, `candidate_scheme.rs`, `candidate_effect.rs`, solver
endpoint/canonicalization code, intrusion tests, and Oracle `bounds.rs` around
filter registration and lower insertion.

Frozen hashes matched for the artifact and direct listed dependencies. Oracle
`bounds.rs` hash: `c300c8c0c495da46822e1e1df38b833a6bffe5f3707642ae2cd26910b0608df7`.

Uninspected: original-T reachability from a real source root, formal-row source
admission, contextual carrier implementation, complete termination/rollback,
broader tests, and execution.

## Next gate

Trace an actual negative-extrusion caller and later scheme root to establish
whether the original T and anchored copy C are jointly reachable, then require
the chosen contextual representation to preserve the attachment payload and
make the lower/filter observation. Keep the result conditional until that
source bridge exists.
