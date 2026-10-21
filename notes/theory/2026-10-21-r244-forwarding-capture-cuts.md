# R244 — Forwarding capture across cuts

Status: active read-only proof/source audit. Parent, R71/R72 and production remain OPEN.

## Fixed goal

Continue the unchanged parent theorem in `notes/theory/2026-10-15-computation-forwarding-preservation.md` §§1, 6–7. R243 establishes one conditional equal-age Local edge only. This audit asks whether required edges survive arbitrary local/shared-anchor cuts, with R187's mixed-age bridge/relay as the discriminator. Preserve original assignments, formals, arbitrary finite chains, repeated calls, simultaneous entries and finite-prefix quantifiers.

## Dispatcher boundary

R243 was frozen as an unreviewed one-edge result. The next parent-critical outcome is a cut invariant: each source-required edge is either captured/restored in the local region or preserved via an unchanged shared endpoint under the actual use map. The key missing transition is from the enclosing Function's reached ports through intermediate Apply-effect rows `c_u,q_u` when bridge ports are older shared rows. Check both forward discovery and reverse discovery from the completed Lambda return-effect origin, then trace the physical owner for each edge through Local routing.

Completion receipt retention is not a theorem premise. `record_source_drain_completion` intentionally drops the completion record if `try_reserve` fails to preserve successful inference. Reverse discovery consults retained completion receipts. Establish that needed edges survive when this evidence is absent, or record an exact obstruction without restricting the parent to receipt-retaining runs.

## Source observations in progress

`Capture::expand_row` in `candidate_scheme.rs` returns immediately for non-local rows, leaving their mutable bounds in the session; this is the shared-anchor behavior to verify against each mapped edge. Local effect rows expand through capture incidence, direct lower/upper rows, exact non-variable bounds, and, for shape rows above a positive boundary, incoming effect upper owners. Capture runs to a fixed point over pending endpoints/rows and newly discovered bounds. This alone does not prove a particular source edge is in a captured region or remains licensed at a shared endpoint.

`candidate_context.rs::record_source_drain_completion` returns silently when reservation fails; `source_drain_completed` checks for the cloned receipt marked completed. Capture builds `completed_lambda_effect_origins` from origins whose receipt is present and completed. Remaining work: trace how these origins seed reverse discovery, whether another route supplies the edge, and how `LocalFreshRoute` remaps captured rows/evidence when an endpoint is shared.

## Result and limits

No cut theorem or R187 adjudication yet. R243's equal-age derivation does not cover older shared bridge ports. A valid falsifier must identify an exact source-required bound, its physical owner, the cut, and why neither local capture nor shared-anchor preservation admits it. A missing completion receipt is only a failure of the proposed argument unless source-derived reachability actually depends on it. No code, tests, builds or samples changed or ran. Fresh independent review remains required.

## R244 result: exact receipt-loss cut obstruction

The current source confirms that reverse-owner discovery repairs the ordinary R187-shaped cut when completion is retained. `candidate_apply_effect` canonicalizes both endpoints; for an equal-level row bound `a <= b`, `effect_levels[b] <= effect_levels[a]` selects physical owner `a`, negative polarity, item `b`. The only physical edge is therefore in `a.direct_upper_rows`; it is not mirrored into `b.direct_lower_rows` (`candidate_extrusion.rs`, `candidate_insert_bound_with_evidence`). R217's frozen readback identifies the actual R187 witness as `Effect(10), Negative, Effect(31)`, physically owned by row 10, with relation lineage to Lambda slot 4. R217's Capture route contains this edge when the completed-origin receipt is present.

For a positive-boundary local Capture whose Function shape reaches the upper row 31, `Capture::expand_row(31)` can recover owner 10 only through `ensure_incoming_effect_upper_owners`. That index requires all three conditions: row 31 is local, it was reached from the captured type shape, and the row-10-to-31 negative bound carries a relation among `completed_lambda_effect_origins`. The ordinary one-sided storage leaves no direct-lower entry on row 31 to recover the edge by normal expansion.

The completion path makes the third condition fallible without failing inference. At typed-drain return, `record_source_drain_completion` calls `source_drain_completions.try_reserve(1)` and returns immediately on error. The caller then pops the completed drain and returns its successful transition count. The Lambda Origin still carries its receipt, but `source_drain_completed(receipt)` is false because the completed receipt was not retained. Consequently Capture excludes that slot-4 relation from `completed_lambda_effect_origins`; the reverse-owner index omits `(31,10)`. In the R187 physical cut, row 10 is not otherwise reached from the Function's reached ports, and row 31's one-sided adjacency has no reciprocal route. The source-required slot-4 edge is therefore absent from the captured local graph despite successful inference.

This is an exact obstruction to a theorem that every successful inference has the needed local Capture edge across this cut. It does not refute the language-level forwarding theorem: it identifies missing implementation evidence in one source-to-Capture path. R243's conditional equal-age Local composition and R217's receipt-retaining repair remain valid within their stated premises. An unchanged shared upper row is a different case: it need not be copied into the local graph, and can remain live through its shared identity. This result covers the R187-shaped local upper cut when its completion evidence is lost; it proves no arbitrary-chain, all-cut, R71/R72 or production closure.

## Frozen inputs and limits

The R187 source-derived candidate and R217 readback are evidence inputs, not fresh independent reviews. R217 contract SHA-256 `708528fa574d87319a9bb2ca6003f54e0b5b5cda777da19c15566453c2cfce69`; R217 result SHA-256 `d3600a814f9130fe887675af1b41a3ac157628fad8a25cf49118d67dd8cc0e0f`. R216 correction SHA-256 `ebb6fe85efc12322136c33f112c7cc6f0ef1ddfc352ce15f44c63bc6408114fc` confirms the one-sided physical owner. Current dependency pins are in the R244 contract.

No allocation fault was executed in R244. The failure case follows from the checked source branch and the known R187/R217 physical witness; it is a source-derived conditional obstruction, not a measured runtime failure. No code, tests, builds or samples changed or ran. Remedy requires a separate authorized implementation decision; R244 grants none. Parent, R71/R72, independent review and production remain OPEN.
