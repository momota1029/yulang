# R138 Luna source/native owner handoff — revision 1

- Sprint: `helper-cut-ledger-20261020-r138`, contract revision 1, SHA-256
  `8bfe31e038f1c7684ac2d9dba95164f13448e150ccb08a874bea22610fc6e04f`.
- Assignment: `R138-LUNA-CUT-OWNER-MAP`, revision 1. Sole author `/root`;
  current session `current-conversation-2026-10-20-r138`; no descendants.
- Requested primary model/effort gpt-6-luna/high; observed model/effort UNKNOWN.
- Baseline `66c7b52b197aa035d6feaf20ff4f84198a92f9cb`. All 39 direct
  dependency hashes in the frozen contract match both baseline Git blobs and
  live bytes. The 32 current semantic paths repin eight code owners changed
  since R73; their consequences are separately adjudicated in the owner map.
- Exact output `notes/progress/2026-10-20-r138-cut-owner-map.md`, SHA-256
  `7a4c9ab358b6a11df313380bc9ed24e7d78cdabba6d57f94bf21a6402c49b6fd`.
  This inbox is its only other new Luna-owned path.

## Result and parent application

Outcome class: **source/native owner map; partial; no complete cut, no source
reachability proof, no A/B/C result, no code slice.** R73 remains
UNREVIEWED/UNFINISHED. The map rederives current capture, FreshUse and
restoration owners sufficiently to identify constructor distinctions for the
proof lane, but leaves event counts, occurrence IDs, physical multiplicity,
memo state and the full suffix to the proof lane. All original theorem,
Simple-sub A/B, R70/R71, source/native and production gates remain OPEN.

## Current source/native evidence

- `candidate_scheme.rs::route_candidate_local_run` starts the Local route,
  captures the installed scheme, prepares FreshUse and stores a default Local
  cursor. A default cursor does not establish a complete or empty captured
  graph.
- `Capture::bound` iterates the live bound cursor and retains one graph bound
  per attached relation, or the explicit no-relation case; its dedup key
  includes kind, side, endpoints and relation. Evidence snapshots have a
  distinct dedup map; context payload/demand closure can extend the graph.
- `prepare_candidate_fresh_use` freshens only captured local rows whose current
  level exceeds the boundary and whose metadata is generic, reusing a mapped
  row for repeated representatives. This is a constructor rule, not the
  fixed-source instantiated row map.
- `begin_candidate_fresh_bound` creates a transport relation with exact
  `source_bound`, context remap and use origin where the captured bound has a
  relation; it remaps evidence/bundles and then calls physical bound
  restoration. In ordinary mode `candidate_bound_origin_with_evidence`
  follows `candidate_context_bound` for the physical admission. These paths
  must not be collapsed.
- `candidate_begin_bound_restoration` samples the opposite count after
  insertion. Its step owner retires at that saved count, otherwise rereads the
  live canonical owner and indexed opposite endpoint before replay; it advances
  only after the child completion receipt.
- `dispatch_live_item`/`recapture_candidate_extrusion` use the retained typed
  pair, output-indexed group, source qualification, reuse occurrence,
  activation and pending parents, while relation/generation currentness is a
  separate predicate. The later authentic source consumer/provider is still
  unestablished.

## Revalidated R73 code changes and disposition

Eight source hashes changed from R73's baseline. New source derivation is
required; matching current hashes do not certify old claims.

- `module.rs` removes `replace_admission_root`; local root admission needs to
  be traced at current owners.
- `module/local_source.rs` adds Case carriers and changes local body formation
  to check admitted visibility and accept `IndentedStatementBlock`; the fixed
  source contains private `my` declarations and no Case, but its braced nested
  bodies need current CST→HIR formation evidence.
- `candidate_source.rs` and `candidate_value_graph.rs` add Case traversal and
  constraints only for the new Case form; the fixed source has no Case.
- `candidate_scheme.rs` and `candidate_context.rs` deltas are test-gated
  observation fields/bindings, not production transition changes.
- `shadow_apply.rs` only adjusts test construction with `capture_forest`.
- `lib.rs` now performs `component_term_positions.insert` outside
  `debug_assert!`, so the component-position map is populated in release builds;
  `component_endpoint` later requires that map. Rebuild every fixed-source
  component mapping against this current behavior.

## Implementation slice, checks and next owner

Inspected two primary code owners (`candidate_scheme.rs` capture/FreshUse and
`candidate_extrusion.rs` restoration), and cross-checked source scheduling,
relation transport, memo recapture and typed drain owners. No concrete
approved-behavior violation is established. **NO_SAFE_CODE_SLICE.** A
temporary observer/instrumentation remains outside R138 and needs a new exact
primary contract/lease.

Read-only `rg`, `sed`, `git diff` across the pinned history and SHA-256 checks.
No compiler/parser/solver execution, tests, builds, probes, measurements,
instrumentation, source changes, Git integration or external contact in this
lane. CPU/RSS and exact primary active seconds UNKNOWN; 240 seconds was the
maximum grant, not a claim of elapsed work. Proof lane remains active with its
separate 900-second grant and exact outputs.

Next owner: `/root/r138_proof` must consume/reconcile this source map against
its complete event ledger and preserve every missing premise. The paired fresh
compiler/source and spec reviews happen only after both author outputs freeze.
No theorem or production status is promoted.

Writer `/root` stops writing these two leased outputs after Luna review and
freeze; no descendants or unresolved descendant leases.
