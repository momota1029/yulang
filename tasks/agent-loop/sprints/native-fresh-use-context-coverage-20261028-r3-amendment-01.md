# Amendment 01 — NATIVE-FRESH-USE-CONTEXT-COVERAGE/r3

Status: admitted by Luna through `tasks/agent-loop/current.json`; this amendment changes only one read-only source dependency. Base contract SHA-256: `d6fc97fde87e8c8a0c0eb0cb8afb140029a0428aedcde6f82b1f162c4bc21725`.

## Exact delta

Admit `crates/yu-solver/src/candidate_extrusion.rs` from the clean r3 archive of baseline `bc2a0836ec8fc9dee6a1094552a3dd34cfbcfd0d` as a read-only dependency, SHA-256 `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61`. Scope is limited to the restoration driver around the previously identified locations near lines 966 and 988, and only as needed to decide whether restoration can change the `relation_context` root between preparation and completed-bound admission.

The primary verified that the archived r3 copy and current source both match this hash before admission. The exact path is leased read-only to `/root/native_fresh_use_context_coverage_proof_r3`; the proof lane must acknowledge this amendment hash before reading it. No other new owner or dependency is admitted.

## Preserved limits

The original r3 outcome and all other contract terms remain unchanged: no API or production change; no source-semantic claim; no full FreshUse validator, returned-root theorem, parent closure or production promotion; no `H_u` authority. Rust/proof/reviewer/primary resource allocations and execution caps are unchanged, with no carryover or renewal. The new read consumes the proof lane's existing 1,000-second grant. No Cargo/test/build or Lean/Lake invocation is authorized before fresh review acceptance. All original output leases remain unchanged. If the driver reveals a concrete unstable successful route, report that exact counterexample; otherwise state precisely which restoration property remains unproved. Do not infer global stability from a finite trace.
