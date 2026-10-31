# R89 manifest amendment 01 — immutable birth qualification supplier

Sprint: EFFECT-PERMISSION-APP-DEMAND-INCIDENCE/20261101-R89
Prior manifest: tasks/agent-loop/sprints/effect-permission-app-demand-incidence-20261101-r89-inputs.json (sha256 86727cb01dc42a4b51148e1dff9c75a4f37af01c7862a56afa18eed25ca2a256, revision 1, 33 inputs)
Amended manifest: tasks/agent-loop/sprints/effect-permission-app-demand-incidence-20261101-r89-inputs-r2.json (sha256 6fe8973a6b5e1aa55d73bb47c85cf4bb11b9a57e1a8b034a167197e7f8697dfa, revision 2, 34 inputs)

## Dependency decision

The source mapper found that source-side birth recording calls candidate_value_graph::Graph::qualifies, which was outside revision 1. The mapper has not opened this file. The lightweight sprint dispatcher recommends admitting this exact read-only dependency because R89 already asks for the actual immutable birth-qualification correspondence. Naming the method without inspecting the implementation would leave available primary evidence unexamined.

Added input: crates/yu-solver/src/candidate_value_graph.rs, 54389 bytes, sha256 aaaa88a374083f898188cd390b8cf0244855d8c09c8939b9e68ee2831bc692cf.

Authorized read scope is limited to Graph::qualifies and in-file helpers; construction/retention of birth levels, Value identities and reference edges; whether reachability stays inside the equal-birth induced graph required by the pinned 2026-10-24 decision; and the connection from its arguments to the actual App-demand occurrence. No semantic conclusion may be inferred from the method name or returned Boolean. Tests, builds, edits, external dependencies, worktrees, environments, scratch and cache are not authorized.

The existing source assignment continues under its original 1,000-second lane budget. The incremental read of this new dependency is capped at 300 seconds from that remaining grant; this is not a budget reset or new assignment. If it cannot be completed within the cap, record the dependency as OPEN without expanding scope.

## Current-state compaction

Removed the `/root/r48_review` worker row from `current.json`; it was STOPPED and owned no lease. Its stopped status is preserved here. Kept the R89 proof worker STOPPED with required model/effort facts and frozen candidate/handoff leases. Shortened generic UNKNOWN/quarantine receipts and compacted the open-item text without changing any worker observation or lease. The current file is 16,378 bytes and passes the 16 KiB checker limit.
