# Sprint R192 — local provider readback API

Status: CLOSED, primary-only provisional observation tooling.
Branch: `research/simple-sub-intrusion`; baseline HEAD `07a13ae99d954508b40ca41a74e1693ad7bae123`.
Authority: continue the unchanged source/native parent. Add read-only research observation only; no solver transition, inference semantics, or production authorization.

## Outcome

Add a typed `CandidateInference` readback for an exact local-callee Apply. It
must bind the HIR Apply/callee/local identity to exactly one retained local
FreshUse route and return the retained Capture/map rows plus the source Apply's
ordered Replay dependencies when present. Completeness is explicit: caps,
missing direct source joins, nonzero Capture coverage gaps, and the absence of a
Replay-child completion receipt must remain visible and must never report a
complete preservation certificate. Exercise it against the R187 bridge/relay
source through a temporary readback and inspect the exact rows.

## Exact inputs and leases

Read pins:

- `crates/yu-solver/src/shadow_apply.rs` — `7c52bbd421de84d57efa7aba13a391b26eb4098a77199895482f720017be2fca`
- `crates/yu-solver/src/candidate_scheme.rs` — `48094aff85175ef7b30d1ef8be0e8fc42d6e5282d0c4d562c4a730c13d401b25`
- `crates/yu-solver/src/candidate_context.rs` — `a08ff10637f1ff9a67005f96c5e1bc26a44778f911944054a25cf28bec5ce733`
- `crates/yu-solver/src/candidate_effect.rs` — `c1d7ce19ef5192a46d605faabae34e4437b1f1a15819b5657ec1d70eda7900d1`
- `crates/yu-solver/src/candidate_source.rs` — `937ce62065be19473fcb37a104f1aaf68e9a9431b8683d8e9a33d221c9e6c26a`
- `crates/yu-solver/src/lib.rs` — `24f480355979ee5d96305a08abf6aab67025ede32c2a1575b779e46f5e23b436`
- R191 local readback — `9655bf0041f69e080604703a3d4d11823f63c52307ec6e096679e45965fe2fd2`

Write only this contract, `crates/yu-solver/src/shadow_apply.rs` (two module
declaration/re-export lines; preserve all existing dirty hunks), new
`crates/yu-solver/src/shadow_apply/local_source_observation.rs`, and
`tasks/agent-loop/current.json`. Temporary readback files may use only ignored
`target/r192-readback/` and must be removed at closeout. No solver tests or
other dirty source files are in scope.

## Checks and limits

Compile the solver package and run a single offline custom readback against the
frozen R187 source. Require exact Apply/callee/local identity, one route, all
Capture/map rows under no truncation, both ordered Replay inputs when the source
relation is a Replay parent, and `preservation_complete == false` when coverage
gaps or missing completion receipts remain. This API is structural evidence,
not proof. Maximum active work: 600 seconds; at most one Cargo process; no
carryover. No subagents or independent reviewer. Parent/A/B/source-native/
production remain OPEN.

## Closeout

`RUSTC_WRAPPER= cargo check -q -p yu-solver` passed. One offline readback through
`target/r192-readback/` selected bridge Apply 13 / callee 14 / local 0 / graph
0 route 0 / context use 1 and relay Apply 18 / callee 19 / local 1 / graph 0
route 1 / context use 2. Both had complete source fact/origin lists, no
observation truncation, one direct source relation and one retained Replay edge
with the expected ordered inputs (bridge child 59, parents 55/58; relay child
96, parents 92/95). The actual Origin indices are 33 and 48. The routes returned
12 and 24 Capture/map rows. Their snapshot coverage gaps remain 56 for bridge
and 56 (last row 120) for relay. No Replay-child completion receipt is exposed;
`preservation_complete` remained false for both.

The temporary target probe was removed. This readback is structural evidence;
it is not a preservation proof, counterexample certification or production
authorization. Parent/A/B/source-native/production remain OPEN. Primary-only
closeout; no independent reviewer was available.
