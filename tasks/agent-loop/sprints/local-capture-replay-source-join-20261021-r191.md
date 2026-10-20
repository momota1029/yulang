# Sprint R191 — local Capture/Replay source join audit

Status: ACTIVE, primary-only read-only source/native audit.
Branch: `research/simple-sub-intrusion`; baseline HEAD `0ed00cea392d7f20c6f54f7ed2dc72415532a65e`.
Parent: `notes/theory/2026-10-15-computation-forwarding-preservation.md` §§1, 6–7; unchanged quantifiers and all OPEN gates.

## Outcome

Continue `R187-OLDER-LOCAL-SAME-USE-1` by determining whether the current
CandidateInference observation APIs can authenticate one local-callee chain
from exact HIR Apply/Name source through local FreshUse/Capture, both Replay
inputs, and the actual completed consumer drain. Use the existing bridge/relay
source from R187. Success is a complete source-keyed readback and a falsifier
for the proposed missing suffix, or an exact owner/field that remains absent.
Never interpret a partial observation, a coverage gap, or a candidate solve as
proof of native preservation.

## Exact inputs and leases

Current-worktree source pins (dirty bytes intentionally included and frozen):

- `crates/yu-solver/src/shadow_apply.rs` — `7c52bbd421de84d57efa7aba13a391b26eb4098a77199895482f720017be2fca`
- `crates/yu-solver/src/candidate_scheme.rs` — `48094aff85175ef7b30d1ef8be0e8fc42d6e5282d0c4d562c4a730c13d401b25`
- `crates/yu-solver/src/candidate_context.rs` — `a08ff10637f1ff9a67005f96c5e1bc26a44778f911944054a25cf28bec5ce733`
- `crates/yu-solver/src/candidate_effect.rs` — `c1d7ce19ef5192a46d605faabae34e4437b1f1a15819b5657ec1d70eda7900d1`
- `crates/yu-solver/src/candidate_source.rs` — `937ce62065be19473fcb37a104f1aaf68e9a9431b8683d8e9a33d221c9e6c26a`
- `crates/yu-solver/src/lib.rs` — `24f480355979ee5d96305a08abf6aab67025ede32c2a1575b779e46f5e23b436`
- R187 candidate proof note — `68caee16ceebc6400829dc3ed8a0ac2aa33f528aa54c8263e085ab47c7ef6e24`
- R187 primary readback — `1f39ea63031edc2325ab7013518f0c7e34fb275b134ebf6b47ba546013b988ae`

Read only those owners and exact existing API dependencies needed for the
bridge/relay occurrence join. Write only this contract, `tasks/agent-loop/inbox/20261021-r191-local-capture-join.md`,
`notes/theory/2026-10-21-r191-local-capture-join.md`, and primary-owned
`tasks/agent-loop/current.json`. No compiler/test edits. A disposable probe, if
needed, is limited to ignored `target/r191-readback/` and must be removed before
closeout. Preserve all other dirty and untracked files.

## Method and boundaries

Audit HIR-owned Apply/callee occurrences against exact source facts/origins;
match the retained local route identity and FreshUse map; trace Capture's
source bounds and coverage; trace both ordered Replay inputs and the owning
completion receipt; identify the actual direct consumer drain. Compare every
map and route under exact source identity, not display text or ordinal alone.
If an existing API cannot expose an owner-authenticated join, record that gap
instead of inventing a crosswalk. No test pass or probe result closes the parent.

Maximum active work: 600 seconds, no carryover; at most one Cargo process. No
subagents. Independent review unavailable under the user's solo-worker
constraint. Parent/A/B/source-native/production remain OPEN absent actual proof
and review.
