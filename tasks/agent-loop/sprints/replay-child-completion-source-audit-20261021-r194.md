# Sprint R194 — Replay child completion and Capture gap audit

Status: CLOSED, primary-only source/native evidence audit; theorem open.
Branch / baseline: `research/simple-sub-intrusion` / `144cd57c231fb9cb4ed811364abdbc3c11998072`.
Authority: unchanged computation-forwarding preservation parent §§1, 6–7. No theorem narrowing, inference transition, or production authorization.

## Purpose and success evidence

Use the R187 bridge/relay fixture and exact current solver source to decide what
the retained source-drain completion receipts prove about Replay children, what
they do not prove about Replay-parent delivery/retirement, and which named
Capture evidence gaps block a full-fiber claim. Apply the result to the exact
missing parent premise. The next output is a source-qualified derivation or an
exact obstruction, not a new observer-only success label.

Success evidence: enumerate source-occurrence origins for Apply 13 and 18;
distinguish direct source drains from Replay-acknowledged child drains; trace the
completion owner and parent delivery owner in current source; decode all
nonzero Capture coverage bits to `CoverageGap`; state whether existing retained
data can establish child drain completion, parent acknowledgement, both, or
neither. A custom offline probe may use only `target/r194-readback/`, removed at
closeout. No source edits.

## Exact inputs and leases

Read pins:

- `candidate_context.rs` `a08ff10637f1ff9a67005f96c5e1bc26a44778f911944054a25cf28bec5ce733`
- `candidate_effect.rs` `c1d7ce19ef5192a46d605faabae34e4437b1f1a15819b5657ec1d70eda7900d1`
- `candidate_scheme.rs` `48094aff85175ef7b30d1ef8be0e8fc42d6e5282d0c4d562c4a730c13d401b25`
- `shadow_apply.rs` `5204a36cf0d2bf45fe74d1d42b60c5e7ab6dd7807104e0f1466acdc9db8c3da4`
- `local_source_observation.rs` `dd2ec5b5b0efb55966e39b54cfcba19b8fc8a6edc33247cf4436f247d403cb38`
- `lib.rs` `24f480355979ee5d96305a08abf6aab67025ede32c2a1575b779e46f5e23b436`
- `candidate_extrusion.rs` `7c9a46d327a5e2e3f9e6f8d79f36f11fe21b4a3f68426526e85424a39e2c6332`
- parent `2026-10-15-computation-forwarding-preservation.md` `d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79`
- R191/R192 local source join and readback contracts/results.

Exact writes: this contract, `current.json`, and new
`notes/theory/2026-10-21-r194-replay-child-completion-audit.md`. Temporary
files only under the named target path. No other dirty file may be edited or
staged. No subagents or independent review under the user's explicit rule.
Budget 600 seconds, one Cargo process, no carryover. Preserve theorem A/B,
source/native correspondence and every production gate as OPEN.

## Outcome

The audit found one completed Replay-acknowledged drain receipt, for unrelated
relation 2 with ack `(61, 0)`. The bridge and relay source views contain no
completed drain receipt for their Replay child relations 59 and 96, and no
durable parent-delivery receipt. The Replay implementation does check child
completion and parent queue/consume state at runtime, but the retained target
view does not join those events; retired idle operations can be removed. The
observed Capture masks are 56 and 120, leaving antecedent, processing
antecedent, ordinary-seed authentication, and (for mask 120) Replay-use
antecedents unavailable. This is an evidence obstruction, not a theorem
counterexample. Full result and source locators:
`notes/theory/2026-10-21-r194-replay-child-completion-audit.md`.

No source semantics changed. No independent review was performed. The
temporary probe under `target/r194-readback/` was removed at closeout. R194
used 300s of its 600s allocation; 300s expired without carryover. Parent
preservation, original A/B claims, source/native correspondence, and
production remain OPEN.
