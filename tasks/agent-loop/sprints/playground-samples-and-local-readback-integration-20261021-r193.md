# Sprint R193 — playground sample and local-readback integration

Status: CLOSED, primary-only repair and ordinary-test validation.
Branch / baseline: `research/simple-sub-intrusion` / `bd32348cb41ee3e75dfeda396f4ec0639d06f156`.
Authority: preserve current Yulang2 sample behavior and R192's read-only evidence boundary. No inference semantic change or production proof claim.

## Outcome and evidence

Fix the feature-enabled compile issue exposed by the ordinary playground suite,
then verify all files under `web/playground/examples/` used by the Web selector
have ordinary `yu-playground` test coverage. Preserve exact sample bytes and
the user's uncommitted neighboring edits.

Success evidence:

- `cargo test -q -p yu-playground` passes with the candidate feature enabled.
- `cli_demo_identity` covers `yulang2-identity-island.yu` at int/bool/string.
- `cli_ordinary_islands` covers `yulang2-ordinary-islands.yu` at four definitions.
- `cli_yulang2_diagnostic_examples` covers both intentional failure samples.
- `cli_repeated_choice` and `cli_polymorphic_escaping_closure` cover the remaining two execution samples.
- The local readback's bounded reservation handles its optional single graph.

The run first exposed `candidate_graph` as `Option<GraphState>` where the new
observer tried to call `len`; the bounded source-relation vector needs capacity
for at most one retained graph. Replacing that estimate with `try_reserve(1)`
made the complete playground suite pass. The first default-feature solver check
did not compile this feature-gated module and is not treated as sufficient.

## Scope and limits

Exact write paths: this contract, `tasks/agent-loop/current.json`, and
`crates/yu-solver/src/shadow_apply/local_source_observation.rs`. Read-only sample
and test paths are the six Web fixtures above and their six integration tests.
No sample or test source changes are part of this sprint. No subagents or
independent review; the user explicitly requires solo work. Temporary files are
not needed. Maximum envelope 600 seconds, no carryover, one Cargo process.

The ordinary suite is executable evidence for the checked fixtures, not a proof
of inference preservation. Parent/A/B/source-native/production gates remain
OPEN. Next step after closeout: continue the unchanged parent proof at the
missing Replay completion and complete Capture-fiber coverage owners.

## Closeout

`RUSTC_WRAPPER= cargo test -q -p yu-playground` passed across the package after
the `Option<GraphState>` reservation fix. The six Web fixtures were matched to
their existing ordinary integration tests as listed above; no test or sample
bytes needed edits. No R193 scratch files remain. This is ordinary execution
evidence only. Replay completion and Capture-fiber preservation, the parent
theorem, A/B, source/native correspondence and production remain OPEN. Solo
primary; no independent review.
