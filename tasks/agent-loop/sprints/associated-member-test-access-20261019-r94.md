# R94: use checked public identity lookup in the associated-source test

Status: ACTIVE; one test-access correction only. Revision: 1.
Baseline: R93 frozen implementation and test sources after the failed command.
Branch: `research/simple-sub-intrusion`.
Primary and sole writer: Luna `/root`.

## Fixed outcome

R93's one HIR command stopped at test compilation because the test reached into
private `ShadowArtifact::position_source_keys` and `PositionId.0`. Correct only
that test access. The test already holds the actual `SyntaxNode` and a
same-`ParsedFile` `source_keys` map; use the public checked
`artifact.source_position(key)` and compare its result to the retained
declaration `PositionId`. Preserve the assertion and its exact occurrence
meaning. Do not change visibility or implementation source.

This authorizes one verification command in R94. It is a new, narrowly bounded
successor contract after R93's failed/unmet closeout, not a retry under R93
rev2. A second failure, timeout or compile error stops R94 without repair or
retry. No language semantics, source behavior, expected program output or
diagnostic changes.

## Exact leases and frozen inputs

The only code write lease is:
- `crates/yu-hir/src/tests/shadow_method_role_source.rs`

The primary also owns this contract, `tasks/agent-loop/current.json`, and
`notes/progress/2026-10-19-r94-test-access-verification.md`. The R93
implementation handoff, proof note/handoff, and `crates/yu-hir/src/shadow.rs`
are read-only and frozen.

Exact starting hashes:
- test file: `37cd534fc527ded4d0dcb58b35276e71e9197afdd6330020a349a95047400196`
- `shadow.rs`: `9f7a80055076a01cbd99a3eb9c5bc8c3f0db512f2e84032a53af0eacdad2375b`
- R93 proof note: `6d3a4d0357f99fa9f1b6978bd66d6210409a6e95a1fe046a53239a09f82e012c`
- R93 implementation handoff: `3c42330197fec74e032f43baba13aaade700709f0049843403205cda077fab80`
- R93 failed closeout: hash to be pinned at activation.

The permitted source delta is exactly the two private-field access lines in
`association_bridge_uses_constructor_owned_receiver_and_parse_owned_declarations`.
Replace them with the public checked source-key lookup, preserving the
same-position equality assertion. No production or other test file changes.

## Verification and independent review

After the two-line delta is frozen, Luna may run exactly once:

`CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-hir --lib shadow_method_role_source -- --nocapture`

No additional command that builds/tests/probes the compiler is authorized.
Fresh independent compiler/source review and fresh spec review each have 180
seconds and receive the frozen R93 implementation/proof, R93 failure receipt,
R94 test diff and exact verification receipt. The compiler reviewer checks the
public source-key round trip and that `shadow.rs` did not change. The spec
reviewer checks the assertion was not weakened, all original semantic gates
remain unchanged, and any pass supports only the bounded source bridge.

Fresh cap: 780 seconds total: Luna edit 180, one verification 120, compiler
review 180, spec review 180, integration 120; Astra 0. R93 time remains
charged/unknown and is not refunded, reset or renewed. This R94 cap authorizes
only these exact tasks; no source-semantic implementation follows.

## Falsifiers and closeout

Falsifiers: source key resolves to a foreign/different retained position; the
assertion disappears or is weakened; `shadow.rs` changes; the single command
does not pass; fresh review finds a blocking/major issue. A failed verification
stops R94. Successful command and clean independent reviews may accept only
the narrow source-correspondence prerequisite; they do not prove dispatch,
typing, RoleId, evaluator correspondence, A/B, R50 or production readiness.

After review, close R94 with exact hashes and receipts. Then consult the sprint
selector and return to a distinct effect-hygiene evidence slice while retaining
the R92 runnable source example and all six frontiers in current state.
