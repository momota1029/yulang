# R94 closeout — checked declaration identity in focused HIR test

Date: 2026-10-19. Outcome: **FAILED TO ACHIEVE; verification reached a false range assertion**.

## Exact change and command

R94 changed only two lines in crates/yu-hir/src/tests/shadow_method_role_source.rs.
The test now obtains the actual node's key from the same parsed artifact and
uses the public checked ShadowArtifact::source_position lookup to compare it
to the retained declaration position. crates/yu-hir/src/shadow.rs remained
byte-identical to R93's frozen candidate.

The exact single command was:

    CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-hir --lib shadow_method_role_source -- --nocapture

Exit status: 101. Compilation succeeded; 3 tests ran. The two existing tests
passed. The new test failed at line 98 because it asserted that every
constructor-owned receiver range begins with a space. The preceding assertion
that the HIR receiver range equals range_of its paired source node passed for
the reached iteration. R77's historical observed slice ` b` came from its own
different fixed source case and does not justify this stronger assertion for
every receiver. No retry or follow-up edit occurred under R94.

## Frozen evidence and status

- R94 contract: tasks/agent-loop/sprints/associated-member-test-access-20261019-r94.md,
  SHA-256 c0a599899df414d358f9f27d304991790403f2553b520dcb5db3509dc7c88f43.
- Test after its exact two-line access correction:
  9989e108c874d30804bfbe6d2d96d26f3889934dd2104c74f0b161cca0d41e93.
- Frozen R93 implementation shadow.rs:
  9f7a80055076a01cbd99a3eb9c5bc8c3f0db512f2e84032a53af0eacdad2375b.
- R93 proof note:
  6d3a4d0357f99fa9f1b6978bd66d6210409a6e95a1fe046a53239a09f82e012c.
- R93 implementation handoff:
  3c42330197fec74e032f43baba13aaade700709f0049843403205cda077fab80.
- R93 failed closeout:
  c235ca1ad17c45327a2fd98508b2ff1b83a582f803f434090661a0fed65b13b2.

R93's candidate paired-constructor proof and code have not received fresh
independent review. The R94 result is not a semantic counterexample; it does
not accept the source bridge either. A/B remains OPEN 0→0; R50 remains
NOT_ADOPTED; R85 remains AWAITING_USER_ADOPTION. No method dispatch, typing,
RoleId, generated constraints, evaluator behavior or production gate is
established.

The next action requires fresh selector adjudication. Any successor must be a
new bounded contract with the prior R93/R94 budgets still charged, and the
project must rotate back to a distinct effect-hygiene front after this method/
role source prerequisite is either reviewed or explicitly left unfinished.
