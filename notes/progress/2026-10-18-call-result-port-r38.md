# R38 implementation — ordinary Call result port

Assignment `R38-IMPLEMENT-PORT-CORRESPONDENCE`, contract revision 2
(`tasks/agent-loop/sprints/ordinary-call-result-owner-20261018-r38-rev2.md`,
SHA-256 `f119bf4f031ab8b28fd060921723ddb235bf208ff3b48a87bc169aa1b7fa0421`).
Baseline: `887eed4370278cd9e789fb2b9b10ff58369da540`.

## Outcome

Added one test in the existing `shadow_apply.rs` test module for the recursive
source Apply `loop y`. It executes candidate constraint construction and
propagation, then checks that the retained source occurrence identifies the
actual Apply, `NativeInterface.result` projects to the original
`ApplySourceInput.result` component, and the negative Function demand has
exactly `(argument, argument effect, invocation effect, result)` as its four
ordered children. It checks that the source observer rejects a substituted
occurrence, application effect in the invocation-effect slot, another Apply's
body-result endpoint, and the callee endpoint in the result slot.

The test leaves `PendingCallSupplier::OriginalGenCall0` and the existing
unresolved premises visible. It creates no complete logical result-description
owner, dependent telescope, returned-provider/world object, or typed source
rule. The source synthesis A choice remains authoritative: this test observes
the expression body's Apply result and does not recast an inert returned
computation value as that result or infer a port from a solved effect row.
This is candidate source-to-native port evidence only; it closes no theorem
condition and approves no semantics or production cutover. `NativeInterface`
has no separate returned-provider/world field, so the callee-endpoint
substitution is only a negative control against endpoint conflation, not a
proof about provider identity.

## Evidence reused and rejected

- Reused `shadow_apply.rs::admit_candidate_fact`: it authenticates recipe/source
  incidence, allocates the invocation effect, constructs the negative Function
  demand, retains `NativeInterface`, admits the constraint and propagates it
  through `InferenceSession::execute()`.
- Reused `candidate_call::observe` as the source-owner validator. Its checks
  retain the source Apply and checking occurrence and validate native ports.
  The test observes the still-pending original `Gen-Call-0` supplier.
- Adapted the endpoint assertion in the broader, unmodified
  `candidate_context_tests.rs` owner audit into one focused test.
- Rejected the inference that a valid native port tuple supplies the original
  rule's scope or complete telescope. R37 rev3 closeout records the same parent
  gap and `0 -> 0` theorem-condition count; its candidate was unexecuted and
  both independent reviews were BLOCKED.
- No withdrawn Simple-sub bypass or expected-output change was restored.

## Exact artifact and checks

- `crates/yu-solver/src/shadow_apply.rs` SHA-256:
  `d5e6b179fd4f6fbca579b0fa4d479d8bd11b520d774acbf27f414451c4691137`.
- `crates/yu-solver/src/candidate_call.rs` unchanged at its dependency hash
  `e038ad0dfc4b12bd0d513d6cd6b2b062d8b33368bc1c0dcdef980d479`.
- `git diff --check -- crates/yu-solver/src/shadow_apply.rs`: passed.
- No Cargo, build, test, probe or formatter ran under the assignment boundary.
  The new Rust test is unexecuted and needs review before a verification launch.
- Direct dependencies matched their pinned hashes: baseline
  `shadow_apply.rs` `5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb`;
  Call definition `20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c`;
  Generalize proof `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`;
  synthesis A `71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992`;
  inference principles `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`.

## Remaining premise and next in-envelope step

The proof lane must identify the original ordinary Call result owner and all
ordered dependencies for `q = loop y`; this test does not close that premise.
A fresh compiler review should check source occurrence, result endpoint and
four-port correspondence on frozen bytes. After applicable clean reviews, Luna
alone can decide whether the separately gated focused Cargo check is
authorized. A failing source/result mapping remains a test-owner repair within
these exact test sections and must preserve the open logical telescope.

## Runtime and stop receipt

- Requested worker: Luna/high. Observed model and effort: UNKNOWN.
- Session: `current-conversation-2026-10-18`; no descendants.
- Assignment grant: 900 seconds, fully charged by the frozen sprint contract.
- Writes stopped after this progress note and the single inbox handoff were
  frozen.
- No independent review or production acceptance is claimed.
