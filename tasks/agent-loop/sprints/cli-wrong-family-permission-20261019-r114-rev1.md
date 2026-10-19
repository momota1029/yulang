# R114: wrong-family annotation permission through public execution

Status: **DRAFT_FOR_PRE_EXECUTION_REVIEW**. Primary and sole Git integrator:
Luna `/root`. R113 is closed NOT_RUN at its hard input boundary; this sprint
moves to the under-covered wrong-family permission front and a public CLI
observation, without repeating continuation storage or sibling-view isolation.

## Fixed authority and finite claim

The user's selected annotation policy in
`notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §1 says a
contravariant concrete `[E]` grants function-local subtraction permission for
that specified concrete effect identity. The selected typed-boundary transport
in `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` §13 retains the
corresponding source identity/authority and does not create capture authority
at positions without that exposure. The receiver-relative clarification in
`notes/design/2026-10-15-callback-identity-forwarding.md` preserves other
receivers' protection. These authorities fix the policy direction, but do not
prove the complete compiler/runtime realization or a universal hygiene theorem.

This packet asks one finite question: for the exact source below, does the
annotated `[other]` computation receiver fail to grant a `signal::ping` request
because the resolved `signal` family identity is absent from that receiver's
concrete row? The existing source test supplies a bounded precedent: ordinary
`CandidateInference::solve` accepts the source without conflicts, then the
Machine returns `RuntimeUnavailable::HandlerEvidence`. The source test is not
proof of the static-to-runtime correspondence or public CLI result.

Keep operation matching and receiver permission separate. This source has
`signal::ping` and an unrelated operation in family `other`; it tests a
wrong-family permission row, not same-spelling sibling operation selection,
sibling-view isolation, or all grant/receipt/image conditions. The finite
runtime outcome `HandlerEvidence` is an experimental missing-positive-certificate
result, not a language-level rejection or proof that the effect is forwarded.

## Fixed exact source and expected observation

Use exactly the existing Boolean instantiation of
`runtime_receiving.rs::primitive_roots_require_the_original_receivers_exact_concrete_permission`:

```yu
act signal:
    our ping: bool -> bool
act other:
    our unrelated: int -> int
my receive (input:[other] bool) = catch input { signal::ping(p), _ -> false }
my main = receive (signal::ping true)
```

Source is 195 UTF-8 bytes, SHA-256
`91c015cf7dce0132b0d7faa5cd7d30f87eb1fe3c3cadc5bd18db1595061a771f`,
without final LF. Preserve it byte-for-byte. Boolean construction is directly
owned by pinned HIR LocalSource code; no integer or string decoder is in scope.

Expected finite observation, conditional on ordinary preparation succeeding:

1. `CandidateInference::solve` has no candidate conflicts, as in the existing
   direct Machine fixture.
2. Direct Machine execution returns
   `RuntimeOutcome::Unavailable(RuntimeUnavailable::HandlerEvidence(site))`.
   The proof traces the authentic `[other]` family through HIR and the
   computation formal into the runtime receiver schema; it then traces the
   `signal::ping` request to the `local_grant` consumer and establishes that
   `signal` is not a member of the original `[other]` row. The source contains
   a Lambda, so the closed-primitive bypass does not apply.
3. Public stdin CLI `--run main --steps 10000 -` exits unsuccessfully, writes
   nothing to stdout, and writes the existing `runtime unavailable: ...`
   diagnostic to stderr. The expected diagnostic must be derived from the
   direct Machine's HIR-backed `SourceSite` for the same source and CLI name
   `-`; do not hard-code a numeric source range or hand-author a span.

A preparation failure is a separate source-surface obstruction and falsifies
this fixed prediction; do not reinterpret it as evidence for permission.

## Proof obligation, method and falsifiers

Construct a finite source-to-runtime correspondence for this one occurrence:

- The HIR source owner resolves `signal` and `other` to distinct authentic
  `SourceEffectId`s and resolves `signal::ping` to the `signal` family.
- The annotation owner and candidate source path retain `[other]` on the
  original `receive` computation formal. Static candidate acceptance is only
  the existing finite assertion; do not claim complete static effect hygiene.
- Runtime program construction projects that original formal/annotation to
  the receiving schema. Invocation/consumption creates the exact receiving
  owner and observation; the request retains its declaration identity.
- The machine bypass is checked and excluded for this program. The actual
  `Receiving::local_grant` consumer checks the exact request family against the
  receiver's concrete row. The row contains `other`, while the request family
  is `signal`, so the positive local grant is false and this handler attempt
  returns `HandlerEvidence` at its original HIR-backed site.
- The public `execute`/stdin CLI path returns that runtime error before any
  result rendering; `main` reports failure with empty stdout. The runtime test
  is an observation, not a proof premise for the static-to-runtime bridge.

Use a commuting source/consumer diagram and exact identity membership, not
family spelling. Do not infer that a missing Grant alone proves source-level
protection, rejection or forwarding. Do not claim sibling-view isolation,
negative evidence, actual inflow/residual correspondence, arbitrary receiver
transport, all source programs, or production authority.

Falsifiers include failure to resolve two distinct family identities, the
original `[other]` annotation not reaching the exact runtime receiver schema,
a `signal` grant being constructed from `[other]`, a closed-primitive bypass
on this source, a runtime outcome other than the fixed HandlerEvidence result,
public preparation failure, CLI success, nonempty stdout, or a diagnostic not
derivable from the original Machine SourceSite. A mismatch consumes this
packet's single attempt and stops without repair or retry.

## Frozen inputs

| Input | SHA-256 |
|---|---|
| Authoritative annotation policy `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |
| Typed-value transport direction `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| Receiver-relative clarification `notes/design/2026-10-15-callback-identity-forwarding.md` | `c544ed3c7b83686a740aa43b1db92d901de31a3b197f81f90a4c9dbdae561134` |
| Existing direct receiver fixture `tools/inference-playground/tests/runtime_receiving.rs` | `6ff65fc977c88837ec279b84088a6c2d89ebfc7f78915e7ac985904fcaa26bf2` |
| HIR module identity owner `crates/yu-hir/src/module.rs` | `c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a` |
| HIR LocalSource Boolean/annotation owner `crates/yu-hir/src/module/local_source.rs` | `3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786` |
| HIR family/operation identity owner `crates/yu-hir/src/module/source_annotation.rs` | `b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f` |
| Candidate source registration `crates/yu-solver/src/candidate_source.rs` | `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c` |
| Candidate effect/formal entry `crates/yu-solver/src/candidate_effect.rs` | `6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0` |
| Candidate solver orchestration `crates/yu-solver/src/shadow_apply.rs` | `5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb` |
| Runtime program/formal projection `tools/inference-playground/src/runtime/program.rs` | `7bc27580711d3ef09044e324541904ef3388aca8e3b4f3a72437b1e04dc0210a` |
| Primitive closed-world bypass `tools/inference-playground/src/runtime/primitive.rs` | `97485b9439357497aaf3f19555b1d87eef4aabc955b3a2815f23cf49a65c0153` |
| Runtime permission schema and consumer `tools/inference-playground/src/runtime/receiving.rs` | `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9` |
| Runtime request/control owner `tools/inference-playground/src/runtime/machine.rs` | `fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46` |
| Public prepare/execute boundary `tools/inference-playground/src/lib.rs` | `bdf996d0264e252e345c05bc77b2adcf625120281244171f0054f1d87a8d1e1b` |
| Public stdin CLI `tools/inference-playground/src/main.rs` | `75b38435f4634ee35b3e14a54fb4d021b78bda834b4fd53965302a73309e0100` |
| Output buffering/error boundary `tools/inference-playground/src/output.rs` | `04e99c5bdb562a8edb8a7e17bdcc03f7b46eaca9d8e13b20216b4dcf3032a88a` |
| Existing CLI child-process convention `tools/inference-playground/tests/cli.rs` | `cf265feba7414b159353c81751608e9c127b072559b2c8c4cc513ecbc15c22ea` |
| Package and integration-test target `tools/inference-playground/Cargo.toml` | `87e77de221b023c1c9f07e90f1ce6a692a56e8bb398eca4725f4910254be0a56` |

All pins and the exact source hash must match. Any additional required direct
owner stops the packet; no new source fixture or pin expansion is authorized.
The historical runtime test is reuse evidence only; its old green result is not
current execution evidence.

## Lanes, outputs and command gate

- Proof, Sol/high, cap 480 seconds; exact outputs only:
  `notes/theory/2026-10-19-r114-wrong-family-permission.md` and
  `tasks/agent-loop/inbox/20261019-r114-proof.md`.
- Test-only implementation, Luna/high, cap 240 seconds; exact outputs only:
  `tools/inference-playground/tests/cli_permission_boundary.rs` and
  `tasks/agent-loop/inbox/20261019-r114-implementation.md`. Add exactly one test
  `wrong_family_permission_withholds_runtime_and_cli_result`. It must perform
  the direct Machine observation and one public stdin CLI child. It derives
  the diagnostic from that direct error's original SourceSite rather than
  embedding a numeric span. No production edit or expected-output change.
- Fresh pre-edit spec review, shared review-pool cap 240 seconds:
  `tasks/agent-loop/inbox/20261019-r114-pre-spec-review.md`.
- Fresh post-output spec and compiler/source reviews:
  `tasks/agent-loop/inbox/20261019-r114-post-spec-review.md` and
  `tasks/agent-loop/inbox/20261019-r114-compiler-review.md`.
- Luna alone owns current state, command, review adjudication, closeout
  `notes/progress/2026-10-19-r114-wrong-family-permission.md`, and Git.

After proof and implementation outputs are frozen and both post-output reviews
are CLEAN, Luna may run exactly once:

```sh
CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-playground --test cli_permission_boundary wrong_family_permission_withholds_runtime_and_cli_result -- --exact --nocapture
```

No alternate command, standalone build, formatter, direct CLI invocation,
retry, or repair is authorized. Any command failure or predicted-outcome
mismatch consumes the attempt. Workers may not run executable commands or Git.

## Resources and breadth

Total ceiling: 1,200 seconds: proof 480, implementation 240, all fresh reviews
combined 240, command 120, closeout 120; Astra 0. R113/R111 resource usage is
not reset or reclaimed; all unknown prior resource use remains charged to its
original packet. Preserve the three inherited UNKNOWN identities, board
quarantine, R104 historical lease, R111 frozen unverified file, and every other
quarantined/held path.

R114 closes only one finite wrong-family permission route. It does not close
annotation integration, CandidateInference correctness, general static-to-
runtime projection, sibling-view isolation, missing-Grant semantics, source
admission, the original Simple-sub/evaluator claims or A/B, method/role
behavior, the other effect-hygiene fronts, or production authority. At the next
boundary choose an under-covered front among handler priority, Value/Computation
entry, continuation capture/resumption, projection, or method/role source
behavior; do not repeat this wrong-family fixture or R113's cursor path.
