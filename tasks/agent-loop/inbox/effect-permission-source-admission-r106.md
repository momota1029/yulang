# R106 Rust source-admission handoff

Sprint / contract: `EFFECT-PERMISSION-SOURCE-ADMISSION/20261101-R106`,
`tasks/agent-loop/sprints/effect-permission-source-admission-20261101-r106.md`,
SHA-256 `4ba4111669f060e9df96ce68b112a8a1d63320dc5857f5e8b65fdcf2113792f5`.
Assignment: `R106-RUST-SOURCE-ADMISSION`; handoff revision 3, superseding
frozen revision 1 SHA-256
`eda47e56e972daabe138af0f193bd8ebd288578dc3d321ecff3403a11099e05e` after
fresh compiler-referee rejections. Revision 2 SHA-256
`17d15d3adc3e92f758b4d36fd160d9f245a94db8ed1614ab7b09d08d62baead4` also had
a consumer-type mismatch.
Parent: original Yulang inference/source soundness and effect-hygiene
obligations, with the original Simple-sub source domain, claims and
quantifiers unchanged.

## Runtime, leases and outcome

Requested role/model/effort: `implementer`, `gpt-6-luna`/high. Observed
model/effort: UNKNOWN (runtime metadata unavailable). Worker identity:
`/root/r106_source_admission`. No child assignments.

Outcome class: **NO_SAFE_CODE_SLICE**. The ordinary admission restriction and
function result/application chain are identified, and the separately named
candidate encodes them, but baseline preservation cannot be certified. The
only pre-R106 artifact evidence is the pinned hash; removing the R106 block
from revision 1 yielded a different hash. The exact outside-block bytes cannot
be reconstructed under this assignment's no-Git/no-scratch boundary. Preserve
the unexplained bytes and do not execute Cargo. No source/native or parent
theorem claim follows.

Exact write leases used:

- `crates/yu-solver/src/candidate_effect.rs` (test code only)
- this handoff file

Read-only source owners remained unchanged: `candidate_source.rs`,
`shadow_apply.rs`, and `candidate_scheme.rs`.

## Frozen hashes and source-owner trace

- Sprint contract: `4ba4111669f060e9df96ce68b112a8a1d63320dc5857f5e8b65fdcf2113792f5`
- `crates/yu-solver/src/candidate_effect.rs`:
  `4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15`
- `crates/yu-solver/src/candidate_source.rs`:
  `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49`
- `crates/yu-solver/src/shadow_apply.rs`:
  `caeb837cd13b2e75e76fbed59dcc601e8c9d0a6a6a6f56f6959c0b0b9a98007f`
- `crates/yu-solver/src/candidate_scheme.rs`:
  `4494ba879a05f90767779e12c9ca8e1364f2203f2f60eb63239a544c0d0da470`
- `tasks/agent-loop/history/effect-permission-source-contract-20261101-r105-outcome.md`:
  reused; no file edit
- `tasks/agent-loop/inbox/effect-permission-source-contract-r105-source.md`:
  reused; no file edit
- `tasks/agent-loop/history/effect-permission-source-causality-20261101-r104-outcome.md`:
  reused; no file edit
- `tasks/agent-loop/inbox/effect-permission-source-causality-r104-source.md`:
  reused; no file edit

`candidate_source.rs` named-header collection associates the named result
annotation with the named group's `terminal_body`, then links the outer Lambda
to the definition root. Thus the annotation constrains the terminal body, not
an independently inferred outer function result. Ordinary
`CandidateInference::solve` preflights every retained local source with
`candidate_source::preflight_with_imports_and_roles`; this checks supported
annotation shapes/features but does not itself compare body and annotation
types. It then collects the candidate source world, runs the inference
session, and records the constructed candidate graph. The R104 helper used a
direct `InferenceSession` path and therefore did not establish ordinary
`solve` admission.

The R104 terminal expression `pure` has value shape `α -> Int`, while its
named result annotation has shape `(Int -> [E, 'e] Int) -> (Int -> [E, 'e] Int)`.
The pre-existing `Int`-versus-Function conflict is consistent with that
shape mismatch; R104's late `E` constraint adds no error. This is not evidence
of a solver omission.

## Candidate behavior and checks

The new test is
`candidate_effect::tests::r106_named_result_function_is_captured_freshened_and_consumed`.
Its source declares `left` with named result annotation
`(int -> ['e] int) -> (int -> [E] int)`. The negative callback port uses only
an open row variable, which ordinary preflight admits; concrete `E` occurs at
the positive returned-function result port. The terminal block defines and
returns `relay` with that shape; `relay` returns a function whose body calls
the declared `E::tick` operation. It then instantiates `left id` into `first`,
passes `id` to the returned `relay`, and applies the `run` function returned
by `relay id` to `1`, as `first id 1`.

The test uses only the ordinary `CandidateInference::solve` entry. It checks
that the candidate has no conflicts, `left` and `first` export as functions,
the `first` occurrence in the actual consumer has a fresh-use route retaining
an effect row, a source application is retained, and the consumer exports.
These are structural candidate observations; they do not prove the original
Simple-sub theorem, semantic admissibility, effect hygiene or source/native
correspondence.

No test/build command was run by this assignment. The only permitted Rust
command remains the exact single R106 command in the contract, after fresh
review and only if the candidate passes that review. The R104 and R105 Cargo
allowances are separate and exhausted or conditional as recorded in their
outcomes. No R104 fixture/assertion was intentionally edited; because the
outside-block hash discrepancy remains unreconstructed, I cannot certify full
byte preservation of all pre-existing test code.

## Reused/rejected evidence and unresolved premises

Reused R104's protected fixture/assertion inventory and its source trace only
for the observed diagnostic timing, identity-only representatives, absent
recursive-consumer effect forms, and live-versus-captured Support inventory.
Reused R105's source-contract audit that the shared-tail helper bypassed
ordinary `solve` and used a mismatched terminal body. Rejected any inference
from those direct-session failures to an ordinary-source solver omission.

Revision 1 was rejected for four findings: concrete `E` sat at a
preflight-negative port; its consumer passed `Int` where a callback was
required; its contract hash was stale; and removing only the R106 test block
left SHA-256 `0c0f9ccd…`, rather than R105's pinned baseline
`fab53f41cba94da6ada8850ae99b4ab03a7bfce46ff8f71306dc1b77ade73cb5`.
Revision 2 moves concrete `E` to a positive returned-function result, uses the
open-row form at the negative callback port, and records the live contract
hash, but passed `Int` to `first`, whose returned `relay` expects a callback.
Revision 3 changes the consumer to `first id 1`: `left id` has the returned
`relay` type `(int -> ['e] int) -> (int -> [E] int)`, `first id` yields
`run : int -> [E] int`, and applying `1` reaches the real operation consumer.
Baseline preservation cannot be reconstructed from the permitted evidence. During revision-1 editing I used
generic, unscoped replacements for test source/`Arc` spellings; they may have
matched a pre-existing test outside the R106 block. I cannot identify those
original outside-block bytes or certify that no protected test code changed.
I did not repair code outside the R106 test block; Luna must decide whether to
grant a source reconstruction lease. This uncertainty makes the lane
`NO_SAFE_CODE_SLICE`, despite the corrected candidate source shape.

The new test remains unexecuted and is not eligible for execution while the
baseline discrepancy is unresolved. Falsifiers are ordinary source rejection,
no function-shaped terminal body, a missing captured function, a missing
effect-row fresh use, or failure of the actual application consumer. Any such
failure must be reported as source evidence without changing protected
fixtures, diagnostics, domains, semantics or solver code.

Mutual TODO for Luna: obtain the exact pre-R106 bytes through an authorized
source reconstruction route and compare the complete delta. Keep Cargo at
0/1. If reconstruction establishes an R106-only delta, request fresh review
of the corrected candidate; only Luna may run the single command after PASS.
Do not alter a read-only source owner under this lease.

## Stop and hygiene receipt

All writes are stopped after freezing this handoff and the candidate hash.
Worker state: **STOPPED**; no descendants, persistent cache, test/build output,
generated path, or disposable scratch created. This is a worker stop receipt,
not a test, review, source/native, semantic, parent-theorem or production
closure. The candidate remains provisional pending independent review.

Changed paths: `crates/yu-solver/src/candidate_effect.rs` and this handoff
only. Known disposable scratch: none.
