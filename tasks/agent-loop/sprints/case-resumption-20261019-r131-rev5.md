# R131 rev3 — effectful Case scrutinee across shallow resumption

Status: CANDIDATE only. Delta closes both rev1 pre-spec MAJOR findings and the
rev2 MINOR finding; no proof, implementation, test or browser edit lease is
active until an independent CLEAN delta review and Luna's explicit grant.
Preserved rev2 SHA-256
`fc67663d081d5330466bb5915a4df31c3451d9d3d23aa7a94cc658fa639e293a`.

Branch `research/simple-sub-intrusion`; proposed baseline
`53c313c7b32aa3d7f4f49aacb3b447f9c53ae908`.

## Original outcome and authority

The user's ongoing outcome is proof-backed inference/evaluation breadth while
preserving original Simple-sub and evaluator A/B claims, quantifiers and
semantic adoption gates. R131 targets a finite source-to-runtime correspondence
slice: a request in an effectful Case scrutinee is handled by a declared
`[io] int` receiver; resuming its captured continuation with an integer returns
through the saved Case frame, retains that frame's lexical environment and
received value/view, selects the expected Case arm, then evaluates that arm.
The selected shallow handler is absent when the arm runs.

This is experimental inference-playground and WebAssembly-playground evidence.
It adds no language rule, stable syntax, runtime behavior, production authority
or theorem premise. Original Simple-sub/evaluator A/B, H/A/E/B, all six
effect-hygiene parents, R85 adoption, method M/T/A, R128 review and R129 review
remain OPEN or provisional as currently recorded. The R130 finite Case result
is a dependency for scheduling only; it does not prove this resumption path.

## Fixed outcome and probes

Establish the finite request -> capture -> resumption -> saved Case frame ->
selected arm transition, or identify the exact missing runtime/source premise.
Carry one positive and one paired shallow-handler negative through the public
CLI and browser WASM example path. Required candidate sources:

```yu
act io:
    our tick: int -> int
    our other: int -> int
my relay (thunk:[io] int) = catch thunk { io::tick(value), k -> k 9 }
my main = relay { case io::tick 0: 9 -> 91, _ -> 17 }
```

The positive must complete with `91\n`: the receiver supplies 9 to the
interrupted Case scrutinee, selecting its first arm. Paired negative:

```yu
act io:
    our tick: int -> int
my relay (thunk:[io] int) = catch thunk { io::tick(value), k -> k 9 }
my main = relay { case io::tick 0: 9 -> io::tick 8, _ -> 17 }
```

The negative must fail with an `unhandled runtime request` for the second
`io::tick` and publish no completed output. This is discriminating: if the selected shallow `tick`
handler were incorrectly reinstalled, it would resume the arm's second request
with 9 and the program would complete. A different failure, including
unsupported source, inference rejection, wrong arm/value, lost environment or
view, or handler reinstallation, falsifies the proposed route.
The browser example must expose both positive and negative runs; the smoke test
must check the positive result and the negative error/no-completion outcome.

These exact sources are candidates pending grammar/owner review. If either
requires new syntax or runtime policy, stop and return the exact choice to Luna.

## Proof lane — 450 seconds, Sol/high

Produce `notes/theory/2026-10-19-r131-case-resumption.md` and
`tasks/agent-loop/inbox/20261019-r131-proof.md`. Trace the exact retained
constructors and machine transitions from the source Case and declared
receiver through `Frame::Case`, request propagation, suffix capture,
`capture_template`, `TemplateNode::Bind`, continuation application, response
validation, restored frame return, source-order Case selection, and selected
arm execution. Use an induction over the finite captured frame sequence and an
explicit event/owner trace. State exactly which environment, value, view and
handler-boundary frames are retained, discarded or re-entered. Show the paired
negative reaches the unhandled request boundary after the selected arm starts.

Establish the finite preservation result under explicit successful formation,
receiver evidence, continuation response compatibility and resource premises,
or identify the first obstruction with source owner and counterexample. Do not
generalize from the transition trace to arbitrary effects, full evaluator
correctness, native compiler behavior or A/B. Apply no open hygiene lemma
outside its actual premises. The existing R130 proof and old receiver
permission CLI regression are context, not substitutes for this derivation.

## Implementation lane — Luna/high, 360 seconds

After CLEAN contract review and Luna's grant, add the paired public CLI
regression at `tools/inference-playground/tests/cli_case_resumption.rs` and
extend only the browser example surface at `web/playground/src/main.ts`,
`web/playground/index.html` and `web/playground/smoke-test.mjs`. Reuse the
existing `[io] int` receiver and Case source path. The implementation does not
edit runtime, solver, parser, stable syntax, expected behavior of existing
examples, or inference policy. Keep both sources and assertions exact in the
contract. No tests, build or browser checks run in the implementation lane.

The only authorized browser smoke invocation is
`(cd web/playground && node smoke-test.mjs)`, after
`npm --prefix web/playground run build:wasm`. Any generated
`web/playground/src/wasm/yulang_wasm.js`, `yulang_wasm.d.ts`,
`yulang_wasm_bg.wasm`, and `yulang_wasm_bg.wasm.d.ts` are ignored build outputs,
not integration files. No edits outside the named sources are authorized.

## Pinned source owners at baseline

| Input | SHA-256 |
|---|---|
| `crates/yu-solver/src/candidate_source.rs` | `cbc39315f4243b0bae1db74976cf94282bc94cd28b9eb463699c085f421065f7` |
| `tools/inference-playground/src/runtime/program.rs` | `28748da0458da92b9d1190b250bbb84bdecc6643718eacbca95a04f5d6c9aa0d` |
| `tools/inference-playground/src/runtime/machine.rs` | `4fb918732047f61184bc8f89b829bde68a8d1e6649a24d02640ec14500ae0acd` |
| `tools/inference-playground/src/runtime/continuation.rs` | `194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3` |
| `tools/inference-playground/src/runtime/receiving.rs` | `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9` |
| `tools/inference-playground/src/lib.rs` | `bdf996d0264e252e345c05bc77b2adcf625120281244171f0054f1d87a8d1e1b` |
| `tools/inference-playground/Cargo.toml` | `87e77de221b023c1c9f07e90f1ce6a692a56e8bb398eca4725f4910254be0a56` |
| `tools/inference-playground/tests/cli_resumed_receiver_permission.rs` | `9a5fd48d1f89ae064960554d8ece36d6b9b437ae6cc91504a1e7c035aec9257a` |
| `tools/inference-playground/tests/cli_case_source_progress.rs` | `f831c17a06edca36ea13df9cdece3c7ac8fdf4e025488f17375b87a598c7fa44` |
| `apps/yulang-wasm/src/lib.rs` | `2fc9feb353b3130c4efc888270cec14cba8b2bbcc2fca03d3780c676e0468f8a` |
| `apps/yulang-wasm/Cargo.toml` | `c00101fa1b063622a9826a7971add7396e0f73b614d408f2e962a006799966f6` |
| `Cargo.lock` | `de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5` |
| `web/playground/src/main.ts` | `efdf8bcd8c727a105a85c3ff7c581bcfcb218781db17e88be50e330b7ce6bcab` |
| `web/playground/index.html` | `157d70d0cdc757f485208f0df1f934c647bd2f807696a1140f873bece8ba65ce` |
| `web/playground/smoke-test.mjs` | `67d498313fdab02cb1689d4a9a5bde44ce46cae1d8938f133a7d25f65cfe602e` |
| `web/playground/package.json` | `ff870bfa1ba5cbb139a5a0b1d34673684eed9984f821548703ad648d0c9d1caf` |

Before any grant, verify all listed hashes at the proposed baseline. Preserve
the R130 commit and push receipt. Any changed byte
requires a sequentially revised contract and another read-only delta review.

## Reviews, verification, resources and stop conditions

The pre-spec reviewer has read-only access to this candidate and pinned
owners. Rev1 review found (1) the distinct `io::other` negative did not falsify
handler reinstallation because the handler matched only `io::tick`, and (2)
the root-relative smoke invocation used a script whose WASM read path is
relative to `web/playground`. Rev2 uses a second `io::tick` in the selected arm,
which completes if the handler is restored. Rev2 also left a stale
root-relative smoke invocation at lines 98–99; the rev2 delta reviewer
correctly flagged it. Rev3 removes that invocation and authorizes only the
smoke command with `web/playground` as its working directory. No producer or code/browser write
begins before CLEAN delta review and Luna's explicit acknowledgement. After
both author lanes STOP, freeze proof,
handoffs, implementation and direct dependencies for fresh independent
compiler/source, spec/authority and regression review. Authors and coauthors
cannot review their own evidence. Only after all required reviews are CLEAN may
Luna run exactly these bounded verification commands, serially:

```text
cargo test -p yu-playground --test cli_case_resumption -- --exact case_scrutinee_resumes_into_selected_arm_and_shallow_handler_stays_absent
npm --prefix web/playground run build:wasm
(cd web/playground && node smoke-test.mjs)
```

No separate package check, full workspace test, browser automation or benchmark
is authorized. At most one heavyweight compiler/build process at a time.

Budget cap: 1,560 seconds total; inventory 180, pre-spec 210, proof 450,
implementation 360, final reviews 180, verification 120, closeout 60. One
proof worker and Luna primary only; zero Astra. No nested sprint team. Record
actual IDs/session/model/effort (UNKNOWN if unavailable), active work and STOP
receipts. Preserve every inherited UNKNOWN identity, reservation and
quarantined lease. Return to Luna before any runtime/compiler change, syntax
change, path expansion, second verification attempt, or budget increase.

Luna alone integrates explicit paths, reviews the complete outbound range,
updates compact state and closeout, and commits/pushes non-forcibly. Success is
only finite reviewed source/runtime and public CLI/WASM evidence. It cannot
close the original A/B, any hygiene parent, R85 adoption, R128 review or R129
review. Consultation triggers: material obstruction, authority/dependency/
lease change, integration boundary, or next sprint start/end.

## Revision 4 — verification repair boundary (supersedes verification/resources)

Rev3 verification failed on its first CLI command (exit 101). The CLI
diagnostic reported the second tick's argument-tail source range `152..153`,
while rev3 asserted the complete textual Apply range `143..153`. Existing
source ownership assigns the Apply's `MlArgument` tail to the runtime site;
the failure is an incorrect test expectation, not evidence of a runtime defect.
The WASM build and smoke were not run. The failed attempt is preserved and may
not be repeated except under this revision.

Only the CLI regression and browser smoke assertion are reopened. Both now
derive the one-byte argument-tail range from the exact negative fixture and
require that specific range in the unhandled-request error. Positive output,
empty negative CLI output, the paired sources, and shallow-handler behavior
remain unchanged. Proof, runtime, browser main and HTML remain frozen.

The repair snapshot is `tools/inference-playground/tests/cli_case_resumption.rs`
SHA-256 `53657cd7a3bf57549fcad9f411a5ccd80e9315fcedbd0e86052f6cefb3fd944f`
and `web/playground/smoke-test.mjs` SHA-256
`6071129b561c8cae9ab1b147aaf8dd87eb2a802b51f92b187076c34c2cf5fea2`.
Implementation handoff revision 3 records the failed command, corrected source
provenance and these hashes. Obtain three fresh focused CLEAN delta reviews:
compiler/source (argument-tail to runtime diagnostic), regression (second event
and preserved assertions), and spec/authority (exact paths, resource extension
and retry sequence). No command may run before all three are CLEAN.

Luna authorizes one serial retry of the exact CLI command above, followed only
if it passes by the exact WASM build and correctly located smoke commands above.
Stop on the first failure; no further retry is implied. No runtime/compiler
change or additional verification is authorized.

The original 1,560-second cap is exhausted conservatively: the first failed
verification is charged the full 120-second grant because its exact duration
was not retained. Rev4 raises the cap to 1,800 seconds with 30 seconds for this
assertion/handoff repair, 90 seconds for the three focused reviews, 120 seconds
for the one serial verification sequence, and the existing 60-second closeout
reserve. Previously charged inventory 180, pre-spec 210, proof 450,
implementation 360, final reviews 180 and failed verification 120 total 1,500
seconds; no previous spend is reset. Record actual new spend and stop at 1,800.

## Revision 5 — expectation-protection recovery and accounting

Rev4's spec delta review is STOP, not CLEAN. The CLI diagnostic-span
expectation was edited after the failing run before the required pre-write
`spec_auditor` review. This is a recorded workflow violation under
`rules/testing.md` §Expected-output protection; a later review cannot make that
earlier write compliant. The source-owner explanation establishes why the
argument-tail span is technically correct, but does not erase the process
failure. Verification remains stopped.

Before any further test or smoke expectation write, obtain a prospective
independent `spec_auditor` assessment of this exact recovery: restore the
previously reviewed rev3 assertion snapshots (CLI SHA-256
`42cebe261199451e66da41fdef5b975d3cd622b6a56f78fea60d9775b13465f7`, smoke
SHA-256 `f5af63fa6991743d06dea8cb7cc035a6d9949346171ada74321c9058dcc99c74`),
then apply only the source-justified correction to derive the one-byte second
tick argument-tail range from the unchanged negative fixture. Retain the
specific unhandled-request check, positive output and negative no-completion
checks. The reviewer must confirm this corrects source attribution without
changing the shallow-handler contract or weakening the test. A rejection or
unresolved objection keeps all verification stopped.

If prospective review is CLEAN, Luna will restore those two reviewed snapshots
and reapply the exact approved argument-tail correction, then freeze the
resulting hashes and issue implementation handoff revision 4. The earlier
workflow violation remains recorded and is not described as retroactively
cured. The rev4 compiler/source and regression delta reviews stay valid for the
unchanged code semantics; obtain fresh focused CLEAN compiler/source,
regression and spec/authority acceptance of the recovered candidate before
verification.

Accounting is reconciled: the failed first CLI attempt consumes 120 seconds;
the remaining single retry sequence has a separate 120-second reservation.
The rev4 values `5 charged / 115 reserved` were contradictory and are void.
The 1,800-second rev4 envelope already accounts for 1,500 seconds of prior
work, 30 seconds for the premature repair, 90 seconds for its three reviews,
120 seconds for the retry and 60 seconds for closeout. Rev5 raises the finite
cap to 1,950 seconds: add 30 seconds for prospective spec review, 30 seconds
for the restore/reapply/handoff, and 90 seconds for the final three focused
reviews. No prior spend or violation is reset. Stop at 1,950 seconds. The
retry commands remain gated on the recovered hashes and all three fresh CLEAN
reviews; run once serially and stop on the first failure.
