# Sprint R120 — pending local resumption through the public CLI

Status: CANDIDATE pending fresh pre-spec review and Luna's grant.  
Branch / baseline: `research/simple-sub-intrusion` at `af551a720`; R119 remains a reviewed local checkpoint awaiting integration.  
Goal: continue broad/deep proof-backed inference and evaluator work, with a distinct continuation/resumption hygiene witness and an early runnable effectful source surface. Method/role evidence remains active through R119; R85 adoption stays a separate user decision.

## Exact outcome

For the exact existing `runtime_resume.rs` source below, construct a finite conditional source-to-runtime trace connecting the original pending `result` local, the captured continuation, response `9`, resumed lexical lookup and final public value. Then add one test-only public stdin CLI observation of those exact bytes.

Source: 175 bytes, no final LF, SHA-256
`7f3e39f4eb59da052e209bae88cd80cedff00e7158d0818e8b02c5faa70ee25f`:

```yu
act io:
    our tick: int -> int
    our other: int -> int
my relay (thunk:[io] int) = catch thunk { io::tick(p), k -> k 9 }
my main = relay { my result = io::tick 7; result }
```

The public CLI cell predicts successful exit, stdout exactly `9\n`, and empty stderr for `--run main --steps 10000 -`. This value is anchored in the existing same-source runtime test's `assert_integer(..., "9")`; it is a new CLI observation, not an edit to an existing expected output.

Proof must distinguish the request response from the pending local and final result. Follow capture of the current computation, application of raw `k 9`, resumption through the saved body, completion of `my result`, lexical lookup of that original binder, completion of `main`, and public value/output projection. Keep the containing invocation identity and its active lifetime explicit. Source preparation, candidate admission, same-HIR construction and bounded completion are premises unless this packet directly establishes them.

Falsifiers: the resumed continuation writes or reads another local/environment; the containing owner is expired or replaced; the selected shallow handler is reinstalled; saved body execution is bypassed; exact source preparation fails; or public status/value/streams differ. A matching output alone does not prove the internal simulation. Do not appeal to a fresh-receiver law or any general foreign-continuation rule.

## Authority and exclusions

Use only the already approved runtime and receiving authority in the pinned charter §§14–17 and 21, together with the reviewed primitive computation-root receiving theorem and raw-template correspondence listed below. Those sources do not close arbitrary resumption, foreign-continuation, source/native, Simple-sub/evaluator, permission, projection or general handler-priority claims. Keep R111's failed one-shot receipt unchanged. The 175-byte source is distinct from both R111 recipes. Do not edit `runtime_resume.rs`, `cli_raw_resume.rs`, existing expected outputs, production runtime code, diagnostics, or question files.

No method/role behavior is adopted or implemented here. R119's M/T/A findings remain conditional/open; R85 stays Draft/unadopted. R118's ordinary/effectful public cells remain prior finite observations. Do not let this one front monopolize future work: after R120, rotate to a genuine outward request plus suffix or advance the adopted method vertical path only if the user has adopted R85.

## Frozen inputs

All pins are to be revalidated against current bytes before the grant:

```text
notes/design/2026-09-29-scc-intrusion-redesign-charter.md 547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed
notes/theory/2026-10-16-primitive-computation-root-receiving.md a043c69eb9fd82127bb7ad59d797abf3f10c5edf83bd80316183074f48c28606
notes/theory/2026-10-16-runtime-resume-template-correspondence.md f3a4c925a197e63e5b7faf1ce1e1caf5736d76f1b86ba162c6acc85bfff8e7dd
notes/progress/2026-10-16-playground-raw-resume.md fea89067d065178b1fc61eb06ce98cada2c6bde21db46e8f0695b9abb085591c
tools/inference-playground/tests/runtime_resume.rs 449c3ce11ef04fa60a49517c2fc8a7994d1547cb2dee058d6fdcbd0b095f8580
tools/inference-playground/src/runtime/program.rs c2363ad42104b895519bb29a8eb9aeda545bd0176cebbd78750d3a2df90849ca
tools/inference-playground/src/runtime/machine.rs fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46
tools/inference-playground/src/runtime/continuation.rs 194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3
tools/inference-playground/src/runtime/receiving.rs 8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9
crates/yu-hir/src/module.rs 153a23ecaa68fd150d8bd0cc0316f3723e1cb5d98a6e3026aadef2bfd08fd907
crates/yu-hir/src/module/local_source.rs 3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786
crates/yu-hir/src/source_identity.rs 7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3
crates/yu-solver/src/candidate_source.rs 66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c
tools/inference-playground/src/main.rs 75b38435f4634ee35b3e14a54fb4d021b78bda834b4fd53965302a73309e0100
tools/inference-playground/src/lib.rs bdf996d0264e252e345c05bc77b2adcf625120281244171f0054f1d87a8d1e1b
tools/inference-playground/src/output.rs 04e99c5bdb562a8edb8a7e17bdcc03f7b46eaca9d8e13b20216b4dcf3032a88a
tools/inference-playground/tests/cli.rs cf265feba7414b159353c81751608e9c127b072559b2c8c4cc513ecbc15c22ea
tools/inference-playground/Cargo.toml 87e77de221b023c1c9f07e90f1ce6a692a56e8bb398eca4725f4910254be0a56
```

The proof lane may inspect only these inputs. The implementation lane may inspect these and the leased new CLI file after creation. Any pin mismatch or required unlisted owner returns to Luna before writing.

## Two lanes and exact leases

After CLEAN pre-spec review and Luna's grant:

- Proof, Sol/high, cap 420 seconds; writes only `notes/theory/2026-10-19-r120-local-resumption.md` and `tasks/agent-loop/inbox/20261019-r120-proof.md`. Trace the exact source path, original binding/environment and continuation owners; state HIR/candidate/Grant premises and remaining parent obligations. No tests, builds, CLI or probes.
- Implementation, Luna/high, cap 300 seconds; writes only `tools/inference-playground/tests/cli_local_resume.rs` and `tasks/agent-loop/inbox/20261019-r120-implementation.md`. Add one child-process stdin test for exact source and arguments; assert success, exact `9\n`, empty stderr. Do not edit `cli_raw_resume.rs` or any old expected value. No command.
- After both writers STOP, fresh compiler/source, spec and regression reviews (240 seconds total) inspect the frozen proof, source correspondence, new CLI scope and untouched R111 test.
- Luna runs one command, timeout 120 seconds, only after all three reviews are CLEAN:

```sh
CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-playground --test cli_local_resume -- --nocapture
```

No standalone build, direct CLI, formatter, alternative or retry. A failure or timeout consumes the attempt and leaves the finite observation open.

Total cap 1,500 seconds: inventory 180; pre-spec review 120; proof 420; implementation 300; post-output reviews 240; command 120; closeout 120. Astra 0. Preserve all UNKNOWN reservations and quarantined paths. Luna owns current state, review assignment, command, integration and Git. Stop at a missing owner, dependency drift, authority ambiguity, blocking review, unexpected output or budget limit.
