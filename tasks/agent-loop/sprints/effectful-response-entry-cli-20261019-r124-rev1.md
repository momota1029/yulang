# Sprint R124 rev1 — effectful response entry with a public surface

Status: CANDIDATE; only exact pre-spec review is granted. No proof or
implementation lease until Luna grants after CLEAN pre-spec.

Branch `research/simple-sub-intrusion`; baseline `dfcdea084` (R123 closed and
pushed). This is a new finite slice selected to pair one effect-hygiene
ordering obligation with an early runnable source surface. It does not continue
any storage/fiber inventory.

## Goal and exact outcome

For the one existing `runtime_resume.rs::response_expression_is_forced_once_before_entering_the_saved_context`
fixture, derive a bounded source-to-runtime trace for the actual effectful
response `io::other 11`. Establish that the `other` computation is evaluated
once, its `j` continuation returns the response into the pending application,
and only then the distinct saved `tick` continuation `k` is entered with 11.
Account for the source binder, operation, and continuation identities at each
step. Distinguish static source/IR derivation from the existing test's observed
completed integer. If any required source-to-runtime edge is absent, name its
owner and stop at that edge; do not infer ordering or multiplicity from `11`
alone.

The exact fixture bytes are 247 UTF-8 bytes, no final LF, SHA-256
`e50687fbb969684f41cb6b7f1cba627aed97602dd3847714b8379e40de928ea9`:

```yu
act io:
    our tick: int -> int
    our other: int -> int
my answer (pending:[io] int) = catch pending { io::other(p), j -> j p }
my relay (thunk:[io] int) = catch thunk { io::tick(p), k -> answer (k (io::other 11)) }
my main = relay (io::tick 7)
```

Add one standalone public stdin CLI integration test at
`tools/inference-playground/tests/cli_response_entry.rs`. It must feed the exact
fixture bytes unchanged through `yu-playground --run main --steps 10000 -` and
assert successful exit, stdout exactly `11\n`, and empty stderr. The finite
proof and this independent CLI observation are paired; the CLI output is not a
trace of event count or continuation order. The existing runtime test and all
existing tests/expected output remain byte-identical.

## Authority and exclusions

Use charter §§16, 21, and 24 only for the selected invocation/entry mechanics,
the explicit `[io] int` Computation parameter roles, and receiver-role
clarification. Reuse the runtime-resume template correspondence only at the
constructors and premises it actually establishes. Preserve HIR/candidate
admission and exact source identity as separate premises. Do not claim a
general once-only effect law, general continuation theorem, handler-priority
theorem, static/runtime projection closure, method M/T/A, R85 adoption, any of
the original A/B claims, or semantic approval. No production code, language
semantics, expected output, proof parent, storage design, or effect-fiber
representation may change.

The `OperationV1` runtime receipt machinery for the separate Function-response
fixture returning 42 is not evidence for this source. Do not inject or infer
such a receipt here. The R124 proof must follow the ordinary existing
`RuntimeProgram`/`Machine` path for the exact fixture.

Falsifiers: `j` and `k` are conflated; `io::other 11` is omitted, repeated, or
evaluated after `k` entry; the response does not reach the saved `k` context;
candidate/runtime preparation fails; or the CLI outcome differs from exact
`11\n` with empty stderr.

## Pinned inputs

All hashes are SHA-256 at baseline `dfcdea084`:

```text
notes/design/2026-09-29-scc-intrusion-redesign-charter.md 547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed
notes/design/2026-10-11-yulang-inference-top-level-principles.md 7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81
notes/theory/2026-10-16-runtime-resume-template-correspondence.md f3a4c925a197e63e5b7faf1ce1e1caf5736d76f1b86ba162c6acc85bfff8e7dd
tools/inference-playground/tests/runtime_resume.rs 449c3ce11ef04fa60a49517c2fc8a7994d1547cb2dee058d6fdcbd0b095f8580
tools/inference-playground/tests/cli_local_resume.rs c315daccfd28279192b0052f55c5558fa11133509291855129f744037633e747
tools/inference-playground/Cargo.toml 87e77de221b023c1c9f07e90f1ce6a692a56e8bb398eca4725f4910254be0a56
tools/inference-playground/src/lib.rs bdf996d0264e252e345c05bc77b2adcf625120281244171f0054f1d87a8d1e1b
tools/inference-playground/src/main.rs 75b38435f4634ee35b3e14a54fb4d021b78bda834b4fd53965302a73309e0100
tools/inference-playground/src/runtime/machine.rs fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46
tools/inference-playground/src/runtime/program.rs c2363ad42104b895519bb29a8eb9aeda545bd0176cebbd78750d3a2df90849ca
tools/inference-playground/src/runtime/continuation.rs 194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3
tools/inference-playground/src/runtime/receiving.rs 8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9
tools/inference-playground/src/runtime/mod.rs 64d208743793a03501a76f56bc2b511c50ed40cff3f789757a00b7d608fc846b
crates/yu-hir/src/module.rs 153a23ecaa68fd150d8bd0cc0316f3723e1cb5d98a6e3026aadef2bfd08fd907
crates/yu-hir/src/module/local_source.rs 3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786
crates/yu-hir/src/source_identity.rs 7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3
crates/yu-solver/src/candidate_source.rs 66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c
```

`tools/inference-playground/tests/cli_response_entry.rs` does not exist at the
baseline. It is the sole new implementation path. Pre-spec may identify exact
additional direct owners required to derive the already fixed source claim; it
may not broaden source scope or semantics. Any contract correction requires a
sequential revision and fresh CLEAN pre-spec review.

## Lanes, budget, and verification gate

Total ceiling: 1,440 seconds: inventory 120, pre-spec 120, proof 480,
implementation 240, final reviews 240, verification 120, closeout 120.
Unmeasured producer time is charged conservatively at its full cap. No lane may
borrow from another allowance. Primary repairs use closeout only.

After rev1 pre-spec CLEAN and Luna's exact grant:

- Proof lane `/root/r118_proof_lane`, cap 480 seconds. Writes only
  `notes/theory/2026-10-19-r124-response-entry.md` and
  `tasks/agent-loop/inbox/20261019-r124-proof.md`. Prove the exact binder and
  operation lineage, response-expression evaluation and `j`/`k` entry order
  from pinned source constructors. State premises and the unproved general
  claims. Read-only source inspection is limited to the pinned inputs and
  pre-spec-approved additions. No tests/builds/CLI/probes/formatter/Git.
- Implementation lane `/root/r118_implementation_lane`, cap 240 seconds. Adds
  the one new exact-source public stdin test and writes
  `tasks/agent-loop/inbox/20261019-r124-implementation.md`. It may not edit an
  existing file or alter source/expected output. Read-only inspection is
  limited to its contract-approved harness inputs. No tests/builds/CLI/probes/
  formatter/Git.
- After both lanes STOP, fresh compiler/source, spec/authority and regression
  reviewers check pins, proof/source correspondence, unchanged existing tests,
  exact CLI bytes and outputs, and scope.
- Only after all three final reviews are CLEAN, run exactly once:

```sh
CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-playground --test cli_response_entry -- --exact response_expression_runs_before_saved_continuation_entry --nocapture
```

No alternative command, build, probe, retry, or second fixture. A failed
command consumes the attempt and remains an open result.
