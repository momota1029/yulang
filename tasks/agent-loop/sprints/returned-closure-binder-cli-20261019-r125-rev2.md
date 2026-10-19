# Sprint R125 rev2 — returned closure preserves its original binder

Status: CANDIDATE rev2; addresses the rev1 pre-spec finding by pinning the
retained-value consumer owner. Grant only exact source/spec delta review. Do not
start proof or implementation before CLEAN review and Luna's later exact grant.

Rev2 retains the exact source claim and all other authority. It adds the missing
`runtime/receiving.rs` owner required to trace successful consumption of the
retained closure value, alongside the existing `machine.rs` receipt path.

Branch `research/simple-sub-intrusion`; baseline `145aca5f6` (R124 closed and
pushed). This rotates to a finite static-to-runtime binder-correspondence
frontier and an ordinary runnable stdin surface after R124's effectful
resumption case. It continues the requested breadth/depth balance; it is not a
general closure theorem.

## Goal and exact outcome

For the existing `runtime.rs::returned_closure_retains_its_lexical_capture`
source, establish the exact path from its original `x` formal through
LocalSource/candidate identities, lambda emission, closure environment
capture, local alias `f`, later invocation with a distinct `y`, and Name lookup
of the original `x`. Show that returning from `capture` does not replace or
reconstruct the environment and that the later `f 9` body resolves the original
`x` value 7. Keep the body Name's lexical parameter identity distinct from
`y`; explain the actual environment parent/lookup constructors and consumers.

The exact source is 59 UTF-8 bytes, no final LF, SHA-256
`246f6fe5ff1a9685bf8ae3e264402a22e71be668d997330df3f92e0d272f672b`:

```yu
my main = { my capture x = \y -> x; my f = capture 7; f 9 }
```

Add one standalone public stdin CLI integration test at
`tools/inference-playground/tests/cli_returned_closure.rs`. Feed those exact
bytes unchanged to `yu-playground --run main --steps 10000 -`; assert successful
exit, stdout exactly `7\n`, and empty stderr. The CLI result witnesses public
ordinary-source execution only; it does not prove the binder/environment
correspondence.

## Authority and exclusions

Use charter §§21 and 24 only for ordinary unannotated `Value` argument entry
and the pure receiver role of an unannotated function literal. Keep parameter
entry separate from function receiver classification. Prove only the
constructor-consumer links present for this exact source and current playground
path. Candidate admission, type evidence, RuntimeProgram creation and bounded
execution remain explicit conditional premises unless source review establishes
them directly.

Do not claim general closure soundness, general lexical-scope correctness,
capture stability for arbitrary aliases or recursive sources, permission
equivalence, effect hygiene closure, method M/T/A, R85 adoption, any original
Simple-sub/evaluator A/B theorem, semantic approval, or production readiness.
No production code, existing test, expected output, language semantics, or
inference/evaluator parent may change. This source-identity witness is one
component of the static-to-runtime hygiene frontier, not a universal theorem.

Falsifiers: body `x` resolves to `y` or another binder; the returned closure
does not retain the original capture environment; alias `f` changes the
closure; a later invocation reconstructs `x` from spelling/type instead of
identity; HIR/candidate/runtime preparation fails; or CLI differs from exact
`7\n` with empty stderr.

## Pinned inputs

All hashes are SHA-256 at baseline `145aca5f6`:

```text
notes/design/2026-09-29-scc-intrusion-redesign-charter.md 547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed
notes/design/2026-10-11-yulang-inference-top-level-principles.md 7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81
tools/inference-playground/tests/runtime.rs f8bebfd4eb4571e2814b83ea8473c035b429fe1eed4e07d26942a096143306ec
tools/inference-playground/Cargo.toml 87e77de221b023c1c9f07e90f1ce6a692a56e8bb398eca4725f4910254be0a56
tools/inference-playground/src/lib.rs bdf996d0264e252e345c05bc77b2adcf625120281244171f0054f1d87a8d1e1b
tools/inference-playground/src/main.rs 75b38435f4634ee35b3e14a54fb4d021b78bda834b4fd53965302a73309e0100
tools/inference-playground/src/output.rs 04e99c5bdb562a8edb8a7e17bdcc03f7b46eaca9d8e13b20216b4dcf3032a88a
tools/inference-playground/src/runtime/machine.rs fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46
tools/inference-playground/src/runtime/receiving.rs 8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9
tools/inference-playground/src/runtime/program.rs c2363ad42104b895519bb29a8eb9aeda545bd0176cebbd78750d3a2df90849ca
tools/inference-playground/src/runtime/literal.rs 2fff177a7ba0cabb4930251e1facc8f9be701ff3ec7baa695ce4c182fa1da35f
crates/yu-hir/src/module.rs 153a23ecaa68fd150d8bd0cc0316f3723e1cb5d98a6e3026aadef2bfd08fd907
crates/yu-hir/src/module/local_source.rs 3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786
crates/yu-hir/src/source_identity.rs 7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3
crates/yu-solver/src/candidate_source.rs 66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c
crates/yu-solver/src/shadow_apply.rs 838d862dd34fe2b2bd70c5d92c5ce9af0aa98f10f8b6a8eddf313ae798686543
crates/yu-syntax/src/full_parse.rs 24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8
crates/yu-syntax/src/expression/lambda.rs 56357346a0f59330a202936f88337af1490b1839f339dc113b0b35f2d8c777b0
crates/yu-syntax/src/statement.rs fe8ba4e144b0c3ea5c8f451dddea42f718e9c3087aa77bb81447c61a9d213797
crates/yu-syntax/src/declaration/binding.rs eb9b7c9b97b999d16b364531fdcfad0bfc0cb377855e86ce6d5b825f5aba3544
crates/yu-syntax/src/syntax_kind.rs 26d2a0ddbe1862c95c503420ded0b0d35217bee5ba9f350be9163c065c6b488d
```

`tools/inference-playground/tests/cli_returned_closure.rs` does not exist at
baseline and is the sole new implementation path. Pre-spec may identify a
missing direct owner needed for the already fixed source claim; it may not
expand source scope or theorem. Any correction requires a sequential revision
and fresh CLEAN pre-spec review.

## Lanes, budget, and verification gate

Total ceiling: 1,440 seconds: inventory 120, pre-spec 180, proof 420,
implementation 240, final reviews 240, verification 120, closeout 120.
Unmeasured producer time is charged conservatively at its full cap. No lane may
borrow from another allowance. Primary repairs use closeout only.

After CLEAN pre-spec and Luna's exact grant:

- Proof lane `/root/r118_proof_lane`, cap 420 seconds. Writes only
  `notes/theory/2026-10-19-r125-returned-closure.md` and
  `tasks/agent-loop/inbox/20261019-r125-proof.md`. Derive exact original binder
  and source occurrences, candidate endpoints, emitted Lambda/Name identities,
  captured runtime environment, alias storage, later invocation environment
  extension and original-`x` lookup. Separate all premises and universal
  obligations. Read-only inspection is limited to pinned inputs and
  pre-spec-approved additions. No tests/builds/CLI/probes/formatter/Git.
- Implementation lane `/root/r118_implementation_lane`, cap 240 seconds. Adds
  one exact-source public stdin test and writes
  `tasks/agent-loop/inbox/20261019-r125-implementation.md`. It may not edit an
  existing source/test or expected output. No tests/builds/CLI/probes/
  formatter/Git.
- After both lanes STOP, fresh compiler/source, spec/authority, and regression
  reviewers check all hashes, binder/environment correspondence, exact CLI
  bytes and output, unchanged existing tests, and scope.
- Only after all three reviews are CLEAN, run exactly once:

```sh
CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-playground --test cli_returned_closure -- --exact returned_closure_preserves_original_capture_through_cli --nocapture
```

No alternative command, build, probe, retry, or second fixture. A failed
command consumes the attempt and remains an open result.
