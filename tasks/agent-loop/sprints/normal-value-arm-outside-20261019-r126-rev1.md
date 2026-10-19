# Sprint R126 rev1 — normal-value arm leaves its shallow handler

Status: CANDIDATE; grant only exact authority/source pre-spec review. Do not
start proof or implementation before CLEAN pre-spec and Luna's later exact
grant.

Branch `research/simple-sub-intrusion`; baseline `cbb462687` (R125 integrated
and pushed). This returns to handler extent after R125's ordinary closure
projection. It targets a named §14–15 transition and adds a paired runnable
surface; it is neither an output-only example nor a general handler theorem.

## Goal and exact outcome

Establish, for the two fixed sources below, the normal-return transition of one
shallow Catch: after the scrutinee returns and its value arm is selected, the
selected `Frame::CatchReturn` is validated and removed before value-binder
installation and arm-body evaluation. A fresh request raised by that arm
therefore cannot be selected by that same handler occurrence. Connect the
machine transition to the original Catch/Value-arm source identity and to the
subsequent request's authentic Apply occurrence. Keep the original request's
typed eligibility and handler-evidence premises distinct from requests raised
later by an outside arm.

The exact shared declaration prefix is:

```yu
act signal:
    our ping: () -> int
```

Control source, 80 UTF-8 bytes, no final LF, SHA-256
`92bfee56e9d09113e47b12cb87562c8add1a6658d94cfb6a74f24eabf23f9f2c`:

```yu
act signal:
    our ping: () -> int
my main = catch 7 { signal::ping(), k -> 9 }
```

Outside-arm source, 105 UTF-8 bytes, no final LF, SHA-256
`9c733787af2ec9f12b4ba98a150fd0894f2817a1ad838f53b5e6a8d9cd2527cd`:

```yu
act signal:
    our ping: () -> int
my main = catch 7 { signal::ping(), k -> 9, value -> signal::ping() }
```

For control, the typed machine must complete with integer `7` and the public
stdin CLI must exit successfully with stdout `7\n` and empty stderr. For the
outside-arm source, the typed machine must return an unhandled request for the
same HIR-owned `signal::ping` operation at original Apply range `89..103`, with
Unit payload and a live continuation. The public CLI must fail with empty
stdout and exact stderr
`unhandled runtime request at 89..103\n`. Preparation or `HandlerEvidence`
failure is not the predicted negative result. The exact bytes and CLI check are
finite observations only; they do not prove the frame/source derivation.

Add one standalone paired integration test at
`tools/inference-playground/tests/cli_value_arm_outside.rs`. In one exact test,
check typed Machine outcomes for both sources and run both through the public
stdin CLI. For the outside request, connect its SourceSite to the same HIR's
original LocalSource Apply and resolved operation. Do not edit existing tests,
fixtures, production code or diagnostics.

## Authority, parent contribution and exclusions

Use [the charter](../../../notes/design/2026-09-29-scc-intrusion-redesign-charter.md)
§§14–15 and the top-level inference principles only. The contribution is the
finite normal-return arm delimiter-exit edge: derive it from actual frame
construction, `return_value`, installation validation, value binding and the
next `propagate_request` check. Prefer a reusable local postcondition under
explicit source-formation/installation premises, and apply it to both exact
recipes. Keep the operation-request arm edge in R118 separate; this packet does
not generalize across every arm constructor.

Do not claim general Catch/handler hygiene, operation-arm or selector
priority completeness, generic delimiter semantics, complete source/native
correspondence, soundness, principality, any of the six parent frontiers,
method M/T/A, R85 adoption, or original Simple-sub/evaluator A/B closure. Do
not alter semantic rules, output expectations outside this new test, or
production code. This is conditional source/runtime evidence in the
research-only playground, not implementation promotion.

Falsifiers: selected installation remains available after the normal return;
the value binder/body is evaluated while that handler is active; the arm's new
request is caught by the exited handler; its source occurrence/range or
resolved operation differs from the authentic original Apply; either CLI
result differs from its exact contract; or candidate/source/runtime
preparation fails.

## Pinned inputs

All SHA-256 values are from baseline `cbb462687`:

```text
rules/design-authority.md e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1
notes/design/2026-09-29-scc-intrusion-redesign-charter.md 547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed
notes/design/2026-10-11-yulang-inference-top-level-principles.md 7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81
tools/inference-playground/tests/runtime_control.rs 2619e4c8bb006e2d98cf81887091ae372cb1ae3731de76e7b707a97db577009c
tools/inference-playground/Cargo.toml 87e77de221b023c1c9f07e90f1ce6a692a56e8bb398eca4725f4910254be0a56
tools/inference-playground/src/lib.rs bdf996d0264e252e345c05bc77b2adcf625120281244171f0054f1d87a8d1e1b
tools/inference-playground/src/main.rs 75b38435f4634ee35b3e14a54fb4d021b78bda834b4fd53965302a73309e0100
tools/inference-playground/src/output.rs 04e99c5bdb562a8edb8a7e17bdcc03f7b46eaca9d8e13b20216b4dcf3032a88a
tools/inference-playground/src/runtime/machine.rs fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46
tools/inference-playground/src/runtime/program.rs c2363ad42104b895519bb29a8eb9aeda545bd0176cebbd78750d3a2df90849ca
tools/inference-playground/src/runtime/receiving.rs 8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9
tools/inference-playground/src/runtime/continuation.rs 194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3
tools/inference-playground/src/runtime/primitive.rs 97485b9439357497aaf3f19555b1d87eef4aabc955b3a2815f23cf49a65c0153
tools/inference-playground/src/runtime/literal.rs 2fff177a7ba0cabb4930251e1facc8f9be701ff3ec7baa695ce4c182fa1da35f
crates/yu-syntax/src/full_parse.rs 24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8
crates/yu-syntax/src/statement.rs fe8ba4e144b0c3ea5c8f451dddea42f718e9c3087aa77bb81447c61a9d213797
crates/yu-syntax/src/expression/case_like.rs 6e306bc420e4084832008b64cf39c790648fc1510ba3f1de2876590f79ebe961
crates/yu-syntax/src/pattern/mod.rs 1b608422c93ce0f6947125a9b1ea88314a48b3a5e45030ed23e5154492ad7883
crates/yu-syntax/src/pattern/delimited.rs 9da9ec948775b438a85ca3f27c2805254a4f4171caddb54cabe44e563d017029
crates/yu-syntax/src/declaration/act_decl.rs f1af95a12df81900564c83d0aad541064eb2fff21ca41259b7a943ae3ad4fd74
crates/yu-syntax/src/declaration/binding.rs eb9b7c9b97b999d16b364531fdcfad0bfc0cb377855e86ce6d5b825f5aba3544
crates/yu-syntax/src/type_expr/mod.rs 2e08a49960cd4010ba39641ae509afb7cf59711c1464d3349f5f6db590ebf01f
crates/yu-hir/src/module.rs 153a23ecaa68fd150d8bd0cc0316f3723e1cb5d98a6e3026aadef2bfd08fd907
crates/yu-hir/src/module/local_source.rs 3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786
crates/yu-hir/src/source_identity.rs 7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3
crates/yu-hir/src/module/source_annotation.rs b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f
crates/yu-solver/src/candidate_source.rs 66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c
crates/yu-solver/src/candidate_effect.rs 6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0
crates/yu-solver/src/shadow_apply.rs 838d862dd34fe2b2bd70c5d92c5ce9af0aa98f10f8b6a8eddf313ae798686543
```

The new test path does not exist at baseline and is the sole implementation
write path. The pre-spec reviewer may require a missing direct owner for this
fixed claim but may not broaden the source domain or alter the §14–15 semantics.
Any repair requires a sequential contract revision and fresh CLEAN delta review.

## Lanes, resources and verification gate

Candidate total ceiling: 1,800 seconds: inventory 180, pre-spec 120, proof
600, implementation 300, final reviews 360, verification 120, closeout 120.
Unmeasured producer time is charged conservatively at the full lane cap. Astra
budget zero. Preserve the three inherited UNKNOWN reservations.

After CLEAN pre-spec and Luna's later exact grant:

- Proof lane `/root/r118_proof_lane`, cap 600 seconds. Writes only
  `notes/theory/2026-10-19-r126-value-arm-outside.md` and
  `tasks/agent-loop/inbox/20261019-r126-proof.md`. Derive source Catch/arm/Apply
  identities and the conditional frame postcondition through selection,
  frame removal, value binding, arm evaluation and the subsequent request
  consumer. Apply it to both recipes and keep typed-boundary premises explicit.
  No tests/builds/CLI/probes/formatter/Git.
- Implementation lane `/root/r118_implementation_lane`, cap 300 seconds. Adds
  one paired public stdin integration test and writes only
  `tasks/agent-loop/inbox/20261019-r126-implementation.md`. It checks the two
  exact typed Machine outcomes, the outside request's source/operation/payload/
  continuation lineage, and the two contracted CLI outcomes. No production
  edits, existing test/fixture changes, tests/builds/CLI/probes/formatter/Git.
- After both lanes STOP, assign fresh independent compiler/source,
  spec/authority and regression reviews on the frozen proof, paired test and
  handoffs. Run one exact targeted command only after all reviews are CLEAN:

```sh
CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-playground --test cli_value_arm_outside -- --exact normal_value_arm_runs_after_shallow_handler_exit --nocapture
```

No alternate command, retry, second fixture or extra build/probe is authorized.
Closeout records before/after evidence, remaining parent premises, exact
warnings, reviews, Git outcome and resource charges. Luna alone integrates and
pushes the intended range.

## Rotation record

R126 addresses shallow handler extent. Following candidates, subject to fresh
source/dependency inspection, are native operation-payload Value/Computation
entry; the reviewed method/role decision milestone (R119/R123), with R85
adoption separate; and receiver-permission expiry after resumption. Rotate
across the six distinct effect-hygiene fronts; never repeat one adjacent
storage/fiber slice merely for activity. No new contract here authorizes those
successors.
