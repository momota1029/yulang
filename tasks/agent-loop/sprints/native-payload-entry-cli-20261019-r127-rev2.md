# Sprint R127 rev2 — declaration role controls native operation-payload entry

Status: CANDIDATE rev2; request only a read-only delta review of the rev1 minor. No proof or implementation starts before CLEAN delta review and Luna's later exact grant.

Branch research/simple-sub-intrusion; baseline 234d2b6d579f12e01448042a8d79d1cf145afb73 (R126 pushed). This advances a distinct §21 Value/Computation entry edge from operation declaration syntax through native request publication. It keeps ordinary and effectful source execution runnable and does not reopen handler extent, closure storage, or permission-fiber work.

## Original outcome and success evidence

For these two fixed programs, derive the conditional source-to-runtime path from the act operation declaration and call through HIR LocalSource, candidate preparation, RuntimeProgram and the native operation consumer. The resolved declaration's argument annotation determines whether the delayed argument is forced as a Value before a request is published or exposed as a Computation payload without being forced. Connect declaration, operation identity, Apply occurrence, delayed argument, request payload and continuation. Keep operation argument entry role distinct from §24 receiver role and from solved-effect or permission evidence.

The existing runtime-control recipes have no final LF:

    act signal:
        our ping: int -> int
    my main = { my loop x = loop x; signal::ping(loop ()) }

Value source: 92 UTF-8 bytes, SHA-256 a620b984fea7f339da2adcf4acfd053725fcf10e63861efc20a0f8e769b5189e. The authentic request Apply is expected at outer CallTail 81..90. The delayed argument diverges; under the exact 1,000-step bound, typed Machine must return ResourceExhausted { steps: 1000 } before publishing a request. Public stdin CLI must fail with empty stdout and these exact stderr bytes, including one terminal LF and no other bytes: `runtime step budget exhausted after 1000 steps; no completed result\n`.

Computation source changes only the declaration argument annotation:

    act signal:
        our ping: [] int -> int
    my main = { my loop x = loop x; signal::ping(loop ()) }

Computation source: 95 UTF-8 bytes, SHA-256 7041a3314180f4438ca717794bbaaf7b5dc2e904096211f0682df2d14969bbbc. Its authentic request Apply is expected at outer CallTail 84..93. Under the exact 10,000-step bound typed Machine must return UnhandledRequest for the same HIR-owned ping declaration, with RuntimeValueKind::Computation payload and a live continuation. Public stdin CLI must fail with empty stdout and these exact stderr bytes, including one terminal LF and no other bytes: `unhandled runtime request at 84..93\n`.

Add one standalone paired test at tools/inference-playground/tests/cli_native_payload_entry.rs. It checks both typed Machine outcomes, authentic operation/Apply lineage, payload kind and continuation for Computation, and both public stdin CLI results. No production edits, existing test/fixture/diagnostic changes or expected-output changes.

These outcomes are finite observations. Fuel exhaustion proves no divergence theorem, general laziness, effect preservation, operation eligibility or soundness.

## Authority, parents and non-goals

Use rules/design-authority.md, charter §21 Value/Computation entry clauses, and the top-level inference principles. Preserve declaration-to-construction-to-consumer correspondence and exact sources. The contribution is the §21 argument-entry branch: declaration argument effect-row presence selects force-before-publication versus inert Computation publication. §24 receiver classification stays separate.

Do not claim a theorem for all declarations, calls, handlers, effects or receivers; divergence; complete source/native correspondence; effect preservation; permission equivalence; original Simple-sub/evaluator A/B; or production readiness. All six effect-hygiene parents, method M/T/A, R85 adoption and Simple-sub/evaluator A/B remain OPEN. No semantic rule or expected output changes.

Falsifiers: declaration annotation presence does not control the native branch; Value request publishes before its argument exhausts fuel; Computation executes the argument before publication; operation, Apply occurrence/range, payload kind or continuation differs from authentic source; preparation fails; either CLI result differs.

## Pinned inputs

All hashes are from baseline 234d2b6d5:

    rules/design-authority.md e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1
    notes/design/2026-09-29-scc-intrusion-redesign-charter.md 547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed
    notes/design/2026-10-11-yulang-inference-top-level-principles.md 7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81
    tools/inference-playground/tests/runtime_control.rs 2619e4c8bb006e2d98cf81887091ae372cb1ae3731de76e7b707a97db577009c
    tools/inference-playground/tests/cli_entry_demand.rs 283e3518f8d28efedd171cacfe97fc7246225339b1c160d06b3c58944f86c8bc
    tools/inference-playground/Cargo.toml 87e77de221b023c1c9f07e90f1ce6a692a56e8bb398eca4725f4910254be0a56
    tools/inference-playground/src/lib.rs bdf996d0264e252e345c05bc77b2adcf625120281244171f0054f1d87a8d1e1b
    tools/inference-playground/src/main.rs 75b38435f4634ee35b3e14a54fb4d021b78bda834b4fd53965302a73309e0100
    tools/inference-playground/src/output.rs 04e99c5bdb562a8edb8a7e17bdcc03f7b46eaca9d8e13b20216b4dcf3032a88a
    tools/inference-playground/src/runtime/machine.rs fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46
    tools/inference-playground/src/runtime/mod.rs 64d208743793a03501a76f56bc2b511c50ed40cff3f789757a00b7d608fc846b
    tools/inference-playground/src/runtime/program.rs c2363ad42104b895519bb29a8eb9aeda545bd0176cebbd78750d3a2df90849ca
    tools/inference-playground/src/runtime/receiving.rs 8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9
    tools/inference-playground/src/runtime/continuation.rs 194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3
    tools/inference-playground/src/runtime/primitive.rs 97485b9439357497aaf3f19555b1d87eef4aabc955b3a2815f23cf49a65c0153
    tools/inference-playground/src/runtime/literal.rs 2fff177a7ba0cabb4930251e1facc8f9be701ff3ec7baa695ce4c182fa1da35f
    crates/yu-syntax/src/full_parse.rs 24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8
    crates/yu-syntax/src/statement.rs fe8ba4e144b0c3ea5c8f451dddea42f718e9c3087aa77bb81447c61a9d213797
    crates/yu-syntax/src/declaration/act_decl.rs f1af95a12df81900564c83d0aad541064eb2fff21ca41259b7a943ae3ad4fd74
    crates/yu-syntax/src/declaration/binding.rs eb9b7c9b97b999d16b364531fdcfad0bfc0cb377855e86ce6d5b825f5aba3544
    crates/yu-syntax/src/type_expr/mod.rs 2e08a49960cd4010ba39641ae509afb7cf59711c1464d3349f5f6db590ebf01f
    crates/yu-syntax/src/expression/mod.rs 05d874dd4c2874eb7b24038467c8a74b22fa6f7821a3980f3348683ad02743f1
    crates/yu-syntax/src/expression/operator_chain.rs 81db2aec4774f2cd1ddc12b64fd9206cf41cdf3eee00ed740676ffc6d7fc5669
    crates/yu-syntax/src/expression/tails/delimited_tail.rs 349fe2335e04a68da7d07803f2dd2eb185887d07bf8c9475ba09af089a76a2cf
    crates/yu-hir/src/module.rs 153a23ecaa68fd150d8bd0cc0316f3723e1cb5d98a6e3026aadef2bfd08fd907
    crates/yu-hir/src/module/local_source.rs 3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786
    crates/yu-hir/src/source_identity.rs 7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3
    crates/yu-hir/src/module/source_annotation.rs b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f
    crates/yu-solver/src/candidate_source.rs 66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c
    crates/yu-solver/src/candidate_effect.rs 6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0
    crates/yu-solver/src/shadow_apply.rs 838d862dd34fe2b2bd70c5d92c5ce9af0aa98f10f8b6a8eddf313ae798686543

## Lanes, resources and verification gate

Rev2 ceiling remains 1,800 seconds: inventory 180, pre-spec 240 (rev1 charged 180 plus one 60-second delta review), proof 600, implementation 240 (reduced by 60 before issue), final reviews 300, verification 120, closeout 120. The total remains fixed; no spent time is reclaimed, borrowed or reset. Charge the delta at its full 60-second cap if unmeasured. Astra budget zero; preserve inherited UNKNOWN reservations.

After CLEAN pre-spec and Luna's exact grant:

- Proof /root/r118_proof_lane, cap 600s. Writes only notes/theory/2026-10-19-r127-native-payload-entry.md and tasks/agent-loop/inbox/20261019-r127-proof.md. Derive finite declaration/Apply/runtime-consumer correspondence and conditional Value-before-publication versus Computation-publication postcondition; apply to both recipes. Keep effect-row, preparation, runtime consumer and bounded-outcome premises explicit. No tests/builds/CLI/probes/formatter/Git.
- Implementation /root/r118_implementation_lane, cap 300s. Writes only tools/inference-playground/tests/cli_native_payload_entry.rs and tasks/agent-loop/inbox/20261019-r127-implementation.md. One paired stdin test; no production edits or existing test/fixture/diagnostic changes. No tests/builds/CLI/probes/formatter/Git.
- After both lanes STOP, assign fresh compiler/source, spec/authority and regression reviews on frozen proof/test/handoffs. Only after all three are CLEAN run exactly once:
 
    CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-playground --test cli_native_payload_entry -- --exact native_operation_payload_role_controls_publication --nocapture

No retry, alternate command or extra probe/build. Closeout preserves all H/A/E/B and parent gates OPEN, and distinguishes fuel exhaustion from divergence. Luna alone integrates and non-forcibly pushes the reviewed paths. After this bounded §21 result, return to method/role source correspondence before repeating §21 entry or handler work.

## Rev2 delta and pre-spec boundary

Rev1 pre-spec found one minor: the two stderr phrases omitted the terminal LF added by `main.rs` through `eprintln!`. Rev2 changes only those exact output-byte statements and reallocates 60 seconds from the unissued implementation allowance to one delta review. All source bytes, ranges, declarations, authority, output expectations apart from explicit final-LF spelling, owner pins and all other resources stay fixed.

The delta review checks that both literals end in exactly one LF, match the pinned `main.rs`/`lib.rs`, and introduce no other changed expectation or dependency. Stop before producer grants if the review exceeds 60 seconds or finds anything beyond this correction; no renewal or additional repair is authorized.

Review exact owner pins, authentic CallTail ranges and diagnostics, source declaration/LocalSource/native-consumer relation, candidate preparation conditions, budget and review/test gates. A wrong range/diagnostic, missing owner or new material premise stops this candidate; no producer grant exists yet.
