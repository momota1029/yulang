# Frozen handoff: ordinary-hir-application-implementation

Sprint: `ordinary-hir-application-admission-implementation-20261017`, revision 3.
Contract SHA-256: `47d160176e72306e150675b2daf6e548d74e1e8d3dfc794c8dbf40ac0ba674e2`.
Adjudication baseline: `1ed35f0cbff1e05fd5c3de7476224e17e9de6d99`.
Source dependency baseline: `5fbceb68d`.
Adopted design rev4 SHA-256: `2e61e2acb1a8981bb78592accc48207a24a5cc4c75278e100f63eb960acfeea3`.
Assignment-ID: `ordinary-hir-application-implementation`, handoff revision 1.

Parent: the original inference/execution goal with original A/B claims,
quantifiers, source domain and source/native correspondence unchanged. Original
theorem conditions discharged: 0. This work supplies no semantic Call, source T,
MODEL, soundness, principality, termination or parent closure.

Role/worker: Luna implementer lane, `/root/ordinary_hir_application_implementation`,
`current-session`; requested `gpt-6-luna` / high, observed model/effort UNKNOWN.
One author, no descendants. Active time is conservatively estimated at about
1,400s of the 1,710s cap; no renewal requested. All writes cease with this handoff.

Exact leased paths and hashes at freeze:

```text
crates/yu-hir/src/module.rs
crates/yu-hir/src/source_identity.rs
crates/yu-hir/src/shadow.rs
crates/yu-hir/tests/ordinary_application_admission.rs
crates/yu-solver/tests/research_accepted_call_vertical.rs
tasks/agent-loop/inbox/20261017-ordinary-hir-application-implementation.md
```

Frozen artifact SHA-256 values (handoff hash is computed after this edit):

```text
module.rs b4f89fe7c5dc8a3f4260fbe3dd2b173546e07385fbd8dbb38275f3625217127f
source_identity.rs 7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3
shadow.rs 460c813cb0d2e21565df011b1d816abbc2b180cef13797a1b7b453e9ee413f66
ordinary_application_admission.rs 38b822bc801c0538878cc5fb3f929f55dee784e2377f4bc75f03679ea9872492
research_accepted_call_vertical.rs 9c3dea05d11c49bae09520d5f6fe27430f1706185232daf2cf8e8d801a42d71a
```

The author reused the frozen rev4 construction/key/identity/carrier lemmas and
the accepted-call source audit. Baseline owner hashes were rechecked before
writing: `module.rs` `2e0c579a525efd5ac4c7ce0f06189c568ed46c7382d4576698a0b8d846c2228e`,
`source_identity.rs` `aa97bc34be51644cf944b2813af47ad9243a8eb270850eeb6df34b9cddb3b3a2`,
`shadow.rs` `2dffd7fd6542eed9fd3346e0672e76197c248be9c84334f341c4d612234b7ee9`,
and vertical test `78fd0d4c38df86def4cd4aefb37e164f71269eb58cd9a53b370bc42e42f9a963`.
The proof candidate's earlier resource-linear claim was rejected after the
`E_m` counterexample; implementation uses adopted `O(V+E+R)`, worst-case
quadratic-in-V accounting. No Simple-sub bypass was restored.

Outcome class: implementation draft, pending independent applied review and
execution. The ordinary `lower_module` path now has a private associated-HIR
preflight for Atom/Group/Apply shapes, stages operand-resolution diagnostics
once in source order, keeps rejected/recovery shapes on the old whole-body
refusal, and defers canonical child occurrences until after ordinary carrier
formation. It checks exact source keys, preserves a same-key body-root mapping,
rejects a conflicting root mapping, stages descendant occurrence mappings
through `append_stage`, and publishes no module on identity/reservation failure.
Apply error lists are reserved and materialized once; Group contributes no
copied list. Checked counts cover node/child growth, occurrence ordinals,
cumulative physical reference count R and reference bytes. `ErrorSink` reserves
error and diagnostic destinations before appending either record. Recursive
child boxes use a local fallible allocator helper; empty lists retain zero error
references and nonempty list allocations correspond to nonempty Apply lists.

The opt-in local-source/shadow lowering producer remains unchanged. The shared
inventory now accepts ordinary Apply with an empty error list when its
occurrence/source identity is authentic; existing opt-in Apply still requires
valid attached error IDs. No solver semantics were edited. The accepted-call
vertical fixture now enters via ordinary `lower_module` and retains its
candidate-only propagation, exported-definition, source-authenticated fresh-use
and source-call observations, with a carrier-count assertion.

The focused admission test source covers the fixed source, ML and CallTail
forms, Group(Atom), Group(Apply), nested/root Groups, unresolved and ambiguous
operands, unsupported tuple and recovery refusal, carrier-before-child ordinal
ordering, and error-list reference counts. Its expected physical counts are:

```text
clean 2-Apply spine: R=0, reference bytes=0, nonempty Apply-list allocations=0
unresolved 3-atom/2-Apply spine: R=5, bytes=5*sizeof(HirErrorId), allocations=2
Group-wrapped same spine: R=5, bytes=5*sizeof(HirErrorId), allocations=2
```

An internal identity collision test checks conflicting-root rejection and that
`append_stage` leaves the prior mapping unchanged. These are authored assertions,
not run observations. No Cargo, compiler, build, test, parser probe or whole-tree
formatter was run. `git diff --check` was CLEAN at the earlier static checkpoint;
it must be repeated against the final bytes. The two prescribed Cargo commands
remain held for applied reviews and the pre-run regression review.

Source -> constraints -> propagation -> consumer correspondence: ordinary HIR
constructs and source-authenticates application occurrences for the fixed
source. The vertical's `CandidateInference` is a private feature-gated candidate
path and does not establish standard inference. The exact first standard
consumer remains `crates/yu-solver/src/lib.rs`,
`ConstraintBatch::collect`/`collect_mode`, where Apply/Group stays Error and
`ApplicationTypingRuleUnresolved` is observed without Call constraints. The
source-typed callable/context constructor and native source/result correspondence
remain open owners; this lease contains no solver or native implementation path.

Parent application of the frozen Astra candidate: only its structural
operand-occurrence/key/identity/carrier conjunct can be applied after fresh
review. Exact source-key mapping is taken from the parse-owned node table;
canonical child identities follow unchanged carrier identities. The frozen
candidate proof and its own handoff remain unchanged and independently reviewed
only as recorded in sprint state; this implementation author does not certify
either artifact.

Mutual TODOs:

- `HIR-APP-IMPLEMENTATION-REVIEW-1`, Luna: freeze this diff and dependency
  manifest, then obtain sequential fresh compiler, spec and architect review;
  regression auditor reviews the exact pre-run diff/commands. Falsifiers include
  root Group ownership, equal-text distinct keys, tuple punctuation, rejected
  recovery before operand resolution, dense error references and post-carrier
  ID order. Only after CLEAN reviews run the two frozen Cargo commands once each.
- `CALL-SOURCE-NEXT-1`, standard solver owner: connect these exact ordinary HIR
  incidences to the independently typed source interface and the actual standard
  constraint constructor, propagation and consumer while retaining original
  context/provider/response/future premises. First executable open owner is
  `crates/yu-solver/src/lib.rs` `ConstraintBatch::collect`/`collect_mode`;
  required output is source-to-constraint-to-consumer correspondence, falsified
  by any Apply that reaches this route without its approved source interface.
  This is outside this writer's lease and remains OPEN.
- The proof/source owner must apply the structural conjunct back to the original
  Call/source bridge and name its exact first typed-source/native adequacy
  premise. F1 and FK1, original A/B, N-Transport, semantic Call, soundness,
  principality, termination and production gates remain OPEN.

All authored paths are listed above; no scratch/generated paths. Worker state:
STOPPED after handoff freeze, no descendants or unresolved writer leases. Review
and execution remain pending. Next in-envelope step: independent applied review
of the frozen bytes, then the prescribed single-owner checks; do not alter the
source domain, expected outputs, diagnostics or standard solver semantics to
make them pass.
