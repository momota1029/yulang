# Sprint minimal-cut-and-accepted-source-vertical-20261017 — reduce one original-goal cut and prove an accepted source path

Status: ACTIVE, Luna admission in progress. No semantic adoption.
Branch/baseline: `research/simple-sub-intrusion` / `d33b01033625ef69d1d844e6400191dd84e73b2f`.
Contract revision 1; SHA-256 recorded in `current.json` after freeze.

## Original outcome and success evidence

Parent goal: implement Yulang type inference and execution with proofs. Preserve
the original Simple-sub A/B quantifiers, source domain, native correspondence,
principality and termination claims. This sprint first constructs a compact,
source-located dependency cut for F1/FK1, N-Transport, Call, soundness,
principality and termination. It separates proved-within-scope, conditional,
semantic-choice and implementation/verification-resolvable claims. The cut is
relative to the pinned evidence below, not a global minimality theorem.

The sprint outcome is one of: (a) a genuinely smaller named premise in an
original obligation, established by applying a proof-resolvable result to that
obligation, plus a reviewed accepted-source-to-fresh-use regression; or (b) an
exact semantic decision at the admission seam if every relevant cut requires a
new meaning. A proposal, test, note, or conditional wrapper alone is not
progress toward closure.

The candidate source is the existing fixture program:
`my id x = x; my apply f = f 1; my answer = apply id`.
It is only a candidate until the test proves zero parser recovery, zero HIR
errors, successful ordinary `CandidateInference`, and source-authenticated
fresh-use/export observations.

## Evidence boundaries and inputs

Original theorem/source anchors (all remain open unless individually discharged):
F1/FK1, N-Transport, Call, forward soundness, principality, termination, and
the A/B and source/native parents. The task decomposer must state exact locators
and status, and must distinguish a located statement from a proved theorem.

Frozen direct dependency pins:

```text
tasks/agent-loop/current.json 5ab095a680ee71188eb93fd7b320adb8ee4ad72ec9e2dcb4e619d71dc9a3ec8f
rules/goal-driven-sprints.md 729fed88535671ebd128f0c70fd8618d2a2f7cb7df3a458698799fac9d9f1789
rules/design-authority.md e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1
rules/testing.md 829eb0c6b6b10db902f0329e3117351b92dba9ca1480ef5722ccd6d2fabbb524
notes/design/INDEX.md 63f272e168746562e72309131d76e0db7b25db6b70b4cd5d9d654550358d4cea
notes/design/2026-10-11-yulang-inference-top-level-principles.md 7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81
notes/design/2026-10-17-operation-response-signature-introduction-proposal.md ed71da1c0d6d4cfb849e1c75bccfc2ab3262ac2ee233e4f8cef27e71f1fced18
notes/theory/2026-10-17-operation-signature-default-source-qualification.md da32c75beae3a52ee64eecfdc3ef7f30c3406746b8600f046fe1aa79bf8b46a1
notes/design/2026-10-17-operation-response-instance-witness-lifecycle-proposal.md 1bfcf65c04a1f9bd9f10d231db617986a766cf923798e1e49b503f0613e667ad
notes/progress/2026-10-17-operation-default-and-instance-lifecycle-closeout.md dc205f17b466b3f467d0ee9b41cc4699ec5f7c5d0f1fc17e809993842518e237
notes/progress/2026-10-06-principality-proper-domain-view-boundary.md c9175bdb695efbbc110a2f0b2122583284b6f02ac617e08d11634e200e472591
notes/theory/oracle-inference-document-audit/directed-weights-termination.md 73fe03015e4b202fe69d52df9ad3f54111c519cde653bf47e8b4d993a77e8eb8
notes/theory/2026-10-13-direct-transport-admission-association-proof.md b1b4e9ffd814af2faa842c56cbc8b7ece99ba2ddd63566bddc683e0649953fba
notes/theory/2026-10-12-intrusion-association-proof.md 214fe6973b05c395d294598b5d5a755e12f64d8e3cd33e60f86e88db46d9616b
notes/theory/2026-10-13-source-check-positive-transport-proof.md 1d4605b5c3ce321eccc8fef3c87bd38d5715e2ed0b28dda6d2abbfc3a32ee518
notes/theory/2026-10-16-native-outer-use-source-witness-transport.md 90a02bdf7a6a2e241bce968e77df12b67f29419cf9c7b6c78f8965636f36ba23
crates/yu-hir/src/module.rs 2e0c579a525efd5ac4c7ce0f06189c568ed46c7382d4576698a0b8d846c2228e
crates/yu-hir/src/module/source_annotation.rs b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f
crates/yu-hir/src/module/local_source.rs ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5
crates/yu-syntax/src/full_parse.rs 24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8
crates/yu-syntax/src/lib.rs 18709b87b1b761374b5b81f90fcbf37d001fd7d981597e889aef05ad3f230f93
crates/yu-solver/src/shadow_apply.rs bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf
crates/yu-solver/src/candidate_source.rs efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38
crates/yu-solver/src/candidate_effect.rs 11a1477ff2c35c03dccb70bdc6121d89d3ced9fadb1921cb8cf8cd5c093b07fb
crates/yu-solver/src/lib.rs 2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f
crates/yu-solver/tests/candidate_lifecycle_retirement.rs 7b40929ee90485137a529e67c37b10f82f8e4a1c35f8238b704e3f69c486a822
crates/yu-solver/examples/research_source_registration.rs 10ea5f2c6db7c9d093d86780dbeb217d7eca11332e99a4d1ec40f4753f544e7c
crates/yu-solver/Cargo.toml 7a599e95800c67ca4688b0f91917609345a252aae6d2ea6cd0f413eb1c07893c
```

The index is navigation only. The current.json pin above is the prior sprint snapshot, for startup reconciliation only; it does not certify live worker state. Each cited theorem/spec must be read at the pinned
bytes before reliance. Existing October 17 response/lifecycle proposals remain
unadopted; C-OMIT is unanswered and unadopted. The decomposer may not recommend
semantic adoption as if it followed from the code.

## Lanes, exact leases and admission

Phase 1, read-only, max 180s: `task_decomposer` maps the graph and reconciles
OPRESP-DEFAULT-1/ENTRY-1 with existing rules. Outputs:
`notes/progress/2026-10-17-original-goal-minimal-cut.md` and
`tasks/agent-loop/inbox/20261017-original-goal-minimal-cut.md` (Luna-owned
write-back after the worker's report). Identify the smallest evidence-backed
cut in the graph, its original parent, first missing premise, source owner,
falsifier, and whether existing authority settles it.

Luna admission seam: freeze the DAG and select one proof-resolvable cut. If
every applicable cut needs a semantic choice, stop before proof/example
admission and provide the choice, compatibility and spec impact to the user.
No conditional-wrapper packet.

After admission, one bounded `astra_prover` assignment (medium, <=900s) may
construct across related stages and apply its result to the original parent.
Lease: `notes/theory/2026-10-17-selected-source-vertical-correspondence.md` and
`tasks/agent-loop/inbox/20261017-selected-source-vertical-correspondence.md`.
Keep original quantifiers and source domain.

After admission, one Luna/high implementation assignment (<=480s) builds a
reversible source example and a regression using only existing APIs. Exact
leases: `crates/yu-solver/examples/research_accepted_call_vertical.rs` and
`crates/yu-solver/tests/research_accepted_call_vertical.rs` and
`tasks/agent-loop/inbox/20261017-accepted-call-vertical.md`. No library edits,
existing fixture edits, expected-output edits or semantic choices. Regression
requires zero parser recovery, zero HIR errors, successful ordinary
CandidateInference, and source-authenticated fresh-use/export observations.
An example is not proven executed by the test target.

One exact verification, <=120s, after pre-run regression review:
`cargo test -p yu-solver --features shadow-apply-candidate --test research_accepted_call_vertical`
No retry. Record target execution precisely. Known formatter/CI failures are
reported separately from this new test's result.

Fresh post-run regression review is required. Authors and reviewers never
overlap. Existing UNKNOWN leases remain quarantined; authors run sequentially
within the cap of six occupied/reserved identities. Luna owns all admission,
review assignments, adjudication, central state, staging and Git.

## Resources, non-goals and stop

Sprint envelope 2400s: decomposer 180; Astra 900; implementation 480; reviews
480 (compiler 180, spec 120, regression 180 split pre/post); coordination 120;
one Cargo command 120; reserve 120. Retire unused time; no rollover. One Astra
at a time, no worker descendants. No production promotion, theorem weakening,
semantic adoption, fixture or expected-output edits, or broad CI cleanup.

The implementation slice must advance accepted source through generation,
accumulation, propagation and fresh use. If source admission fails, no
acceptance claim; if the currently approved APIs cannot evidence a stage, record
the exact owner and keep that gate open. Parent theorem closure requires an
independently reviewed result applied to its original obligation.

At closeout report only (1) original unresolved premises genuinely discharged,
(2) new implementation/test behavior established, (3) remaining unproved item
and the next single cut. Tests and proposals do not count as theorem closure.
