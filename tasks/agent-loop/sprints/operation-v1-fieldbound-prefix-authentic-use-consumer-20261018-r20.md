# R20 — FieldBound prefix formation and authentic-use consumer

## Fixed parent, outcome, and baseline

Original parent remains `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`:
original quantifiers, source/native correspondence, required principality,
Call, soundness, and termination requirements are unchanged. Parent starts
**OPEN / closure 0**. A candidate v1 result is not automatically a proof of the
original receive construction.

R19 closeout: `tasks/agent-loop/sprints/operation-v1-local-install-use-lineage-and-capture-20261018-r19-closeout.md`.
R19 source/proof characterization commits `6748039fa` and `118375dce` are CLEAN;
its runtime checkpoint is commit `8e1ad99fd`. R19 consumed 3900/3900 seconds;
no carryover.

Before/after target for this sprint: establish the earliest owner-valid route
from source-derived q/m0/FieldBound evidence to the authentic local-use capture,
its own FreshUse mapping, and that use's native edge/drain/ack; or freeze the
first exact obstruction and a smaller parent premise. Preserve early q-view
preparation and shared anchors. Never retroactively add evidence after capture,
borrow a sibling use's edge/ack, infer identity from names/types, or turn tests
into theorem closure.

In parallel, resolve the R19 runtime gate at its first failed boundary:
`runtime_resume.rs` parsed cleanly and HIR lowering returned, but
`hir.errors().is_empty()` failed before candidate solving. The exact error
IDs/kinds/attachments were not recorded. Compare them with the existing
canonical owner-aware admission in `CandidateInference::solve_mode`; do not just
remove the zero-error assertion. The existing R19 runtime path is frozen and
compiled; its local-g runtime and sibling test were not reached.

## Pinned baseline and dependencies

Git baseline: `8e1ad99fd` on `research/simple-sub-intrusion`. Exact relevant
workspace pins:

```text
98b00634966c692f5c8f7ab0b3312b168688ce5a46694efee117a77854c07d8e tasks/agent-loop/sprints/receive-negative-pair-construction-20261017.json
276979eccec49396c6799b96ca1e0277c6108dc2fd1fe487a52e4565cff6ed54 notes/design/2026-10-18-operation-v1-source-completion-and-consumer-r6.md
1d63c2c9740bdc47e4c5e3671c8e4fb524a14edeaa600baa91af0e1cf282ed73 notes/theory/2026-10-18-fieldbound-capture-order-and-consumer.md
d2952e5bba7fbae3da0c89ef37de89a8773111610bdc2c5b6aa42cdb743144c2 notes/theory/2026-10-18-fieldbound-freshuse-source-falsifier.md
66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c crates/yu-solver/src/candidate_source.rs
03b44d0f8280c1ae79f66b5528f1bd0b0ffebac46b312ef7ffce605f702f48dd crates/yu-solver/src/candidate_scheme.rs
6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0 crates/yu-solver/src/candidate_effect.rs
5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb crates/yu-solver/src/shadow_apply.rs
7c3e163c5ad710f1eb7f44ab21018fe2788f7334390f1afe6f432d8212f3f34a crates/yu-solver/tests/candidate_operation_catch.rs
42f89dcf5fa6d7095db1e220c89308a2a35f4e74b05c3e8821d4fb2e3e32b0ca crates/yu-solver/src/candidate_context.rs
e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479 crates/yu-solver/src/candidate_call.rs
7a57a93481095c6e7d4b8781810b1a5aa0d174e41ede29ac3f2b2b96bce10b0c crates/yu-solver/src/candidate_intrusion.rs
fc0d948d884a406746066f3df8db257d5c6686505166b330bef839a9b9e2f35d crates/yu-solver/src/candidate_extrusion.rs
2300400e87d0a487225f207d414ac71fa4f21c6f80279fea4f793e43c7809aee crates/yu-solver/src/lib.rs
60e91c9a51394b04af42b3ec7c284062b34fcd9faa4ea79c35b4ae58aaf460ed crates/yu-hir/src/module.rs
6ea0914a11a4a05d6dde8d63c413cfd42fb887596b3315d998848d502a91715a crates/yu-solver/src/shadow_initialization.rs
484967c20c829344a8abe3aa583f6a65e715fb927b8d6b0ba816f0cc6291ad11 tools/inference-playground/src/runtime/program.rs
fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46 tools/inference-playground/src/runtime/machine.rs
ea4579c34b0c01a8e109a6b26cb426ac1fb337a87d7ff4af66a4969010a784db tools/inference-playground/tests/runtime_resume.rs
```

Any pin drift returns to Luna before that dependency is used or written.

## Productive lanes and exact leases

### A. Constructive source/native lane — Sol, 720 seconds

Exclusive output lease:

- `notes/theory/2026-10-18-fieldbound-prefix-and-use-construction.md`
- `tasks/agent-loop/inbox/20261018-fieldbound-prefix-and-use-construction.md`

Trace actual action scheduling and owners from source construction through
early q/m0 preparation, FieldBound formation, installed root, per-use capture,
all relevant FreshUse remaps, and that use's native edge/drain/ack. Prove the
prefix premise or identify its earliest missing owner/operand. Include sibling
use isolation, shared anchors, and exact provenance. Apply every supported
claim back to the original receive parent; clearly label any v1-only premise.
No source/solver edits. A proof that assumes the field incidence already exists
before capture is not completion.

### B. Runtime HIR admission gate — Luna implementer, 300 seconds

Exclusive output lease:

- `tools/inference-playground/tests/runtime_resume.rs`
- `tasks/agent-loop/inbox/20261018-local-g-hir-admission-gate.md`

Keep the valid-source sibling and runtime lineage gates. Record actual HIR error
IDs, kinds, and attachments/owners, then compare each against the exact owner-
aware paths accepted by `CandidateInference::solve_mode` and source declaration
placeholder ownership. Preserve rejection of any unowned or wrong-kind error.
Do not change HIR/source semantics, solver admission, or runtime program/machine.
If an error cannot be shown to be an already authorized placeholder, stop at
that owner; do not waive it. Freeze before verification. Independent review is
required before the diagnostic/focused command. Runtime evidence is conditional
on unchanged static candidate acceptance and a completed local-g receipt.

### C. Conditional native implementation — Luna/high, 1200 seconds

Write authority activates only after Luna reviews lane A and a fresh independent
design review returns CLEAN. Exact candidate code/test lease:

- `crates/yu-solver/src/candidate_source.rs`
- `crates/yu-solver/src/candidate_scheme.rs`
- `crates/yu-solver/src/candidate_effect.rs`
- `crates/yu-solver/src/shadow_apply.rs`
- `crates/yu-solver/tests/candidate_operation_catch.rs`
- `tasks/agent-loop/inbox/20261018-fieldbound-prefix-use-implementation.md`

Implement only an owner-valid prefix/capture/use-consumer path permitted by the
reviewed design. Do not reorder evidence past a capture or consume another
FreshUse's receipt. This is candidate research, not production promotion. If a
new source meaning, solver schema, or language semantic choice is required, do
not silently choose it: freeze a concise bridge-rule proposal with its original
rule, consistency obligations, and falsifier for independent review, then ask
Luna/user to choose before integrating that semantic choice.

### D. Primary design and integration lease

Luna owns `notes/design/2026-10-18-fieldbound-prefix-and-use-implementation.md`,
`tasks/agent-loop/current.json`, review assignment, test execution, integration,
and Git. The design note must name whether implementation is justified by
current rules or depends on a reviewed but not yet adopted bridge rule.

## Review, verification, and resources

A fresh reviewer (not lane A's author) reviews the design before lane C writes.
A compiler referee reviews frozen native code and exact runtime gate changes;
no author self-certification. Luna owns all Cargo processes, one at a time.
Focused candidates:

```text
cargo test -p yu-solver --features shadow-apply-candidate --test candidate_operation_catch
cargo test -p yu-playground --test runtime_resume
```

Run only the exact target(s) authorized by the reviewed frozen result. Any
diagnostic probe must preserve the error assertions and precede an optional
final target only if the probe shows solely owner-authorized placeholders. No
retry on changed bytes without a fresh review.

Total cap 3600 seconds, fully reserved/charged at issue, Astra 0:
proof 720; runtime HIR gate 300; conditional implementation 1200;
independent design/code reviews 720; focused verification/integration 660.
No R19 carryover. Stop on cap, a genuine unowned HIR error, a counterexample,
source/solver semantic choice without selection, dependency drift, or the
focused targets' completion.

Original parent conditions close only when the original source/native
quantifiers and all gates are actually proved. Green candidate tests or a new
bridge proposal alone close zero conditions.
