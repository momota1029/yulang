# R25 HIR caller-evidence retention handoff

Sprint: `caller-evidence-source-binding-20261018-r25`, contract rev2,
SHA-256 `586f89e2a6cb4f0d6913e6e57c0d36cb625cd70e9d58ef214846c1db9796bf97`.
Assignment: `R25-HIR-RETENTION-IMPLEMENTATION`, handoff rev1; Luna/root author.
Baseline `f7edada810d94a320fc7d5a3e785e407a0bfb01c`; source implementation
branch baseline for this code was `15eb31c99` after reviewed design rev2.
Outcome class: implementation candidate, independent implementation review
completed CLEAN. No production or semantic-authenticity claim.

## Behavior implemented

`SemanticImports::with_caller_evidence` retains an opaque owning
`'static + Send + Sync` payload with parse-root key, exact module identity and
an exact source key. Lowering rejects foreign parse/module bindings and checks
that the anchor is an admitted top-level HIR binding declaration. The resulting
`HirModule` owns the binding. `SemanticImports::empty()` remains unbound.
Read-only accessors expose keys/module and concrete payload type only.

This is structural transport. It does not validate payload contents, semantic
authenticity, scopes, dependencies, same-fiber interpretation, `j0`, `a0`,
license/incidence, phase actions, `JointWF`, or world validity. The first API
does not bind effect/operation annotation anchors. `HirModule` keeps its
existing structural equality behavior; evidence correspondence is queried
explicitly. Candidate and runtime retain their existing HIR owner, but no new
solver/runtime semantic consumer was added.

## Frozen paths and hashes

```text
c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a crates/yu-hir/src/module.rs
91cbf982d8281af8c364d1e07e7f425b8bf2a71467af54e1012cbc4171f1dd4e crates/yu-hir/src/lib.rs
b9b3aa5f0d1a3e6783d2e8b53e2d4edd13b5c4ac43538d71216662bcd19399d1 crates/yu-hir/tests/semantic_import_binding.rs
b6a51aa9b4cd716382f4b180a0c5a348dc1d84ced263d08a461b727b6b344df5 notes/theory/2026-10-18-caller-evidence-source-binding.md
9a66dbd7499c95f620b6173699be57d829ca10aa974c5423beb7e4cbcc4a6024 tasks/agent-loop/inbox/20261018-caller-evidence-source-binding.md
```

Proof artifact/handoff direct dependencies match their recorded baseline
except for the two expected concurrent HIR source changes noted above. The
conditional proof does not depend on those changed bytes. Source/native
applicability for the latest HIR implementation was **NOT_CHECKED** by the proof
author and is part of this fresh review.

## Checks

- `cargo test -p yu-hir --test semantic_import_binding`: **5 passed**.
- `cargo test -p yu-hir`: HIR unit tests **130 passed**; in
  `simple_module_resolution`, **20 passed / 2 failed**. Both failures were
  reproduced on the clean baseline worktree at `f7edada81`:
  `admitted_parameter_header_keeps_lambda_for_unresolved_and_unsupported_bodies`
  and `indented_and_unsupported_bodies_stay_error_values_without_nested_lowering`.
  These failures predate this change and remain unresolved.
- `rustfmt --edition 2024 --check crates/yu-hir/tests/semantic_import_binding.rs`:
  passed.
- `cargo fmt --package yu-hir -- --check`: failed on broad pre-existing format
  drift across the package (including unchanged portions of `lib.rs`); no
  package-wide formatting rewrite was applied. `git diff --check` passed.

Tests establish structural identity/owner retention only. They do not prove
semantic validity or parent closure. Compiler warnings were the existing
unused `AssociationProvenance` fields and `replace_admission_root` function.

## Parent and remaining premises

Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains
**OPEN/closure0**, original conditions **0 -> 0**. The conditional proof says
retained allocation/key identity composes, and stable semantic applicability
needs independent authenticity plus stable interpretation. No authentic
caller context is supplied by current `prepare`, which still uses `empty()`.
Original operation/member/signature correspondence, guard/license formation,
phase-current actions, full F1/FK1, soundness and principality remain open.

Next: fresh independent review of the frozen proof and HIR implementation,
then Luna adjudication. Do not promote the payload to semantic evidence. Any
operation-annotation or solver/runtime consumption requires a separate exact
lease and review.

Writer state: Luna code frozen for review; no descendant writer. Requested
model/effort Luna/high; effective metadata UNKNOWN. Proof lane stopped with
420/720 seconds charged; Astra 0. Implementation and proof writers are stopped.

## Independent review and adjudication

Fresh `compiler_referee` `/root/r25_implementation_review` reviewed the frozen
proof and implementation snapshot and returned **CLEAN**, with no blocking,
major or minor findings. Its seven contract/design/proof/handoff/implementation
hashes matched. The review independently checked the source/native retention
path, declaration catalogue, same-parse/module enforcement, `Send + Sync`,
structural equality boundary and semantic-authenticity exclusions. It did not
run tests or certify original theorem closure. Luna adjudication accepts the
HIR transport implementation within this exact scope. Parent conditions remain
0 -> 0; caller-authentic introduction and operation/member/signature
correspondence remain OPEN.
