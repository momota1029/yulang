# R108 closeout: exact method/role source entry observed

Status: **CLOSED_CLEAN_FINITE_SOURCE_ENTRY**.

The exact R100 `SecondInt` source entered one authentic `ParsedFile`, and the
test connected its original declaration/member syntax to retained positions
from the same parse. The exact source was 148 bytes with SHA-256
`fb54857e70924c178842692d7cce1a9c35b7c2a55bceab78710889b913d7dfcb`, with no
final LF.

The test observed the `RoleDeclaration` and `ImplDeclaration` roots, connected
the implementation member's original ancestry to the associated same-parse
ImplDeclaration, and compared the implementation subtree's original raw child
sequence—including punctuation, whitespace and other tokens—with retained
`Position` relationships. The checks cover parent, raw child order/ordinal,
node/token status, kind and byte range. They also distinguish the original
`selected` formal pattern from the separate body `selected` occurrence by
syntax node, parse key and retained position.

This discharges R100's **finite `R100-ENTRY` premise for this exact fixture**.
It does not establish a universal parser-completeness theorem. Applying the
reviewed R100 consumer case analysis, the first remaining executable-member
premise is **R100-P2-MEMBER** at the HIR `plan_root`/`lower_plan` to LocalSource
boundary. Executable parameters, annotations and body environment are still
unproved.

## Frozen evidence and reviews

- R108 contract SHA-256:
  `ebe3bd813d0959c84f6eb969e610654aa2f031ff99cd0222bcdd9a3dc951e547`.
- Test file SHA-256:
  `ea90e8ef445aae1155e28e10356068dfaecb8b2bc430d5bf6f18094acee21e1a`.
- Test-only implementation handoff SHA-256:
  `fd853ccabacde019d65065a7dbb3ca9c53690fcc66ebd39a76ed17f2faabdce2`.
- Pre-edit spec delta review: CLEAN at
  `tasks/agent-loop/inbox/20261019-r108-spec-review.md`.
- Post-output spec review: CLEAN at
  `tasks/agent-loop/inbox/20261019-r108-post-spec-review.md`.
- Compiler/source review: CLEAN within the pinned scope at
  `tasks/agent-loop/inbox/20261019-r108-compiler-review.md`.
- The sole authorized command ran exactly once:

  ```sh
  CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-hir --lib tests::shadow_method_role_source::exact_role_impl_member_source_reaches_original_occurrences -- --exact --nocapture
  ```

  Result: exit 0; **1 passed, 0 failed, 133 filtered**, finished in 0.00s after
  a 3.22s build. One pre-existing `dead_code` warning for
  `replace_admission_root` in `crates/yu-hir/src/module.rs` appeared. There was
  no retry or other test/build/runtime command.

R106 and R107 remain preserved as failed `NOT_RUN` correction packets; their
reviews motivated the later assertions and final two reference fixes. Their
failures are not hidden by this successful R108 outcome.

## Parent boundaries and breadth

The following remain OPEN: executable HirParameterIds; method lookup and
selection; lexical resolution of the body `selected`; body checking; ordinary
receiver-first Apply generation; candidate/runtime admission; dispatch; result
`2`; R100 P2/P3/P4 beyond the finite entry premise; original Simple-sub/evaluator
A/B, F1/FK1 and foreign-continuation obligations; R85 adoption; semantic
approval and production promotion.

The parent goal continues to balance six independent effect-hygiene fronts,
proof-backed method/role behavior and early runnable ordinary/effectful source
execution. R105 remains the bounded wrong/sibling-permission CLI observation;
this method/role source test does not resolve any effect front. At closeout the
next slice should rotate toward an under-covered effect-hygiene front or the
ordinary/effectful runnable path instead of extending this exact source-entry
test.

No production source or expected output changed. All producers and reviewers
stopped. Luna owns current-state update, source-gate adjudication and any Git
checkpoint.
