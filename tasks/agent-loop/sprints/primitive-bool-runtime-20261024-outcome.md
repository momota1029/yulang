# PRIMITIVE-BOOL-RUNTIME-20261024 — outcome

Status: **IMPLEMENTATION PASS, independently reviewed, committed and pushed**.
Baseline: `e80b83f0f81e3859dfd848f768f7d76d6f98e8d6`.
Contract revision 1 SHA-256:
`c85f07b09d0072eee08acb07bce60ef004769463a5b67bfd3fb967d7ad3c933a`.
Factual correction under contract revision 2:
`primitive-bool-runtime-20261024-rev2.md`.
Author: `/root` only. No code-writing descendants.

## Result applied to the source-to-runtime path

The pinned Yulang2 boolean primitive family now has an end-to-end candidate
path in Yulang3:

1. `source_annotation::pinned_primitive_op` recognizes only the exact
   `builtin_op` names `bool_eq`, `bool_not`, and `bool_to_string` and carries
   their typed `PinnedPrimitiveOp` identities onward.
2. Candidate source collection interns the Boolean/String leaves. The source
   primitive signature owner constructs `bool -> bool`, `bool -> bool -> bool`,
   and `bool -> str` with empty effect rows. Its primitive-annotation exposure
   also checks the exact primitive occurrence, ground types, and argument
   count, so these operations can be used through their annotated standard
   library bindings.
3. `Instruction::Primitive` retains the source identity. The runtime uses
   arity one for `bool_not` and `bool_to_string`, arity two for `bool_eq`,
   applies boolean negation/equality, and returns lowercase `true` or `false`
   from `bool_to_string`. Existing argument-kind checks reject non-Boolean
   runtime values; no coercion was added.

This matches the frozen Oracle's `lib/std/bool.yu` and primitive type/evaluation
owners. The Oracle uses curried `bool_eq`; both arguments are evaluated before
the primitive applies, with no short-circuit behavior. The ordinary local name
resolution path remains authoritative before primitive recognition.

## Verification and review

Read-only source audit: `/root/proof_implementation_referee` confirmed the
source signatures, `BinaryPredicate` currying, pure effect rows, runtime
meanings, and existing partial-application flow. The assignment was interrupted
after its handoff; it made no file changes.

Independent implementation review: `/root/source_permission_review` returned
**PASS**, all four supplied hashes matched, and no blocking, major, or minor
findings were reported. It checked source identity, candidate leaves,
primitive-annotation type/arity correspondence, curried signatures, runtime
application, canonical Boolean strings, and failure for mismatched runtime
values.

Checks:

- `cargo check -p yu-hir -p yu-solver -p yu-playground` — PASS. Existing
  unrelated warnings remain in `yu-hir` and `yu-solver`.
- `git diff --check` — PASS.
- `python3 tools/agent_sprint.py check` — STATIC CHECK PASS; this is not a proof,
  live-worker audit, or independent review.
- No tests were added or run, and no evaluator probe was run.

Frozen implementation SHA-256 values:

- `crates/yu-hir/src/module/source_annotation.rs`:
  `b7094dac5b277cf2efe39bd33d4f0d2301071b6ca96260887822575663dbcd89`
- `crates/yu-solver/src/candidate_source.rs`:
  `70c29b9e489b6ea17ecbee6610c0b256feacb92c90f87ba6c452b56cf0daf0a7`
- `crates/yu-solver/src/candidate_effect.rs`:
  `d7bebf24a823ccd56ceb200ff6e9915e4b81c4fad0e4ad77d6ad6d5043e454f9`
- `tools/inference-playground/src/runtime/machine.rs`:
  `30c83d44623ceae1951091745bf15d6025eca2b64bfbc33ae2bf31b5f8118b75`

Direct oracle dependencies were read from commit
`a58eefc31e22141574b6f20c6a5748151c6d79f1`: `lib/std/bool.yu`
(`2d52be35270f14a487b88608e508aed64860a2f0b3a3843fbc843e9e19e18eb9`),
`crates/infer/src/builtin_ops.rs`
(`c79a7dfb031bc58598ea6551472be568362f3b34c1b7a1b4c53721e0581c053d`),
`crates/evidence-vm/src/runtime.rs`
(`eb3f2d42752ff112b621d35471ebab79e767523f4597c7d6bd57329d02231ee7`), and
`crates/mono-runtime/src/lib.rs`
(`3a821fc693414e6d9feef6d16bf44df4caa13d3b17af137439155b74765a683f`).
R149 authority/evidence hashes at review: `1644743185363d3c258c606a2e65245b3db8206dddeb666d2994e2471d74f7fa`
and `6f9a7a430f54fe412163ddec7f374ff9a671d7d5ec62fa6cec252e8cb7800828`.

## Scope still open

The `int_add`, `int_to_string`, and `string_concat` paths already existed at the
sprint baseline; this increment does not newly implement them and by itself
does not execute the Types/Console examples. Those examples still require their
separate tuple, module/library, output, and effect paths. This sprint does not
implement full Yulang inference or evaluation and does not close BuildLocal,
principal inference, effect-permission adoption, source coverage, native
correspondence, or the original Simple-sub A/B claims. The three safety
manuscripts remain separate proof artifacts with their listed open gates; this
primitive implementation does not apply or promote them.

The outbound integration set is limited to these four implementation files,
this contract, this outcome, and `tasks/agent-loop/current.json`. Seven
pre-existing untracked files were preserved, including the two paths whose
writer cessation remains unconfirmed. They are not part of this change.
Integration commit: `8a2f8113f2b7298bc0789c5b285ae05a6603f9d4`.
After a fresh fetch, `origin/research/simple-sub-intrusion` matched that exact
commit. No force push was used.
