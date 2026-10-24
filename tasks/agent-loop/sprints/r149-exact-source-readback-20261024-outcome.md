# R149 exact source readback — outcome

Sprint: `R149-EXACT-SOURCE-READBACK-20261024`, contract revision 2, SHA-256
`20541baa2157ffaa9453b7b076bb0b686b61c4663d187cc00af822026905fbe2`.
Baseline: `aba6c8eb9b9caf2559bf955670d662503950c98d`.

## Result

**PARTIAL_REVIEWED; the source-to-CST/HIR readback remains open.** The frozen
handoff identifies the parser, source-key, recovery and HIR identity owners and
the actual sample-environment access seam. It does not contain a parser/HIR
execution or readback. Exact CSTs, source-key comparisons, declaration/member/
operation joins and sample admission outcomes remain unobserved. No parser
rejection, compiler defect, theorem closure or production change is claimed.

The exact sample environment is constructed by private
`playground_syntax_environment` in `tools/inference-playground/src/lib.rs`;
`pinned_stdlib` is private and its relevant items are `pub(crate)`. Public
playground entrypoints do not return the retained parse/HIR objects required
for this readback. The independent reviewer confirmed this as an evidence
access seam while leaving compliant in-crate instrumentation possibilities
open. Any visibility/API change needs a later exact lease and fresh review.

## Frozen evidence and review

- Producer note: `notes/theory/2026-10-24-r149-exact-source-readback.md`,
  16,553 bytes, SHA-256
  `f5cedf75832e6192ddd901039ce9b2a9fd88e82c69c54e74756459fe8bc1ef4d`.
- Producer inbox: `tasks/agent-loop/inbox/20261024-r149-exact-source-readback.md`,
  6,965 bytes, SHA-256
  `0068ebe2cc513047e8e5f4ff7bcc632feebf5ef169ce175056eca8a925d06996`.
- All 24 direct source/dependency pins and both exact sample byte hashes
  matched. The producer's initial unfiltered filesystem-tree reconstruction
  included empty directories. Primary and independent review reconciled the
  Git manifest to 151 entries / 15,003 bytes, SHA-256
  `e6c7315c50c75bc6b5ed27405022258769d5594ab31645d15cbdac7400299462`.
  All filesystem regular-file paths matched; only empty directories
  `crates/yu-syntax/src/grammar/type_expr` and `crates/yu-syntax/src/scan`
  were omitted by Git. The tracked source tree therefore remains the pinned
  `b4ae511288745b882a6afb951ecaec4fe6d69d16`.
- Fresh independent review: **PASS as a partial handoff under the contract's
  boundary criterion**. No blocking or lesser corrections. Review confirms
  consumer-specific recovery handling and that no blanket parser-rejection or
  impossibility claim follows from the private visibility seam.

## Scope and next step

No driver or scratch output was created; the producer stopped before readback.
No tests, builds, parser/HIR/compiler/evaluator/runtime executions, or
production edits occurred. Three legacy UNKNOWN worker reservations remain
quarantined. The exact source-to-declaration obligation, provider selection,
fetch/publication, execution join, original A/B and full inference/evaluator
goal remain OPEN.

Next, Luna must decide whether to authorize a minimal in-crate readback wrapper
that calls the actual private environment constructor and retains the original
parse/HIR objects. Any production/API visibility change requires its own exact
lease and review; this outcome grants no such authority.
