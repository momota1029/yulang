# R192 — canonical source interpretation prerequisite

Revision 1. Status: primary-owned source-semantics intake after R191; fixed
goal remains inference soundness for the unchanged Yulang source domain.

## Parent and exact missing interpretation

The parent remains `YulangClosure.SourceProblem.InferenceSoundness`
(`Contracts.lean:128–130`), with every original supported source, the actual
generated constraints, every satisfying assignment, and the same assignment in
the final `sameScoped` witness. R191 established that the current abstract
`SourceProblem` does not yet instantiate the mathematical Yulang generator,
independent type/effect denotation, or scoped relation.

This packet examines the canonical source meaning needed by the generation to
source induction, beginning with the selected App witness:

```text
⟦descriptorFormation(q,f,arg,vq)⟧(E, Δ, a) = ?
⟦logical ViewLogic admission⟧(E, Δ, a, vq) = ?
```

The meaning must be independent of `Kernel.atom`, source typing success,
successful constraint solving, or a hidden admission law. It must preserve the
original binder telescope, occurrence, payload, formation fields, and one
solution assignment. It must connect to the full source interpretation; this
packet cannot close the parent by proving an App-only conditional lemma.

## Permitted outcomes

1. Recover an existing accepted source definition and its exact equation to
   the original generation/consumer, with authenticated source and direct
   dependencies.
2. If accepted authorities determine the relation, state a concrete
   mathematical definition and derive its assignment/readout equation without
   adding premises. Keep the definition provisional pending independent review.
3. If the required definition is not fixed, record the exact open expression,
   missing fields, bounded owner search and downstream parent edge. Do not
   claim global absence, semantic ambiguity, impossibility, or choose new
   semantics. A pending question-board decision stays pending.

No new type constructor, carrier, source rule, admission policy or supported
domain is authorized. The independent source/Lean mapping may use the listed
files only and must stop at an unresolved authority boundary.

## Evidence and resources

Pinned direct inputs:

- `Contracts.lean` — `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`
- `OriginalSourceGeneration.lean` — `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`
- `OriginalSourceEnvironment.lean` — `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132`
- `OriginalSourceInterpretation.lean` — `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef`
- `OriginalSourceSyntax.lean` — `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1`
- `docs/yulang-source-type-safety-ja.tex` — `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166`
- `notes/design/2026-10-08-source-generalize-definition.md` — `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38`
- `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` —
  `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`
- `notes/design/2026-10-05-source-contracts-and-common-allowance.md` —
  `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186`
- `notes/design/2026-10-11-yulang-inference-top-level-principles.md` —
  `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`

Read only the declarations/equations needed for the source relation, App
formation, and logical admission. Do not inspect Rust owners or broaden to
linked historical packets. Primary cap: 600 seconds. Fresh independent
`spec_auditor` cap: 600 seconds. No proof worker before an independent source
definition is available. No Lean/build/test/Rust/environment/cache/scratch work.
The pending `questions/2026-11-02-original-typed-union-rule/question.md` is a
status locator only: do not answer, edit, stage, or treat it as resolved. Stop
if an exact field equation needed here depends on that unanswered semantic
choice.

Sole outputs:

- `notes/theory/2026-11-02-canonical-source-interpretation-r192.md`
- `tasks/agent-loop/inbox/canonical-source-interpretation-r192.md`
