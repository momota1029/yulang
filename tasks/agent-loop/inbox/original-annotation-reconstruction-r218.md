# R218 original annotation reconstruction — frozen handoff, revision 2

Sprint / contract: R218 / 1; contract SHA-256
`edc324dd8f0e5eaf4e0f5da8b6c6310e942215a58d936a48a3dfc0ff8ed882e0`.
Baseline: `yulang3` at `ef1873b5e9507192bc97fcdcbb1074eaae70f2e4`.
Parent gate: `YulangClosure.SourceProblem.InferenceSoundness`,
`Contracts.lean:128–130`; original quantifiers, `supported`, source meaning
and effect-hygiene policy unchanged.

## Assignment and frozen artifacts

- Primary model: `notes/theory/2026-11-02-original-annotation-reconstruction-r218.md`,
  SHA-256 `9bbec9b53fdd764abd828da333b47696e5e6f61ec21f6c04d0b2197abff65651`.
- Lean candidate: `notes/theory/lean/YulangClosure/OriginalAnnotationReconstructionR218.lean`,
  SHA-256 `757e1aba95e32761360676facdab27ca11b34b4e1b986c8b0f1479ee33a604e6`.
- Contract: `tasks/agent-loop/sprints/original-annotation-reconstruction-r218.md`,
  SHA-256 `ada687b7f18aaf0a1bc25a6bd63918370f021c590c9b3840d6c6d11c6bb3c338`.
- Outcome: `tasks/agent-loop/history/20261102-original-annotation-reconstruction-r218-outcome.md`
  (primary closeout pending final review).

Direct Lean dependency pins:

```text
OriginalSourceSyntax.lean                    3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1
OriginalSourceGeneration.lean                126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef
OriginalSourceInterpretation.lean            feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef
OriginalSourceEnvironment.lean                0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132
OriginalSourceRecordBoundary.lean             c7889284745ebd23ec300cf3e4de0a8f7ffc4546a9af2eccf5df76d071a0dd1a
StaticAnnotationConstraintInterpretation.lean 1829ee637ab5cf3254e220e4c0fc1306f248499f087baa779287b947c67018c9
Contracts.lean                                 2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e
```

Governing source pins are recorded in the model note. Rust and frozen-Oracle
source are read-only evidence and retain R217's pinned hashes.

## Outcome, proof and parent application

The original syntax stores annotation IDs and the Lambda generator forwards
the ID and selected entry to `sourceFormalRole`. A particular `supported`
predicate or `Kernel` could capture a fixed table; the inspected generic source
cone does not construct an authenticated law connecting such a table to this
Lambda atom. The separate
`OriginalSourceRecordBoundary.Declarations.annotation` readout is consumed by
recorded annotation-boundary cast construction; no source law connects it to
Lambda `sourceFormalRole`, four Function ports, or every supported source.
`Kernel.atom` supplies that meaning from outside the source syntax.

The Lean module constructs one original Lambda with annotation ID 7 and two
explicitly external readout functions choosing distinct trees. It separately
stores a value `Effectful` wrapper and Function argument/result arrow rows. It
proves these external choices differ for the identical source and that no one
resolver over raw source syntax agrees with both. It does not implement a
Yulang resolver, prove an actual Yulang collision, or assert either external
meaning is language-valid.

Checked declarations in
`YulangClosure.OriginalAnnotationReconstructionR218`:

```text
original_lambda_formal_unchanged
external_readouts_preserve_row_ownership
annotation_trees_distinct
same_annotation_id_distinct_external_readouts
conditional_no_common_source_resolver
no_source_resolver_agrees_with_both_external_readouts
```

Pinned Lean `4.35.0`, Lake `5.0.0-src+eb6cafb`. Primary checker built the
module (3 Lake jobs, exit 0), printed all six declaration types, and audited
all six; each `#print axioms` result was the empty dependency list. The
registered leaf's initial checker attempt stopped before build because its
inherited `RLIMIT_AS=1 GiB` caused Lake thread creation to fail (exit `-6`);
the leaf then stopped, and the primary took the cache lease. Full primary
command and receipts are in the model note. Existing project cache reused;
no package/environment update, Rust build, or tests.

## Parent and scope accounting

This result identifies a missing source-data law but does not remove an
induction premise. Parent delta 0; roots 0/4; packages 0/5; effect-hygiene
theorem delta 0. The source-qualified question remains whether an authenticated
annotation declaration relation already exists and is used by the Lambda
generator; no such law was found in the inspected source cone. The current
carrier/Oracle arrow-row mismatch remains open. Keep the parent and all source
coverage obligations open.

## Contributors and execution state

- Complementary read-only source audit: `/root/r218_original_annotation_source_audit`;
  completed with no writes, no build/tests; observed model/effort UNKNOWN.
- Lean leaf: `/root/r218_annotation_lean`, requested role `lean_prover`;
  module writes stopped and process exited. Observed model/effort UNKNOWN.
- Primary: Luna, sole integration/Git owner.
- Fresh independent `compiler_referee` review: pending at handoff freeze.

The handoff is revision 1. No reviewer has certified this artifact yet.
