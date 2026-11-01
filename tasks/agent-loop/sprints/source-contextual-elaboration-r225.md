# Sprint R225 — source contextual elaboration at App

Status: **ADMITTED** by Luna on 2026-11-02 after the reviewed R224 R2 exact
source-owner stop. Branch `yulang3`; baseline is checkpoint `579df249d` plus
the R224 closeout/admission records. Original user goal, source semantics and
all four parent roots remain unchanged.

## Parent-facing objective

The unchanged roots are `InferenceSoundness`, `SourceScopedCoverage`,
`PrincipalCoverage`, and `InferenceTermination` in
`notes/theory/lean/YulangClosure/Contracts.lean:128–154`. R225 targets the
first source owner needed by the original Value-entry App soundness case:
resolve the callee's declared or inferred formal Function interface and its
original callback-slot profile, then deliver that expected callback boundary
to a callback literal before generating the literal body. Receiver role comes
from that boundary; parameter Value/Computation entry remains determined
independently by the existing source rule.

Define a proof-level bidirectional elaboration operation over the original
source syntax, with synthesis for the callee and checking for the argument.
Establish an adequacy equation showing that the original App rule consumes the
same resolved formal boundary that checking delivered before body generation.
Apply the equation to an unchanged named premise of the original App/soundness
obligation under the same source scope, assignment and shared witness. A
standalone elaborator, a conditional adequacy theorem, or a theorem whose
premise supplies the already-resolved interface does not meet the objective.
If the original source syntax/checking judgments cannot determine a required
input or order, freeze the exact missing constructor/equation and semantic
owner; do not choose new language semantics locally.

## Governing semantics and authenticated inputs

- The user-adopted expected-callback delivery rule is
  `notes/design/2026-10-03-callback-context-delivery.md`, SHA-256
  `df4941d4c66e4f3147257024a35e7041a2c51dd528657cc80efaf3d0db62fed5`.
  Its B path passes `(F_cb, β, Slots(β))` before body constraints, selects
  receiver Handler role from that context, independently preserves §21
  parameter entry, constructs `F_lit`, and checks `F_lit <: F_cb`. It rejects
  endpoint substitution and stronger equality. Its source API is not silently
  decided here.
- `notes/design/2026-10-02-source-computation-role-elaboration.md`, SHA-256
  `9a230eb023698666f4c3e518a527009d6915e65f658b230e6da6a29914ca3abb`, is a
  candidate/design locator; it is not independent authority to change source
  rules.
- The approved joint Function compatibility boundary is
  `notes/design/2026-10-03-concrete-compatibility-boundary.md`, SHA-256
  `5b0b4321d8644f88a7a946aff31b6b3190d37a9076ac698fa91fdfeef1470f16`.
  Preserve jointly resolved effect descriptors under the same assignment,
  owners/incidence and existing `K,D`; do not split into independent port
  inequalities or compose separate concrete successes.
- Contextual Function membership is
  `notes/design/2026-10-08-contextual-function-membership-definition.md`,
  SHA-256 `0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0`.
  The selected mixed-row receipt is
  `questions/2026-10-05-function-effect-row-denotation/receipt.md`, SHA-256
  `7cd1cea5b6b4649e68b6d57b854e1fa390a4bf671d051256c2f6823b11b2d1d3`.
  Neither supplies the missing source acquisition or delivery equation.
- Reauthenticate before work: `Contracts.lean`
  `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`;
  `OriginalSourceSyntax.lean`
  `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1`;
  `OriginalSourceGeneration.lean`
  `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`;
  `OriginalSourceChecking.lean`
  `a0ba215e28fe0152e3c66024da86ab9a63219b7950e741bf260cbc4c2897ffd6`;
  `OriginalSourceInterpretation.lean`
  `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef`;
  `OriginalSourceCallerSchema.lean`
  `9bb15c7f383a997c4e7d63efd521704c925e62c95072f81ad18ad2aec9ba30b9`.
  Also authenticate R224 R2 contract
  `30e55a488f709712b421428d677de5be85ce37ff007c1ac4a74f474d5ccd2060`, proof
  handoff `bafd07be8b6a2b1f2310ceaafe1a17e22bec818590b3bdf8c559f5968b69a62e`,
  and independent review recorded in the R224 outcome. Drift returns to Luna
  before writes.

## Forbidden shortcuts and falsifiers

Do not supply `F_cb`, `β`, `Slots(β)`, a Function descriptor, the desired
source judgment, a Kernel admission predicate, or a same-scoped witness as an
assumption when the operation is meant to acquire it from the original App
source. Do not change `sourceRules`, annotation meaning, source typing,
Function compatibility, callback entry, Call, effects, or scope. Do not treat
`OriginalSourceCallerSchema` as a constructor. Do not use a new carrier to
hide the acquisition obligation. Preserve the complete Value-entry
`Force(D) >>= B` behavior and observations, same provider/receipt/world and
assignment, coupled `ν,K,D`, and the reviewed mixed-row discriminator.

Review falsifiers: boundary arrives after callback body generation; receiver
role inferred from parameter entry; the App rule uses a different formal than
the one checked; the elaboration silently changes source scope or assignment;
adequacy assumes the source fact it should derive; or the delivered result
forgets Call/effect/readout obligations. A failure must identify the first
missing source constructor/equation and its owner, not claim impossibility.

## Lanes and exact outputs

1. **Constructive proof — registered `lean_prover`, max 3,600 seconds.** Own
   only `notes/theory/lean/YulangClosure/SourceContextualElaborationR225.lean`
   and `tasks/agent-loop/inbox/source-contextual-elaboration-r225-proof.md`.
   Define the smallest source-directed synth/check operation that can decide
   callee formal acquisition and pre-body delivery. Prove its adequacy from
   original syntax/rules and apply it to one named unchanged App premise. Keep
   all obligations and quantifiers explicit. If the original rules lack the
   needed input, report the exact seam and stop without adding an axiom or
   hypothesized interface.
2. **Source owner trace — registered `researcher`, read-only, max 1,200
   seconds.** Own only
   `tasks/agent-loop/inbox/source-contextual-elaboration-r225-owner.md`.
   Trace actual current source declaration/annotation inputs through App
   checking and callback literal generation. Establish whether the selected
   boundary and original callback profile are available before body checking;
   report source locations and first owner. No compiler/Rust edits, builds or
   tests.
3. **Fresh independent `compiler_referee`, max 900 seconds, after both
   handoffs freeze.** Own only
   `tasks/agent-loop/inbox/source-contextual-elaboration-r225-review.md`.
   Adversarially check source-rule fidelity, pre-body order, role/entry
   independence, scope/assignment and same-witness preservation, and actual
   application (or exact honest stop) at the unchanged App premise. Neither
   author reviews their own work.

Luna is sole owner of dependency/hash rechecks, any pinned-project Lean
verification, cache writes, checker and axiom audit, state synchronization,
adjudication, Git and push. No implementation lane is admitted: there is no
safe compiler code slice while the source constructor is unresolved.

## Resources and checkpoint

Use only the existing pinned project `notes/theory/lean` and its existing
`.lake/build`; no new worktree, environment, project copy, target directory,
cache location or scratch tree. The user explicitly authorizes Lean cache
generation. No build/cache write before a concrete theorem module is frozen.
After that, one CPU, one heavy process, `-M1024`, 1 GiB process limit, and at
most 64 MiB aggregate `.lake` growth above the R223 baseline of 131,264,002
bytes; stop before build if the target artifact exists at intake or the cap
would be exceeded. Build only the exact new module target and run the focused
bundled theorem/axiom checker. Report theorem types and full axiom lists. No
default/full build, Rust, Cargo or tests.

Total sprint envelope is at most 5,700 seconds across lanes, with zero Astra.
Roots remain **0/4** and packages **0/5** unless an original root is genuinely
discharged after review. Parent-premise delta is the primary progress measure.
Consult the dispatcher at a material blocker/authority change or closeout.
