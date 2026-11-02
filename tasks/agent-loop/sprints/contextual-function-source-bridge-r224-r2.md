# Sprint R224 revision 2 — contextual Function source bridge

Status: **REVISED / ADMITTED** by Luna after the R224 rev1 Function-rule
authority mismatch. Branch `yulang3`; admission baseline is the current
checkpoint containing the R224 rev1 stop. Preserve the rev1 contract and its
two frozen handoffs byte-for-byte. The user goal and all four original roots
remain unchanged.

## Original parent and measurable outcome

The original parents remain `InferenceSoundness`, `SourceScopedCoverage`,
`PrincipalCoverage`, and `InferenceTermination` in
`notes/theory/lean/YulangClosure/Contracts.lean:128–154`. In particular,
soundness retains every supported source, original scope, generated constraint
and solution, and requires one witness for both `sourceJudgment` and
`sameScoped`. R224 rev2 targets an original generated Value-entry App and its
Function/interface readout. Success must apply one source-constructed equation
to a named premise of the unchanged App/soundness obligation, or freeze the
first exact missing source constructor/equation and its authoritative owner.
No standalone support bound, assumed admission/interface law, desired source
judgment, or parent-delta claim without that application counts as success.

## Fixed semantic authority and dependencies

- The selected boundary is `notes/design/2026-10-03-concrete-compatibility-boundary.md`,
  SHA-256 `5b0b4321d8644f88a7a946aff31b6b3190d37a9076ac698fa91fdfeef1470f16`.
  §1 requires both Function effect descriptors to be resolved jointly within
  one inequality, under the same assignment, source owners/incidence and
  existing `K,D`; it forbids independent general-Type comparisons and
  composing separate concrete resolution successes. The case
  `Fun(a,never,b,c) <: Fun(a,d,[b,d],c)` must not create an independent
  `d <: never` obligation. No broader four-field rule is approved.
- §§7–8 require role-first Function elaboration: derive the actual receiver
  role and declared/expected boundary before body constraints, while retaining
  the independent parameter-entry role. For a value-entry invocation, preserve
  the complete `Force(D) >>= B` path, argument and body observations, and the
  same provider, receipt, world, assignment and correlated `ν,K,D`.
- [Contextual Function membership](../../notes/design/2026-10-08-contextual-function-membership-definition.md),
  SHA-256 `0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0`,
  fixes the same-provider complete-call meaning within §§1–4; it does not
  supply exhaustive descriptor admission or the requested source equation.
- [Callback expected-context delivery](../../notes/design/2026-10-03-callback-context-delivery.md),
  SHA-256 `df4941d4c66e4f3147257024a35e7041a2c51dd528657cc80efaf3d0db62fed5`,
  fixes role selection before literal body generation while charter §21 keeps
  parameter entry independent.
- The selected mixed-row fragment is in `notes/design/2026-10-03-concrete-compatibility-boundary.md`
  §9 and `questions/2026-10-05-function-effect-row-denotation/receipt.md`,
  SHA-256 `7cd1cea5b6b4649e68b6d57b854e1fa390a4bf671d051256c2f6823b11b2d1d3`.
  Its targeted deep-handler removal discriminator requires complete
  source-owned request/continuation/path/attachment/image evidence. It is not
  a complete descriptor calculus or a general row-union law.
- Original source/generator/readout inputs are pinned at admission:
  `Contracts.lean` `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`;
  `OriginalSourceGeneration.lean`
  `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`;
  `OriginalSourceChecking.lean`
  `a0ba215e28fe0152e3c66024da86ab9a63219b7950e741bf260cbc4c2897ffd6`;
  `OriginalSourceInterpretation.lean`
  `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef`;
  `OriginalSourceSyntax.lean`
  `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1`;
  `OriginalSourceCallerSchema.lean`
  `9bb15c7f383a997c4e7d63efd521704c925e62c95072f81ad18ad2aec9ba30b9`.
  Rehash these and the selected authority inputs at dispatch. Any drift returns
  to Luna before writing.
- R224 rev1 handoffs are frozen counterevidence to the original route:
  proof `c0c9518afd29a788c0fb3104b42da4ac43f645ad2204121f3ffbc6f78102f27c`;
  owner bridge `a9818d3cba8bffb9b78660884bc5cad4dcd8045e28dccca31e4ca008d7f834ae`.
  R186 records are locators only; discard the independent four-port variance
  target and its unverified App bridge.

Do not redefine source typing as generated-formula satisfaction. Do not assume
`Kernel.admitted`, descriptor formation, complete-call admission, receiver
role/interface formation, the desired source judgment, or a same-scoped
witness. Do not introduce a new carrier, independent port comparisons,
concrete transitivity, new effect meaning for `never`, or narrowed source
semantics. Existing finite source rules and readout definitions must construct
the equation. A missing equation is an honest bounded result, not a theorem.

## Lanes, outputs and review seam

1. **Constructive proof — registered `lean_prover`.** Own only:
   - `notes/theory/lean/YulangClosure/ContextualFunctionSourceBridgeR224.lean`
   - `tasks/agent-loop/inbox/contextual-function-source-bridge-r224-proof.md`

   Trace the actual raw App/Function introduction and checking rules to the
   Value-entry interface/readout. State the theorem with the unchanged source
   witnesses and assignment. Carry argument and body observations jointly
   through `Force(D) >>= B` and the approved mixed-row case. Apply the result
   to a named original App premise. If construction stops, identify the first
   missing equation and semantic owner; do not fill it with a premise.

2. **Source-owner investigation — Luna, read-only.** Trace the exact selected
   Function role/boundary from source introduction/checking, through generated
   interface and to the actual App consumer. Identify which original
   constructors already carry role, annotation/expected boundary, parameter
   entry, shared provider/receipt/world and coupled effects, and the first
   missing owner equation if any. No Rust edit, Rust/Cargo command, build or
   test. R224 rev1 owner evidence is input, not a substitute for this source
   boundary.

3. **Fresh independent `compiler_referee` review after freeze.** Own only
   `tasks/agent-loop/inbox/contextual-function-source-bridge-r224-review.md`.
   Check exact authority, source construction, unchanged App-premise
   application, non-vacuity and complete axiom audit. Falsifiers include
   force-before-receipt, separate assignments, dropped/re-emitted pending
   effects, or family-only suppression. The proof author and source
   investigator cannot review their own claims.

Luna is the sole owner of dependency rechecks, pinned-project verification,
cache writes, checker and axiom audit, state synchronization, adjudication,
Git and push. Parents remain open absent genuine reviewed application.

## Resources and cache

The user explicitly authorized Lean cache generation. Use only the existing
pinned project `notes/theory/lean` and its existing `.lake/build`; no new
worktree, environment, project copy, target directory, cache or scratch tree.
Lean is pinned at 4.35.0. Preserve R224 rev1 spent time; this revision may use
only the remaining R224 envelope, with no reset and zero Astra. One CPU, one
heavy process, `-M1024`, 1 GiB process limit, and the original aggregate `.lake`
growth cap of 64 MiB above 131,264,002 bytes. Stop before a build if any target
artifact exists at intake or the cap would be exceeded. Do not clean caches.

Only the new module's normal Lake outputs are permitted:

```text
notes/theory/lean/.lake/build/lib/lean/YulangClosure/ContextualFunctionSourceBridgeR224.olean
notes/theory/lean/.lake/build/lib/lean/YulangClosure/ContextualFunctionSourceBridgeR224.olean.hash
notes/theory/lean/.lake/build/lib/lean/YulangClosure/ContextualFunctionSourceBridgeR224.ilean
notes/theory/lean/.lake/build/lib/lean/YulangClosure/ContextualFunctionSourceBridgeR224.ilean.hash
notes/theory/lean/.lake/build/lib/lean/YulangClosure/ContextualFunctionSourceBridgeR224.trace
notes/theory/lean/.lake/build/ir/YulangClosure/ContextualFunctionSourceBridgeR224.c
notes/theory/lean/.lake/build/ir/YulangClosure/ContextualFunctionSourceBridgeR224.c.hash
notes/theory/lean/.lake/build/ir/YulangClosure/ContextualFunctionSourceBridgeR224.setup.json
```

Build only `+YulangClosure.ContextualFunctionSourceBridgeR224:olean` and run
the focused bundled theorem/axiom checker. Report actual theorem types and
complete axioms. No default/full build, Rust, Cargo or tests.

## Parent metrics and stop conditions

Report unchanged roots as **0/4** and packages as **0/5** unless an original
root is actually discharged. A conditional source equation or exact blocker
does not close a root. Preserve Call, annotation checking, all effect hygiene,
source scope, and the one shared witness. Stop on the first missing approved
constructor/equation, changed dependency, resource-cap conflict or source
authority mismatch. At the first exact equation seam or closeout, consult the
dispatcher before any material change in route or authority.
