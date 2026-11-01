# Sprint R227 — original Function/profile formation construction

Status: **ADMITTED** by Luna on 2026-11-02 after reviewed R226 design-only
stop and dispatcher closeout. Branch `yulang3`; baseline checkpoint `eeb5cca72`.
The original inference goal, source domain, semantics, four parent roots and
effect hygiene remain unchanged.

## Objective

Construct the candidate source equations for E1/E4: from original declaration
and annotation syntax, produce the complete role-indexed Function interface
of a declared formal and its original static callback template/profile. Apply
those equations to the reviewed known declared Value-formal path and R226's
worked original App. Keep source-use substitution as one symbolic map and
identify precisely what E3/E5 must transport and deliver before callback body
generation.

This is a proof-only source-definition proposal. The lane must produce actual
construction equations and justify each field from its original source owner;
another inventory that merely labels E1/E4 missing does not meet the objective.
No Lean theorem, compiler edit, API change or semantic adoption is authorized.
If a construction needs an observable source meaning absent from authority,
return the concrete candidate rule, affected accepted judgments and exact
approval needed. Do not make that choice locally.

The bounded source case is the known declared ordinary Value-formal path
selected by callback-delivery B. It does not narrow any original parent
quantifier. Unknown/inferred callees and annotation/callback overlap remain
open cases; preserve symbolic unknowns and do not add rejection or mandatory
annotation behavior.

## Fixed authorities and authenticated inputs

- Callback delivery B:
  `notes/design/2026-10-03-callback-context-delivery.md`, SHA-256
  `df4941d4c66e4f3147257024a35e7041a2c51dd528657cc80efaf3d0db62fed5`.
  Preserve known instantiated callback contract, pre-body boundary, receiver
  Handler role, independent Value/Computation entry, fresh literal interface,
  and final `F_lit <: F_cb`.
- Joint Function/effect authority:
  `notes/design/2026-10-03-concrete-compatibility-boundary.md`, SHA-256
  `5b0b4321d8644f88a7a946aff31b6b3190d37a9076ac698fa91fdfeef1470f16`.
  Preserve jointly interpreted effects, one assignment, original incidence
  and `K,D`; independent port inequalities and concrete-success composition
  are excluded.
- Callback profile sources are evidence to analyze, not automatic source
  authority: `notes/theory/2026-10-15-function-callback-profile-construction.md`
  SHA-256 `e4dbbf9cb4e15f460279647c5f4f1b8f8513dce01ea6a0d4a0a08e24f81a54cc`;
  `notes/theory/2026-10-14-callback-profile-native-construction.md`
  `1d2af128aa819e48f39744ea6e0ffa37277a2c87e4b3478fd1b5d0fc4bbc5d1c`;
  `notes/theory/2026-10-15-callback-profile-reconstruction-receipt.md`
  `4389d6e67df9e1039821a70dd55f8d40e14467b437a02f52fb584ee39e85d6fc`;
  `notes/theory/2026-10-15-callback-profile-applicability.md`
  `fd655814157503e73b77086e3216f313b838c6ea5d0365bce314972c2cb3ca8c`.
- R226 reviewed evidence: outcome
  `tasks/agent-loop/history/20261102-r226-outcome.md` SHA-256
  `80d807a0cec83caf1fe7aba6c3b9573a7e8055925738a8bc6d2385fb99e4a1d1`;
  proposal `notes/design/2026-11-02-source-callback-interface-acquisition-proposal.md`
  `9662cd6d1b6e08a29d96bffd54dc10a1af5e96789c9d0f620b17cdb3078d6459`;
  handoff `tasks/agent-loop/inbox/source-callback-interface-acquisition-r226-design.md`
  `7cedfea7c23f973a2e5f9b863ec0cd08e35e58b2eb4fe5a285d4019310c173e4`.
- Reauthenticate original Lean syntax/checking and parent proposition before
  finalizing: `Contracts.lean`
  `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`;
  `OriginalSourceSyntax.lean`
  `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1`;
  `OriginalSourceGeneration.lean`
  `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`;
  `OriginalSourceChecking.lean`
  `a0ba215e28fe0152e3c66024da86ab9a63219b7950e741bf260cbc4c2897ffd6`;
  `OriginalSourceInterpretation.lean`
  `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef`.
- Reauthenticate current source construction owners:
  `crates/yu-hir/src/module/source_annotation.rs`
  `409ce491bc216c6963bf76d20810790aa2756edf260ecc35e76d5cfc05d24b3f`;
  `crates/yu-hir/src/module/local_source.rs`
  `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1`;
  `crates/yu-solver/src/candidate_effect.rs`
  `4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15`;
  `crates/yu-solver/src/candidate_source.rs`
  `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49`;
  `crates/yu-solver/src/candidate_call.rs`
  `fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f`;
  `crates/yu-solver/src/shadow_apply.rs`
  `99d67895c250e5d79fb774728867fe2fc88c4dc22df9bfc38ac9fd1aeb0908e5`.

## Required construction and falsifiers

1. Define the original Function interface field by field from a real
   declaration/annotation syntax tree. Distinguish source role, nested value
   type, argument/result computation interfaces, present and omitted effect
   coordinates, and source identities. Every field must cite its original
   constructor/meaning; a native negative type alone is insufficient.
2. Construct the static original `β, Slots(β)` from the same source formal and
   its original callback slot/template. Preserve full source paths, typed
   dependencies, symbolic and omitted ports, and use identity. `FormalPermission`
   paths, handler request-family labels or runtime activation `b` alone are
   not a complete profile.
3. State a single source-use substitution and show how every declared source
   variable maps through it, preserving non-generic outer rows, repeated names,
   result/formal correlations and future-use dependencies. It must not require
   a final solver answer to generate initial constraints.
4. Apply the construction to the exact known declared formal in R226's worked
   App. Show how E1/E4 feed E3/E5, then how callback B gets the boundary before
   body generation. Do not equate the formal with the entire App descriptor.
5. Trace the result through the unchanged `descriptorFormation`,
   `wholeArgumentCompatibility`, `completeCallCertificate`,
   `sourceCallIncidence`, `callableImage`, callee-returned-value-to-App-
   descriptor check and App-callable-image-to-synthesis check. Mark all
   remaining E2–E9 equations without assuming them.
6. Preserve original quantifiers, source scope and one shared witness;
   complete Value-entry `receipt; Force(D) >>= B`, actual provider/receipt/world,
   assignment and coupled `ν,K,D`; Call/effect/readout and the mixed-row
   boundary. Computation entry remains distinct from receiver role.

Falsifiers include: defining profile from native solved support; dropping
omitted effect coordinates; independently freshening a shared annotation;
using a native graph as the abstract source premise; assigning expected
endpoints directly to the literal; conflating receiver role and parameter
entry; relying on an already-completed FreshUse route before body generation;
changing source annotation interpretation or overlap behavior; or claiming a
parent-premise reduction without an applied theorem.

## Lanes and outputs

1. **Source formation construction — registered `researcher`, max 1,800
   seconds.** Own only:
   - `notes/theory/2026-11-02-original-function-profile-formation-r227.md`
   - `tasks/agent-loop/inbox/original-function-profile-formation-r227-construction.md`

   Provide actual construction equations, concrete source justification,
   worked R226 App instance, exact remaining owners and if needed a discrete
   semantic-choice proposal. No Lean/Rust/compiler implementation or API work.
2. **Fresh independent `compiler_referee`, max 600 seconds, after freeze.**
   Read-only review of each source field/projection, original profile, single
   substitution, body-before-check ordering, unchanged App consumer, shared
   effect/call obligations and any semantic-choice boundary. Return review by
   message. Reject unsupported constructors, circular admissions, invented
   profiles, lost correlations or silent source changes.

Luna owns semantic adjudication, hash rechecks, state, Git and push. A reviewed
candidate definition does not itself authorize semantic adoption or compile
into an original parent theorem. No compiler slice is approved.

## Resources and closeout

At most 2,400 seconds total: 1,800 construction and 600 review. Zero Astra.
No builds, Lean/cache, tests, Rust/Cargo or compiler execution. No temporary
directory, environment, worktree, new cache or generated project output.
Preserve unrelated dirty files. The user-authorized Lean cache may be generated
later only for a concrete theorem in the existing pinned project.

Report the exact equation set constructed, any missing source definition and
approval required, independent review, unchanged App premise and parent delta.
Roots remain 0/4 and packages 0/5 until a later reviewed theorem discharges an
original root. Consult the dispatcher on any semantic alternative before
selecting it or admitting the next proof/implementation packet.
