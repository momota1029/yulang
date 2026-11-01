# Sprint R226 — source callback-interface acquisition proposal

Status: **ADMITTED** by Luna on 2026-11-02 after the reviewed R225
incomplete-only stop. Branch `yulang3`; baseline checkpoint `c4e263b92`.
Original source semantics, the ongoing Yulang inference guarantee goal and all
four parent roots remain unchanged.

## Objective and parent metric

Prepare and independently review a **proposal**, before another theorem
assignment, for acquiring a callback formal's source-use Function interface
and original slot/profile from retained source annotation/declaration inputs,
then making that result available to callback checking before its body is
generated. The proposal must show a worked original App path through
`descriptorFormation` and its callee-to-descriptor consumer, and mark every
equation that remains unproved.

This packet is representational design work. It may identify candidate
definitions and their source owner, but must not add source rules, choose a
new annotation/overlap/unknown-callee meaning, change the compiler, assume a
resolved `F_cb`, or claim any original premise discharged. No Lean theorem is
assigned. R226 outcome is measured by whether it identifies a concrete
construction and exact remaining equation owners; the parent-premise delta
remains **0** unless a later reviewed theorem is applied to an unchanged parent
premise. Roots remain 0/4 and packages 0/5.

## Fixed authorities and inputs

- User-adopted callback boundary delivery B:
  `notes/design/2026-10-03-callback-context-delivery.md`, SHA-256
  `df4941d4c66e4f3147257024a35e7041a2c51dd528657cc80efaf3d0db62fed5`.
  The proposal must preserve already-instantiated `(F_cb, β, Slots(β))`,
  pre-body delivery, receiver Handler role selection, independent parameter
  Value/Computation entry, synthesis of `F_lit`, and one final
  `F_lit <: F_cb`. Do not copy expected endpoints into the literal interface.
- Joint Function/effect boundary:
  `notes/design/2026-10-03-concrete-compatibility-boundary.md`, SHA-256
  `5b0b4321d8644f88a7a946aff31b6b3190d37a9076ac698fa91fdfeef1470f16`.
  Keep effect descriptors jointly resolved under the same assignment,
  incidence/owners and existing `K,D`; do not split ports into independent
  inequalities or compose concrete successes.
- Original source definitions: `Contracts.lean`
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
- R225 evidence: sprint contract
  `4d5cea5c80080f4fbe196ca7cba7312bfb88986b8736673388ddfa143ab913a8`;
  proof stop `ef586f6af2e1c5233b2d4980533817c5dc0ae7badcf09308ccc4cbcab3fec511`;
  owner schedule trace
  `e58c149bace45d3738d039065b2a8e4cecbfd561d5d24cb88b65e5ff4a91b27e`;
  independently reviewed R225 outcome
  `R225 outcome is recorded in tasks/agent-loop/history/20261102-r225-outcome.md`
  and must be rehashed at dispatch.
- Current retained source/instantiation owners, reauthenticate at dispatch:
  `crates/yu-hir/src/module/source_annotation.rs`
  `409ce491bc216c6963bf76d20810790aa2756edf260ecc35e76d5cfc05d24b3f`;
  `crates/yu-hir/src/module/local_source.rs`
  `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1`;
  `crates/yu-solver/src/candidate_source.rs`
  `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49`;
  `crates/yu-solver/src/candidate_call.rs`
  `fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f`;
  `crates/yu-solver/src/candidate_effect.rs`
  `4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15`;
  `crates/yu-solver/src/shadow_apply.rs`
  `99d67895c250e5d79fb774728867fe2fc88c4dc22df9bfc38ac9fd1aeb0908e5`.
  These are source-identity pins only; no Rust edit or execution is authorized.

## Required proposal content

1. Trace an actual **known declared-formal** App from its original source
   declaration/name and annotation syntax through source-use instantiation to
   the exact formal Function interface and original `β, Slots(β)`. Identify
   the actual existing input/owner for every field. Do not start from a
   supplied resolved interface.
2. Show the App-to-argument checking path and how this result reaches B before
   any callback Lambda body constraints. Distinguish this contextual boundary
   from the Lambda's own annotation and parameter-entry role.
3. Preserve inferred types as symbolic variables and explain what constraints
   bind them. Do not require an unknown callee's final solved type before
   ordinary constraint generation. Mark symbolic-callee/interface acquisition
   as unresolved if current source inputs cannot provide it.
4. Work through the unchanged original App constructor and named consumers:
   `.descriptorFormation`, `wholeArgumentCompatibility`,
   `completeCallCertificate`, `sourceCallIncidence`, `callableImage`, and the
   callee returned-value-to-App descriptor check. Show where the proposed
   output would enter and which equalities/adequacy steps are still missing.
5. Retain complete Value-entry `receipt; Force(D) >>= B`, argument/body
   observations, same provider/receipt/world/assignment and correlated
   `ν,K,D`, Call/effect/readout obligations, same shared witness and original
   source domain. Retain Computation-entry behavior separately.
6. Separate representation definitions from a **genuine semantic choice**.
   In particular, do not locally decide annotation/callback overlap or
   unknown-callee behavior. The already selected known-formal B path does not
   require resolving those broader cases before its acquisition proposal.

The proposal is falsified if it supplies `F_cb` or a profile as an assumption,
uses a final solver result as an input to initial checking, invents slot data,
loses substitution correlation, applies receiver role from parameter entry,
delivers the boundary after body generation, uses a different App formal, or
claims descriptor formation/call admission without their actual source laws.

## Lanes, outputs and review

1. **Source-owner design — registered `researcher`, max 1,800 seconds.** Own
   only:
   - `notes/design/2026-11-02-source-callback-interface-acquisition-proposal.md`
   - `tasks/agent-loop/inbox/source-callback-interface-acquisition-r226-design.md`

   The first is a concise candidate representation/flow proposal. The second
   is the authenticated source-owner derivation, worked App path, falsifiers,
   exact unproved equations and honest stop conditions. No Lean module, source
   edits, implementation, tests, builds or execution.
2. **Fresh independent `compiler_referee`, max 600 seconds, after both files
   freeze.** Review the actual source owners, acquisition fields, use-site
   substitution, pre-body path, App consumers, symbolic inference preservation,
   and authority boundary. Return verdict by message (read-only role); do not
   author or mutate source files. Reject any assumed resolved interface or
   invented overlap/unknown-callee rule.

Luna is sole owner of semantic adjudication, hashes, compact-state updates,
Git and push. This proposal does not authorize a follow-on Lean proof or
compiler patch. Those require a concrete, reviewed construction and a new
bounded packet under the existing objective.

## Resources and closeout

At most 2,400 seconds total: 1,800 design plus 600 review. Zero Astra. No
Lean/Lake/build/cache, Rust/Cargo/test/compiler execution, temporary trees,
new environments or directories. No cache generation is needed for a design
proposal; the user's cache authorization remains active for a future theorem
verification in the existing pinned project. Preserve all unrelated dirty
paths.

At closeout, report concrete source data fields found, exact missing
equations/owners, reviewer verdict, unchanged App premise and parent delta.
Roots remain 0/4 and packages 0/5 absent reviewed application to an original
root. Consult the dispatcher if the design reveals a required semantic choice
or before admitting a proof/implementation packet.
