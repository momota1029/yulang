# Sprint FULL-PAPER-TYPE-SUBSTITUTION-20261026/r22 — template invocation instance typing

Status: CANDIDATE pending Luna admission; no worker/checker may act before a fresh worker receipt is recorded and committed.
Branch: `research/simple-sub-intrusion`
Baseline: `8ff731456dd9385f6497e9c5c0b99e7d8820a898` (accepted R21)
Authority: `docs/yulang-operational-type-safety-ja.tex:129,243,953–977`; no R18 variant interpretation is in scope.
Contract revision: r1

## Original outcome and success evidence

Original parent goal remains the full paper type-substitution theorem for every represented and omitted type-bearing component, followed by inference/executor semantics and the original A/B obligations over the unchanged source domain. R22 is a checked prerequisite only; it does not alter the parent theorem's quantifiers, source domain, accepted semantics, or owner. The paper invocation rule at §3.2 (:243) requires a declared code identity, one type instance shared by formal types and result, and actual values typed in the resulting formal list. At :129 template bodies are separately typed in the prescribed formal environment.

R22 outcome: add a unique resolved-template premise over `DeclarationTable.templates`; require exact equality between invocation type-argument count and declaration `typeArity`; derive `ValuesTyped` for the actual arguments against `formals.map (instantiateType typeArguments)`; conclude the raw `.template identity typeArguments arguments` computation at `instantiateType typeArguments result`. The same `typeArguments` vector must occur in both instances. Add genuine inversion retaining exact result type, resolution, arity and argument typing; add arbitrary-σ transport in the common six-judgment proof, including commutation of resolution through `mapTemplateBody`/`mapDeclarationTable` and use of `instantiateType_subst` for every formal and the result. Preserve the actual template body through table mapping. A composition witness may be included only if it follows directly from `ValuesTyped` and stays inside this exact rule.

Success evidence: focused build of both leased Lean modules; audit prints the exact theorem types and complete axiom lists for the new resolver transport, constructor, inversion, and all six transports; no `sorryAx`, `admit`, project axiom or checker bypass in the changed dependency cone; fresh source-only independent review has no blocking or major finding. Failure falsifiers include: accepting an ambiguous identity; mismatching type arity; typing formals and result from distinct argument vectors; accepting arguments not typed at every formal; losing the executable body while mapping declarations; or an audit/build failure.

The table-body condition from :129 remains a separate OPEN premise: the entry's body must type under the formal environment before an instantiated invocation is applicable to execution. R22 neither defines an assumed body-typing predicate as a theorem nor claims body execution, preservation, inference/executor safety, source/native correspondence or production readiness.

## Two continuing lanes

**Proof lane:** registered `lean_prover` `/root/r17_forall`, after fresh active-work/session receipt and exact hash match. Continue through resolver definition/transport, constructor/inversion, arbitrary-σ mutual transport, focused build and audit. Reuse R13 `instantiateType_subst`, R16 actual `mapTemplateBody`/declaration table mapping, `ValuesTyped` and R21's common transport structure. Keep any unresolved consequence as a precise OPEN premise; no scope or budget expansion.

**Implementation/source lane:** `NO_SAFE_CODE_SLICE`. Primary inspected the manuscript rule and Lean owners `PaperExecutionSyntax.lean` (`TemplateBody`, `mapTemplateBody`, `DeclarationTable`, `PaperComputationTyped`) and `PaperExecutionTypingSubstitution.lean` (`instantiateType_subst`, six-family transport); the only executable mapping is abstract Lean declaration-table mapping. Search of Rust HIR/playground runtime found no corresponding type-parameterized declaration-table call entry. A code edit or Rust theorem would therefore invent an unestablished bridge. This lane records source correspondence limits only; no implementation or tests are authorized by this contract.

## Frozen authority, dependencies and leases

Read-only dependency hashes at baseline:

```text
docs/yulang-operational-type-safety-ja.tex  a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b
notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean  e025922217e5c5fc6d68780936acd99ac8252267f8c262b50da790a72cf73b0e
notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean  db213de9e97d965fb5e105f75009c9ec4f64e02892e5fdf3a8132317cc5e5f1d
notes/theory/lean/YulangClosure/PaperExecutionBinderLaws.lean  568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a
notes/theory/lean/YulangClosure/PaperTypeSubstitution.lean  02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861
notes/theory/lean/YulangClosure/PaperTypeFormation.lean  29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13
notes/theory/lean/YulangClosure/DeclSubst.lean  f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258
```

Exact worker write leases after Luna records and commits the fresh receipt: `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean`, `notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean`, `notes/theory/lean/.lake/R22Audit.lean`, and `tasks/agent-loop/inbox/paper-typing-subst-r22.md`. Worker owns no other source, build cache, status, review or Git path. Primary retains `.lake/build`, checker/cache ownership, central status, final audit, review assignment, adjudication and Git. Reviewer path after artifact freeze: `tasks/agent-loop/inbox/paper-typing-subst-r22-review.md`, to be leased to a fresh eligible independent source-only reviewer before review starts. The R18 docket `tasks/agent-loop/inbox/r18-variant-correspondence-proposal-v1.md` is a separate primary-owned, unadopted authority-review proposal.

## Resources, verification and stop boundary

Envelope: at most 900 active seconds including intake/review; 8 literal serial Lean/Lake invocations total, 120 checker seconds total, at most one heavyweight build, finite focused iterations, and one audit file. Worker cap is 6 invocations; primary reserves 2. No cross-sprint budget transfer. Pinned project: Lean 4.35.0 in `notes/theory/lean`; one checker owner at a time; `-j1 -M1024`. Worker must not run any checker before the actual fresh receipt is matched, recorded and committed. No tests, Rust builds, default build or network activity.

Review mode M1: one independent source/spec correspondence reviewer, not an author or repairer, checks the frozen contract/dependency/artifact hashes, single-instance use, uniqueness/arity, body-premise boundary, six transports and complete audit. Convergence requires no blocking/major finding, or one batched repair within remaining budget followed by a re-frozen review delta. A failed build/audit, authority mismatch, changed dependency, ambiguous rule, budget boundary, STOP or session end stops work; record exact failure and residual parent premise. Unknown writers keep quarantined leases.

At the next sprint boundary, apply successful lemmas to the unchanged full-paper parent or preserve the exact first omitted premise and owner. Full paper, R18 variant correspondence, omitted rules, recursive graph guards, inference/executor semantics, original A/B, Rust/source-native correspondence and production all remain OPEN.
