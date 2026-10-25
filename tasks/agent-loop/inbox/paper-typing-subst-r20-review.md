# R20 independent source-only review

Verdict: **NO BLOCKING OR MAJOR FINDINGS** for the frozen represented union-elimination rule, inversion, injection typing compositions and arbitrary-substitution extension.

Reviewer `/root/r16_independent_review`, assigned as a non-author; no R20 construction, repair or edits. Active acknowledgement preceded inspection. **Source-only review: 0 Lean/Lake invocations, 0 checker seconds.** Retained build/audit evidence was inspected; this is not a fresh kernel receipt. Only this report was written outside the repository.

## Authority and frozen inputs

Worktree `/tmp/yulang-r20-unioncase`; baseline `aafbc15f0f9595eabea2c5187fba75fff06c3d04` is the contract-supplied identifier. No Git command was used. Read main-checkout contract `tasks/agent-loop/sprints/paper-execution-typing-r20-unioncase.md`, freshly matching SHA-256 `49166707d5fd483660672fd29f905fa38c3f0fc1f654b4569a6ea44beadb7743`. Root AGENTS, goal-driven sprint rules and the previously read Lean skill/source/execution references remain applicable.

Fresh artifact/dependency hashes match all supplied frozen values:

| File under worktree | SHA-256 |
| --- | --- |
| tasks/agent-loop/inbox/paper-typing-subst-r20.md | dc3a214ecf0ce25ec3f23845bc1a4e6a49b4e466204d3ca7e053d452cc8de039 |
| notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean | 678f84eb635c95392068887b834a4f79a1a754ad474b950097aa212a3b68032c |
| notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean | 55c84a4c3a5e83c3f4b8ff05b836790f0357b836d31daf0b9b316c427947afb7 |
| notes/theory/lean/.lake/R20Audit.lean | 5e2fb4f6b9ba6f360201ac44637b8abf5aebd7d34987c864146ebaba19641f3d |
| notes/theory/lean/YulangClosure/PaperExecutionBinderLaws.lean | 568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a |
| notes/theory/lean/YulangClosure/PaperTypeSubstitution.lean | 02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861 |
| notes/theory/lean/YulangClosure/PaperTypeFormation.lean | 29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13 |
| notes/theory/lean/YulangClosure/DeclSubst.lean | f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258 |
| docs/yulang-operational-type-safety-ja.tex | a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b |

Passive hashes of the retained objects under `.lake/build/lib/lean/YulangClosure/` also match: Syntax `6bf160c9b5ee1541eff029067edcaf771a29a793fb2d347f929b48d51bf430cb`; BinderLaws `ed7b891d96c75b2132d9aada19eee7296e9e740dde74287f045d4709afce7638`; TypingSubstitution `5a30de8388d65aafe0145da93ef9f67b70d977240370c07e29c1eab85b0e0136`. This identifies retained bytes without revalidating their proofs.

## Source and proof inspection

All Lean names below use prefix `YulangClosure.PaperTypes`.

1. **Paper correspondence and contexts.** Manuscript :233 gives union injections and requires both unioncase bodies to have the same result. Raw syntax :172 is `unioncase(v,x.M,y.M)`; reduction :313 binds the selected injection payload to the corresponding branch variable. The R20 fixed contract spells out the exact elimination contexts: scrutinee A∨B in Gamma, left branch C in A::Gamma, right branch C in B::Gamma. `PaperComputationTyped.unionCase` at Syntax:748–753 implements exactly that rule. D/Xi and the tail Gamma are identical throughout, and one resultType index is used in both branch premises and conclusion. No binder type is swapped and neither branch premise is omitted. This review treats the manuscript as the fixed proof target; research status is not blanket semantic-adoption authority.

2. **Actual inversion retains the original result.** `PaperComputationTyped.unionCaseInversion` at TypingSubstitution:471–483 takes a derivation for the actual raw unionCase at arbitrary resultType, cases on that derivation, and recovers one pair leftType/rightType with the scrutinee and both original branch typings. The branches retain exactly the input resultType, D/Xi/Gamma and raw computations/binders. ResultType is not existentially replaced or weakened to an independently selected output. No additional premise assumes the evidence being recovered. Other represented constructors have a different raw computation head.

3. **Both injection compositions are correctly scoped.** `PaperComputationTyped.unionCaseInjectLeft` at :486–496 uses `PaperValueTyped.injectLeft` from a value typed leftType, then applies unionCase with both unchanged branch derivations. `unionCaseInjectRight` at :499–509 uses a value typed rightType and the existing right introduction, again retaining both branches. Left branch receives leftType, right branch rightType, and both conclude resultType. Neither theorem claims selected-branch execution, reduction, term substitution or runtime behavior.

4. **Arbitrary simultaneous substitution.** New common-recursion branch at :286–289 applies the same arbitrary sigma to scrutinee, left and right IHs. The unchanged mapPaperComputation unionCase equation at Syntax:239–241 retains both binder names while mapping all three subterms. Mapping context cons yields `subst sigma leftType :: mapTypeEnvironment sigma Gamma` on the left and the corresponding rightType context on the right. Both mapped branches conclude the same `subst sigma resultType`; D/Xi/Gamma are mapped together. No formation restriction, special substitution, closed context or separately selected witness is introduced.

5. **All prior cases and six results remain.** Direct diffs against frozen R19 show only the single unionCase constructor, one recursor branch and three theorem blocks, plus whitespace. Raw mappings, existing constructors/premises, forall freshness, wrap, declaration/operation instantiation, records and continuation handling are unchanged. Independent counts give 38 judgment constructors and 38 common-recursion case proofs. Full printed signatures of all six transports retain arbitrary sigma and all original context, subject and type indices; their only typing premise is the original derivation. Continuation response/result remain separate. Their wrapper proofs are unchanged and consume the extended common theorem.

6. **No escape or authority expansion.** The six-module proof-cone search found no sorry/admit/axiom/skipKernelTC/native_decide/implemented_by/unsafe/set_option token matches. The audit options control display only. No imported dependency, root import, source scope, LocalLaws instance, compiler behavior or R18 variant correspondence was changed. No proposition definition is presented as a concrete proof instance.

## Complete retained audit assessment

Read the entire audit source and handoff invocation-2 output at :2904–3040. Its nine theorem-kind checks, exact fully qualified type prints, complete axiom prints, axiom-allowlist checks and begin/end pairs cover all delivered theorems. Each reports exactly **[propext, Quot.sound]**:

- `YulangClosure.PaperTypes.PaperValueTyped.subst_explicit`
- `YulangClosure.PaperTypes.ValuesTyped.typeTransport`
- `YulangClosure.PaperTypes.ValuesAllTyped.typeTransport`
- `YulangClosure.PaperTypes.RecordPayloadsTyped.typeTransport`
- `YulangClosure.PaperTypes.PaperComputationTyped.typeTransport`
- `YulangClosure.PaperTypes.PaperContinuationTyped.typeTransport`
- `YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInversion`
- `YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInjectLeft`
- `YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInjectRight`

The complete printed `PaperComputationTyped.unionCase` constructor reports **does not depend on any axioms**. The retained lists contain no sorryAx, Classical.choice, custom axiom or failed declaration.

Producer receipts record focused Syntax/TypingSubstitution build exit 0 in 22.586330 seconds and `lake env lean -j1 -M1024 .lake/R20Audit.lean` exit 0 in 0.686139 seconds, totaling 2 calls and 23.272469 checker seconds with LEAN_NUM_THREADS=1. The complete retained output includes linter warnings and successful build completion; no failed diagnostic is suppressed. Bundled audit_source/validate_audit PASS is recorded. The pin is Lean 4.35.0; no fresh version query is represented as R20 evidence. This reviewer executed none of those commands and does not supply a new kernel or primary-verification receipt.

## Parent application and open obligations

The new extrinsic constructor directly supplies the three-premise represented unioncase rule. Both existing union introductions compose with it, inversion recovers its premises at the original result, and the common substitution theorem now includes this case for arbitrary sigma. No new mathematical premise remains for that represented local seam, subject to primary adjudication.

Full paper typing/substitution remains OPEN. The first unresolved manuscript-order introduction remains the separate primary-owned R18 variant typeArguments correspondence, followed by other omitted rules such as nominal and switch, with recursive graph guards and remaining administrative cases also open. This result establishes no reduction/branch-execution preservation, inference/executor safety, original A/B closure, concrete LocalLaws instance, source/native/Rust correspondence or production authority. The frozen handoff keeps those distinctions and makes no completion overclaim.

## Cessation

Only `/tmp/yulang-r20-review-report.md` was written. Candidate source/audit/handoff/cache, main checkout and Git remained read-only. No child, scheduling, external contact or ongoing subprocess. Reviewer **0 Lean/Lake calls / 0 checker seconds**; active-time telemetry was not separately instrumented, and no exact duration is invented. **Report frozen; reviewer STOPPED and writes ceased.**
