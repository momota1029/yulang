# R19 independent source-only review

Verdict: **NO BLOCKING OR MAJOR FINDINGS** in the frozen represented wrap introduction/inversion, wrapped-Call derivation and substitution extension.

Reviewer `/root/r16_independent_review`, independently assigned and not an R19 author or repairer. Active acknowledgement preceded inspection. This is **source-only review: 0 Lean/Lake calls and 0 checker seconds**. Retained kernel/audit receipts were inspected; no fresh reviewer kernel acceptance is claimed. Only this report was written outside the repository.

## Authority and frozen inputs

Candidate worktree `/tmp/yulang-r19-wrap`; contract-supplied baseline `c5d41edcbd5689f0c4365a0b5330b709fed422ee`. No Git operation was performed to establish or alter that identifier. Read original R19 contract in the main checkout: `tasks/agent-loop/sprints/paper-execution-typing-r19-wrap.md`; fresh SHA-256 `3f0448e72500adab70e0fa0890aee0c5641032b77dfedf6714bd270d95c6fc74` matched the handoff. Previously read root AGENTS, goal-driven sprint rules, Lean proof skill and source/execution references remain applicable.

Fresh hashes match every supplied frozen artifact and direct dependency:

| File under candidate worktree | SHA-256 |
| --- | --- |
| tasks/agent-loop/inbox/paper-typing-subst-r19.md | d014f09205bb2c08af78c656d476035ae25e8b08b1590f3dc01d88469924c65e |
| notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean | 2192b5de98b9af217318dd95db93c6fd4b776e93266f62ec7e4e23402166acb3 |
| notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean | 6c41d59cf9326b2e94e612b62c02448991979d60658a88a001a4e7143bbfefdc |
| notes/theory/lean/.lake/R19Audit.lean | d6f4ea5cb8206784ef0794007adc207331738a2157df7c9def803c60ee4c0263 |
| notes/theory/lean/YulangClosure/PaperExecutionBinderLaws.lean | 568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a |
| notes/theory/lean/YulangClosure/PaperTypeSubstitution.lean | 02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861 |
| notes/theory/lean/YulangClosure/PaperTypeFormation.lean | 29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13 |
| notes/theory/lean/YulangClosure/DeclSubst.lean | f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258 |
| docs/yulang-operational-type-safety-ja.tex | a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b |

Passive SHA checks also matched the three retained generated objects in `.lake/build/lib/lean/YulangClosure/`: Syntax `e78b9f11560dabc2d779ca3faa7568c66b6b7ae70cd6d036117beaf870fc9e90`, BinderLaws `2739231c458630d06438594042b063868278bcf1c8d6f91e87ce19248c178ee6`, TypingSubstitution `2cab9fe04e495ef2c395e0ba565ac0cb9793ebf08059d0242ea2b526a7cf8904`. Hash matching identifies retained artifacts; it is not a new validation of their kernel proofs.

## Correspondence, proof and scope assessment

All Lean names below are under `YulangClosure.PaperTypes`.

1. **Exact paper rule.** Revisited manuscript:224 and :228, with the original substitution parent :953–977. The paper says function `f:C(A,B)`, argument computation `a:A` under `A'::Gamma`, and result computation `r:B'` under `B::Gamma`, yielding `wrap(f,a,r):C(A',B')`. `PaperValueTyped.wrap` at Syntax:683–691 has exactly these three premises and conclusion. D/Xi are identical throughout; Gamma is the same tail of both adapter contexts. The argument and result endpoints are not reversed. There is no omitted adapter premise, new metadata field, ambient formation assumption or source-domain restriction. The manuscript is the fixed proof target; this review does not treat its research status as blanket language-semantic adoption.

2. **Existing relation preserved.** Direct diff against the frozen accepted R17 source shows a single wrap-constructor block in Syntax, without any other change to raw syntax, mappings, prior constructors or premises. TypingSubstitution adds only the wrap recursor branch and two theorem blocks (plus spacing). Independent counting gives 37 judgment constructors and 37 corresponding common-recursion proof branches, preserving all prior 36 cases, including shared-context forall introduction. No R18 variant relationship is silently chosen or encoded.

3. **Genuine inversion.** `PaperValueTyped.wrapInversion` at TypingSubstitution:467–482 starts from an actual derivation for raw `.wrap function argumentAdapter resultAdapter` and arbitrary result type `ty`. It recovers one shared existential quadruple A/B/A'/B', the equality `ty = callable A' B'`, and every original function/adapter typing premise in the exact D/Xi/Gamma contexts. Its proof inverts the derivation and returns the constructor's witnesses and premises. It does not assume the conclusion, require a preselected callable output, or manufacture independent incompatible endpoint witnesses. Other represented rules have different raw constructor heads, so this inversion is correctly scoped to the actual raw wrap term.

4. **Wrapped Call has the requested typing conclusion.** `PaperComputationTyped.callWrapped` at :485–499 takes the three wrap premises and a Value thunk typed `.thunk A'` under the same shared contexts. It uses the existing Call constructor with the newly built wrap typing to conclude `.call (.wrap f a r) thunk : B'`. It neither consumes a thunk of inner A nor concludes inner B. This is a compositional typing derivation; no execution-step or adapter-runtime claim is made.

5. **Arbitrary substitution preserved.** New common-recursion branch at :192–196 applies the same arbitrary sigma to function and both adapter IHs. Actual `mapPaperValue` retains the function and maps both Computation adapters (:192–194 in Syntax). Unfolding `mapTypeEnvironment` and List.map_cons transports `A'::Gamma` to `subst sigma A' :: mapTypeEnvironment sigma Gamma`, and `B::Gamma` analogously. Function type becomes callable `(subst sigma A)` `(subst sigma B)`; output becomes callable `(subst sigma A')` `(subst sigma B')`. No substitution, declaration, graph, shared environment or result is selected separately or restricted.

6. **All six transport statements retained.** Inspected the complete printed types of `PaperValueTyped.subst_explicit`, `ValuesTyped.typeTransport`, `ValuesAllTyped.typeTransport`, `RecordPayloadsTyped.typeTransport`, `PaperComputationTyped.typeTransport`, and `PaperContinuationTyped.typeTransport` in handoff:2905–2977. Each retains arbitrary sigma, D/Xi/Gamma, its actual raw subject/list and type indices; its sole typing input is the original derivation. Conclusions map D/Xi/Gamma and all subjects/types together. Continuation response and normal result remain separate. Existing public wrappers are unchanged and consume the now-extended common theorem.

7. **No proof escape or hidden authority.** Searched the six-module proof cone for sorry/admit/axiom/skipKernelTC/native_decide/implemented_by/unsafe/set_option: no source matches. The audit file's options control printed names/universes only. There is no project axiom, LocalLaws assumption, proposition definition promoted to an instance, new import cycle or changed frozen dependency.

## Retained audits and execution boundary

Read the complete audit source and handoff invocation-2 output at :2902–3029. All eight theorem begin/end pairs are complete. The audit checks `.thmInfo`, prints exact fully qualified types, collects all dependent axioms and rejects axioms outside the standard allowlist. Every theorem below reports exactly **[propext, Quot.sound]**:

- `YulangClosure.PaperTypes.PaperValueTyped.subst_explicit`
- `YulangClosure.PaperTypes.ValuesTyped.typeTransport`
- `YulangClosure.PaperTypes.ValuesAllTyped.typeTransport`
- `YulangClosure.PaperTypes.RecordPayloadsTyped.typeTransport`
- `YulangClosure.PaperTypes.PaperComputationTyped.typeTransport`
- `YulangClosure.PaperTypes.PaperContinuationTyped.typeTransport`
- `YulangClosure.PaperTypes.PaperValueTyped.wrapInversion`
- `YulangClosure.PaperTypes.PaperComputationTyped.callWrapped`

The complete printed `PaperValueTyped.wrap` constructor reports **does not depend on any axioms**. No sorryAx, Classical.choice, custom axiom or failed declaration is in these retained reports.

The producer records a focused Syntax/TypingSubstitution build, exit 0, 23.970148 seconds, and `lake env lean -j1 -M1024 .lake/R19Audit.lean`, exit 0, 1.993374 seconds; 2 calls and 25.963522 checker seconds total, using installed pinned Lean 4.35.0 and LEAN_NUM_THREADS=1. The retained build output includes linter warnings and successful completion, not omitted errors. The bundled helper's audit_source/validate_audit PASS is recorded. The worker correctly distinguishes the pin/prior installed distribution from a fresh --version receipt and leaves primary final checks pending. This reviewer ran no Lean, Lake, tests or version queries and grants no new kernel receipt or primary acceptance.

## Parent application and remaining premise

The represented paper wrap premise is supplied directly by the new extrinsic constructor, consumed by the existing Call typing rule, and included in the original arbitrary simultaneous substitution theorem. No additional mathematical hypothesis is left for this represented case. This closes only that local rule-coverage seam after primary adjudication.

Full paper coverage remains incomplete. The previously identified `R18-VARIANT-TYPEARG-CORRESPONDENCE-1` is still an unresolved authority/correspondence premise owned by primary semantic/source intake; nominal, switch, other omitted typing rules and recursive graph guards retain their separate obligations. No constraint generation, machine reduction, wrapped-Call operational preservation, source/native/Rust realization, inference/executor safety, original A/B or production conclusion follows from this typing result. The frozen handoff preserves these boundaries and makes no completion overclaim.

## Cessation

Only `/tmp/yulang-r19-review-report.md` was written. Candidate sources/audit/handoff/cache, main checkout, contracts and Git remained read-only. No children, external contact, scheduling or ongoing subprocess. Reviewer resource receipt: **0 Lean/Lake invocations / 0 checker seconds**; exact active-time telemetry was not separately measured and is not invented. **Report frozen; reviewer STOPPED and writes ceased.**
