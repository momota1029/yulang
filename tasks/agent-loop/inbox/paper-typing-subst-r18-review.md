# R18 independent source-only review

Verdict: **NO BLOCKING OR MAJOR FINDINGS in the frozen obstruction handoff.** Its mandatory stop is justified by the exact R18 contract. The reported gap is an unresolved raw-to-paper correspondence, not a refutation of the paper variant rule or a proved variant theorem.

Reviewer `/root/r16_independent_review`, freshly assigned and not an R18 author. Active acknowledgement preceded inspection. Review resources: **0 Lean/Lake calls, 0 checker seconds**. Only this report is written, outside the repository; no source, handoff, cache, Git or shared-record mutation.

## Frozen inputs

Reviewed `/tmp/yulang-r18-variant/tasks/agent-loop/inbox/paper-typing-subst-r18.md`, freshly matching supplied SHA-256 `a54a797f1b9fecb658a21e7c10df48fb40dd718c5d18f75f7906b9cc7740382f`.

Read the exact contract at main checkout `tasks/agent-loop/sprints/paper-execution-typing-r18-variant.md`; fresh SHA-256 `d7c0e9b060687dd60aab5ded32f256f4675f71d1a2117df621c998266a9b69ac` matches the handoff. Its frozen baseline is `e6ff152a983129edbdf3e4d3529d446a50844e38`; this identifier is supplied by the contract, not re-established with Git.

All seven claimed frozen input hashes freshly match:

| Input under worktree | SHA-256 |
| --- | --- |
| notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean | 8f4a32fd1c013ae78a161dadd52bed57cc7c99af5ae30fd30ba133de2c3f74a4 |
| notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean | b2975d38fccbf5c908741c3714b2b513b4b8706d80f3c009125c815d1b944d89 |
| notes/theory/lean/YulangClosure/PaperExecutionBinderLaws.lean | 568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a |
| notes/theory/lean/YulangClosure/PaperTypeSubstitution.lean | 02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861 |
| notes/theory/lean/YulangClosure/PaperTypeFormation.lean | 29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13 |
| notes/theory/lean/YulangClosure/DeclSubst.lean | f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258 |
| docs/yulang-operational-type-safety-ja.tex | a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b |

Neither possible R18 audit location exists (`.lake/R18Audit.lean` and `notes/theory/lean/.lake/R18Audit.lean`). Final proof source bytes remain the accepted R17 inputs. Hash comparison cannot establish absence of every transient historical write; the handoff's runtime/cessation statements remain the producer's receipt, and no contrary evidence was found.

## Findings and correspondence assessment

1. **The stated mismatch is accurate within the governing sources.** The manuscript raw grammar at lines 150–155 uses `t(payloads)`. Its variant rule at :219 requires matching tag, correct arity and ordered payload component typing in the selected row arm. The general projection statement at :109 retains constructor/payload/response type arguments but does not define an independent raw variant annotation list or its relationship to the row. Actual Lean `YulangClosure.PaperTypes.Value.variant` at Syntax:46–47 has three independent fields: DeclarationId, List Ty, List Value. The raw-to-paper role of the second field is not supplied by those statements.

2. **Existing formation does not fill that gap.** `YulangClosure.PaperTypes.Ty.variantCons` stores label, payload-type sequence and tail. `VariantFormed` at Formation:63–67 imposes argument formation, formed row tail and distinct labels. It does not mention Value, the raw List Ty field, a declaration instance or a raw-to-row relation. The corrected-core note §2 V1(b) and §3 V2 retain simultaneous substitution and same-tag/component typing; they do not give that extra list an interpretation. They remain research evidence, not authority to invent one. The review does not infer that no possible governing source exists elsewhere; the handoff correctly requests a primary-owned authority resolution or an existing source that supplies it.

3. **The discriminator is analysis only, correctly labeled.** The two raw Values have the same tag 7 and ordered `[integer 3, boolean true]` payload, differing only between typeArguments `[]` and `[string]`. The described row uses distinct tags 1 and 7, selects the non-head tag 7, and has two ordered component types `[int,bool]`. Thus it makes the unresolved extra field concrete without confusing selected tag, order or arity. The handoff explicitly asserts neither typing nor rejection of either raw Value; it calls the pair underdetermined correspondence and disclaims executable/Lean-checked counterexample status. It does not derive a mathematical contradiction, a native failure or rejection by the original source language.

4. **The preservation/map account is faithful.** Actual `YulangClosure.PaperTypes.mapPaperValue` at Syntax:183–185 retains constructor identity, applies `mapTypeArguments sigma` to every explicit type argument, and recursively maps every payload in the attached list. `mapTypeArguments` is ordinary order-preserving List.map of type substitution. No equality, emptiness, ignored-metadata rule or instance semantics is inferred from that map. The current `PaperValueTyped` definition at :648–718 still has no variant introduction constructor, so accepted R17 transports do not establish the omitted variant case. The handoff does not claim otherwise, restrict sigma, discard either field, or add formation assumptions.

5. **Stopping is contractually required.** R18 explicitly identifies this unspecified raw field, forbids guessing equality/instance semantics or silently discarding it, and requires immediate stop if its relationship cannot be justified from the manuscript. The handoff reaches exactly that condition before editing proof source. Spending the six construction calls on a chosen interpretation would not discharge the missing authority premise. A stop before Lean execution is legitimate here; no missing checker result is represented as a failed theorem or counterexample.

6. **Read-only native inspection supports only the stated limited boundary.** `program.rs:891–893` constructs `Instruction::Variant { tag, payloads }` using source-ordered payload labels. `machine.rs:730–745` uses tuple evaluation for payloads and retains the tag; :1659–1672 reconstructs payload order and the tagged value. These instructions expose no Lean raw List Ty correspondence or declared row typing evidence. The handoff correctly confines its claim to that inspected path and reports no native execution or production conclusion.

7. **No completion overclaim.** The handoff says no theorem construction, proof, new theorem type or axiom audit exists; no Lean/Lake version was observed in R18. It separates prior R17 receipts from R18 execution and leaves original full-paper simultaneous substitution plus variant introduction/inversion OPEN. Its relative-path lookup failure and successful absolute contract lookup are disclosed. The reported lack of theorem/diagnostic receipts is appropriate for this source-only stop. No LocalLaws, proposition definition, test or prior green audit is promoted to parent closure.

## Parent application and next premise

R18 contributes the concrete correspondence obstruction, not a new typing premise. Stable TODO `R18-VARIANT-TYPEARG-CORRESPONDENCE-1` is appropriately owned by the primary semantic/source authority owner: establish the role and substitution action of the raw variant typeArguments field, or supply an existing governing source, while preserving the original supported source scope and shared witnesses. The correspondence must distinguish annotation lists from payload component types and declaration type parameters and account for the displayed raw pair. This review chooses no interpretation and grants no new authority.

Only after that premise is resolved can a new authorized packet add row membership/shape, variant introduction, inversion, the non-head ordered example and arbitrary simultaneous substitution. Full paper typing, other omitted rules, recursive graph guards, inference/executor safety, original A/B, source/native/Rust correspondence and production remain OPEN.

## Execution limits and cessation

No new execution receipt is claimed: reviewer Lean/Lake calls **0**, checker time **0**, no tests/build/install/version command. Producer's 0-call/0-checker-second account is consistent with the frozen source-only artifact; its exact active duration remains unobserved. No reviewer exact active-time telemetry is invented. No children, scheduling, third-party contact or outstanding subprocess. This report is the sole reviewer write. **Report frozen; reviewer STOPPED and writes ceased.**
