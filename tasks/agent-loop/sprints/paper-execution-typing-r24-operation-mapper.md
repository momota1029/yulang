# Sprint FULL-PAPER-TYPE-SUBSTITUTION-20261026/r24 — operation-mapper adapter typing

Status: CANDIDATE until Luna validates the exact adapter typing context and grants leases. No worker/checker may act before a fresh receipt is recorded and committed.  
Branch: `research/simple-sub-intrusion`  
Baseline: `c2bd4055094e7b75a2155638611f015f0baa52ea` (R23 source-gate stop adjudicated)  
Contract revision: r1

## Original parent and selected outcome

The unchanged parent is full-paper simultaneous type substitution at `docs/yulang-operational-type-safety-ja.tex:953–977`, followed by inference/executor semantics and the original A/B obligations. R24 targets a separate represented proof premise: the two operation-mapper adapter derivations at manuscript :694–719 and their arbitrary type-substitution transport. R23's `R23-TEMPLATE-CALLER-CONTEXT-EMBEDDING-1` stays OPEN and is not a dependency or a claim resolved here.

Before defining a judgment, verify the exact source mapping: a mapper uses one operation declaration identity for source/target instances; payload code has direction `P(source) → P(target)`; response code has direction `Q(target) → Q(source)`; both use the same outer declaration table, graph context and captured environment. The candidate Lean adapter environments are respectively `source.payloadType :: environment` and `target.responseType :: environment`, following the paper's computation-function binder convention. The accepted R19 binder convention is supporting evidence for de Bruijn context construction, but does not establish mapper-specific source semantics; its adjudication is pinned below. Source :718 requires both code derivations and matching operation signatures, while :694–719 fixes their directions and shared mapper. If the paper and accepted binder convention do not determine these contexts, identity mapping, or type-argument scope exactly, freeze the exact source-authority blocker and stop before semantic construction. Do not infer an adapter binder or scope from Rust implementation.

If that source check passes, add only `YulangClosure.PaperOperationMapperTyping` in a new module `notes/theory/lean/YulangClosure/PaperOperationMapperTyping.lean`, importing accepted R22 modules. Keep the frozen `PaperExecutionSyntax.lean` and `PaperExecutionTypingSubstitution.lean` unchanged. Define `MapperPlanTyped declarations graphTypes environment mapper` as a transparent relation whose constructor carries: (1) unique resolution of one operation declaration; (2) exact source and target instances obtained by instantiating that same declaration at their respective type-argument lists, each with length equal to the declaration arity; and (3) the actual payload and response `PaperComputationTyped` derivations at the source-grounded input environments and opposite-direction result types. Require the same declaration identity in both instances. In particular, `OperationInstance.typeArguments` is a `Ty` encoding, not the witness list: retain for each side both the witness list and the full equality to `declaration.instantiate witnessList`, whose `typeArguments` field is `argsSyntax witnessList`. Do not reduce this to identity/payload/response field equalities that drop the encoded type-argument correspondence. The relation records these as explicit premises; it is not a new `PaperComputationTyped.mapOperation` constructor.

Prove exact inversion for this relation and `MapperPlanTyped.typeTransport σ` for arbitrary `σ`, constructing a derivation for the actual `mapMapperPlan σ mapper`. Use `PaperComputationTyped.typeTransport`, `OperationDeclarationResolved.typeTransport`, operation-instance/declaration instantiation commutation, and `mapMapperPlan` only where statements match. Preserve one mapped declaration, graph environment and captured tail through both adapter derivations. A separate wrapper proposition may bundle a body derivation with this mapper evidence only if useful; it is not the packet's main result and must not be called implementation of the omitted mapOperation typing rule.

Construct a polarity discriminator with one unary operation declaration whose payload/response templates are both `Ty.var 0`, source instance `Bool`, target instance `Int`, payload adapter returning an Int literal, and response adapter returning a Bool literal. Demonstrate the correct relation and prove that the same declaration table, source Bool instance, target Int instance, mapper identity and payload adapter cannot satisfy the relation when only the response adapter is changed to an Int-returning `.ret (.literal (.integer ...))` computation (`¬ MapperPlanTyped ... badPlan`). Keep the witness lists and their full `declaration.instantiate` equalities identical in the positive and negative cases. State that this checks adapter typing polarity; it is not a paper counterexample and does not prove mapOperation preservation or execution.

R24 does not add a constructor to the frozen six-judgment relation, prove the complete mapOperation typing rule, prove one-step execution preservation/freshening, or discharge term substitution, R23, R18, inference/executor, A/B, source/native/Rust or production obligations.

## Success evidence and falsifiers

Success requires: (1) source-grounded mapping of identity, direction, adapter formal environments and shared `D/Xi/Γ`, or an honest frozen authority blocker before semantic artifacts; (2) exact theorem types for `MapperPlanTyped`, inversion, arbitrary-σ transport of both adapters and the mapped plan, and polarity discriminator; (3) focused build and complete axiom audit; (4) fresh independent source/spec review with no blocking or major issue.

Falsifiers: different source/target operation identities; reversed or conflated payload/response directions; different declaration, graph or captured context for the two adapters; failure to transport the actual mapped mapper; assuming the frozen computation judgment already has a mapOperation constructor; treating the separate relation as completion of the full rule; wrong-direction response accepted; a `sorryAx`, unapproved axiom, failed declaration or mismatch with the manuscript. A genuine source-context ambiguity stops construction and is reported, not repaired by invention.

## Continuing lanes

**Proof lane:** registered `lean_prover` `/root/r17_forall`, only after a fresh actual active-work/session receipt, exact contract/input hash match, and Luna's committed acknowledgement. First perform the source audit. If it fails, write only the handoff and stop. If it passes, continue within this packet through the mapper relation, inversion, arbitrary-σ transport, polarity discriminator and exact audit/handoff. No edits to accepted R22 modules.

**Implementation/source lane:** `NO_SAFE_CODE_SLICE`. The inspected HIR/playground path does not establish a paper mapper-to-runtime correspondence or an approved end-to-end source/constraints/consumer path. No Rust change or test is authorized.

## Frozen authority, inputs and exact leases

Read-only hashes at baseline:

```text
docs/yulang-operational-type-safety-ja.tex  a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b
notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean  e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932
notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean  3b1588bff2d28a3db7aa241c930495b84f090e880ad49ac8fb2d593d54943d41
notes/theory/lean/YulangClosure/PaperExecutionBinderLaws.lean  568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a
notes/theory/lean/YulangClosure/PaperTypeFormation.lean  29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13
notes/theory/lean/YulangClosure/PaperTypeSubstitution.lean  02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861
notes/theory/lean/YulangClosure/DeclSubst.lean  f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258
tasks/agent-loop/inbox/paper-typing-subst-r23-adjudication.md  be099fabf7a7eea06b137ebc5862a1d0058da132356c06f369ec9fe8e635bcd1
tasks/agent-loop/inbox/paper-typing-subst-r19-adjudication.md  b98075739888a5cb9a90e49166f78a39e79e44ed2659554c0f8ffecfa3664ed4
```

Exact worker writes in isolated checkout `/tmp/yulang-r24-mapop`: new `notes/theory/lean/YulangClosure/PaperOperationMapperTyping.lean`, `notes/theory/lean/.lake/R24Audit.lean`, and `tasks/agent-loop/inbox/paper-typing-subst-r24.md`. No accepted source, root import, current state, contract, checker cache, or reviewer path. If source authority blocks, worker writes only the handoff. Primary owns current state, `.lake/build`, checker output, adjudication and Git. Fresh reviewer after freeze receives only `tasks/agent-loop/inbox/paper-typing-subst-r24-review.md`.

## Resource and stop contract

Envelope from the sprint-end selector: 1200 active seconds including intake/review; at most 8 literal serial Lean/Lake invocations and 120 checker seconds; worker cap 6, primary reserves 2; one checker/cache owner at a time; at most two heavyweight builds, no more than one concurrent. Use pinned Lean 4.35.0, `-j1 -M1024`. Worker must not edit or run a checker before fresh receipt/hash reconciliation and committed acknowledgement. No tests, default/full build, Rust build, dependency changes or network activity.

Review mode M1: one fresh non-author source/spec reviewer checks direction, identity, scope, theorem premises, mapped-plan result, polarity example and complete axiom output. Convergence requires no blocking/major finding or one bounded repair plus re-frozen delta review. Stop for source ambiguity, new semantic choice, authority/dependency change, budget boundary, checker failure, STOP or session end. Preserve R23/R18 and all original parent statuses.
