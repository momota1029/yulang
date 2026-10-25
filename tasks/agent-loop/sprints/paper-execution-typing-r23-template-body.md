# Sprint FULL-PAPER-TYPE-SUBSTITUTION-20261026/r23 — registered template body typing under type instantiation

Status: CANDIDATE until Luna authorizes the source-audit phase. The semantic phase is BLOCKED until the caller/body context correspondence is source-grounded. No worker/checker may act before a fresh receipt is recorded and committed.  
Branch: `research/simple-sub-intrusion`  
Baseline: `9d1962d56872f551f20476b0578002c49f7d5f1d` (R22 accepted and pushed)  
Contract revision: r1

## Original parent and selected outcome

The unchanged parent is the full-paper simultaneous type-substitution theorem at `docs/yulang-operational-type-safety-ja.tex:953–977`, then full inference/executor semantics and original A/B over the unchanged accepted source domain. R22 is a reviewed prerequisite, not parent closure. R23 investigates the first remaining template premise at manuscript :129/:243 and the single-step template expansion at :327. The source says every registered body is typed in its prescribed formal environment and an invocation/expansion uses one shared type-argument vector; the expansion also substitutes value arguments, whose term-substitution theorem is outside this packet.

Before adding any judgment, establish how the stored body context embeds into the invocation context. Source :243 gives one ordered formal-type list and requires arguments typed at that one type instance; it does not itself write `\Gamma,\bar x:\bar A`. Source :129 requires each stored body to be typed in its prescribed formal environment, while :194–196 say each entry carries type arguments, value arguments, a result and a body, and that free captured values are explicit arguments. Use accepted R21’s ordered-binder convention for the term formals: repeated cons makes the last formal lookup index zero (`extendTupleEnvironment formals []`). Use accepted R22’s `typeArity`/`instantiateType` convention for the entry-local type parameters and list-order instantiation. These settle the list conventions only. Source :264–270 says omitted `\Xi` is shared across all premises, but does not by itself settle whether body typing uses the caller’s exact `D/\Xi`, an entry-local/opened context, or an embedding between them; explicit captures at :194 alone do not imply `\Xi=[]`. Inspect the full governing source and accepted definitions for an exact scope embedding, including how `mapDeclarationTable` and `mapGraphEnvironment` relate under instantiation. If that evidence is absent, stop before semantic construction and freeze the exact authority blocker and owner. Do not use a conditional table-invariance lemma as a substitute for this scope correspondence or infer a convention from implementation.

Only if the exact body/caller context embedding is source-grounded, add a new module `YulangClosure.PaperExecutionTemplateBody` importing the accepted R22 modules. Define a transparent `TemplateBodyTyped declarations graphTypes entry` relation whose constructor carries exact resolution of that entry in `declarations.templates` and an actual `PaperComputationTyped` derivation for that entry’s `body`, with the source-grounded formal environment and result `entry.result`. This definition is an explicit premise package, never a proof that any generated table is well-typed.

Prove `TemplateBodyTyped.typeInstantiation` for arbitrary `arguments`, using `σ := instantiateSubstitution arguments` and the accepted `PaperComputationTyped.typeTransport`. For an entry `.mk identity arity formals result body` and an actual body derivation, conclude a `PaperComputationTyped` derivation for the instantiated body `mapPaperComputation σ body` at `instantiateType arguments result`, under `mapDeclarationTable σ declarations`, `mapGraphEnvironment σ graphTypes`, and the correspondingly mapped formal environment. Preserve the complete entry and make the single type-argument vector explicit. State separately that R22's `arguments.length = arity` premise is required to apply this instance to a well-arity invocation; do not add an unused arity premise to the generic substitution theorem.

A same-table specialization is secondary and permitted only after the source-grounded scope embedding, with explicit premises for every required equality such as `mapDeclarationTable σ declarations = declarations` and `mapGraphEnvironment σ graphTypes = graphTypes`. These equalities do not establish the missing context embedding. Do not claim that manuscript :129 or resolver uniqueness alone proves them. If the paper supplies exact closure premises, derive the equalities only from those premises; otherwise retain them as OPEN.

Construct one concrete polymorphic body derivation using two ordered formals to test binder order (for example formal types `[.var 0, .bool]`, result `.var 0`, body `.ret (.variable 1)` under the reverse-cons environment). Instantiate the type parameter with Int and show the body derivation has result Int. Also check the R22 signature-only falsifier: no formals, result Bool, body `.force (.literal (.integer 1))`. R22's invocation signature can type the zero-argument call at Bool, but the body must not satisfy `TemplateBodyTyped`; do not present the ill-typed body as a paper counterexample or alter R22's rule to make it typeable.

R23 does not prove value/term substitution, one-step execution preservation, whole-table well-formedness for generated source, or full source/native correspondence. The concrete example is one instance of the new body judgment, not evidence that all source-generated tables satisfy it.

## Success evidence and falsifiers

Success first requires an exact source-grounded embedding of the stored-body `D/\Xi` and formal environment into the invocation context, with precise locators and definitions. If this cannot be established, success is a frozen authority-blocker handoff before any semantic artifact. Only after that gate passes may the packet add the explicit resolved-body premise, arbitrary type instance, required same-context equalities, examples, focused build, complete axiom audit and fresh independent review.

Falsifiers: using formal order inconsistent with `extendTupleEnvironment`; deriving body typing from resolver/signature alone; dropping or changing the actual stored body; using different type arguments for formals/result/body; silently assuming declaration-table invariance; treating the R22 signature falsifier as body-safe; asserting term substitution or execution; a `sorryAx`, unapproved axiom, failed declaration, or any mismatch with manuscript scope. A genuine source ambiguity stops construction and is reported, not repaired by a new convention.

## Continuing lanes

**Proof lane:** registered `lean_prover` `/root/r17_forall`, only after a fresh actual active-work/session receipt, exact hash match, and Luna's committed acknowledgement. First produce the source/context embedding audit. If it fails, write only the bounded source-only handoff and stop. If it passes, proceed within the same envelope to the explicit resolved-body premise, type-instance theorem, context equalities, examples and exact audit/handoff. Reuse R22 transport, R16 binder/type-shift results and R13 `instantiateType_subst` only where their statements match. Do not edit accepted R22 modules.

**Implementation/source lane:** `NO_SAFE_CODE_SLICE`. Primary's prior reads of `crates/yu-hir/src` and `tools/inference-playground/src/runtime/{program,machine}.rs` found no corresponding type-parameterized declaration-table call entry or registration validator. No Rust change or test is authorized. This remains a read-only correspondence note.

## Frozen authority, inputs and exact leases

Read-only hashes at baseline:

```text
docs/yulang-operational-type-safety-ja.tex  a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b
notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean  e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932
notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean  3b1588bff2d28a3db7aa241c930495b84f090e880ad49ac8fb2d593d54943d41
notes/theory/lean/YulangClosure/PaperExecutionBinderLaws.lean  568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a
notes/theory/lean/YulangClosure/PaperTypeSubstitution.lean  02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861
notes/theory/lean/YulangClosure/PaperTypeFormation.lean  29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13
notes/theory/lean/YulangClosure/DeclSubst.lean  f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258
tasks/agent-loop/inbox/paper-typing-subst-r22-adjudication.md  cd96e28b69535ba847025343574edf687af27a255cd24868bea1f8c95d3a5ce6
```

Exact worker writes in isolated checkout `/tmp/yulang-r23-templatebody`: new `notes/theory/lean/YulangClosure/PaperExecutionTemplateBody.lean`, `notes/theory/lean/.lake/R23Audit.lean`, and `tasks/agent-loop/inbox/paper-typing-subst-r23.md`. No accepted source, root import, current state, contract, checker cache, or reviewer path. If the body/caller context embedding is not established from source, worker writes only the handoff and runs no checker. Primary owns current state, `.lake/build`, checker output, any future root import, adjudication and Git. Fresh reviewer after freeze receives only `tasks/agent-loop/inbox/paper-typing-subst-r23-review.md`.

## Resource and stop contract

Envelope proposed from the sprint-end selector: 1800 active seconds total including primary intake/review; at most 12 literal serial Lean/Lake invocations and 180 checker seconds; worker cap 10, primary reserves 2; one checker/cache owner at a time; at most two heavyweight builds and no more than one concurrent. Use pinned Lean 4.35.0, `-j1 -M1024`. Worker must not edit or run a checker before receipt hash reconciliation and committed acknowledgement. No tests, default/full build, Rust build, dependency changes or network activity.

Review mode M1: one fresh non-author source/spec reviewer checks the frozen scope, theorem premises, formal ordering, exact stored body, table-invariance boundary, falsifier and complete axiom output. Convergence requires no blocking/major finding or one bounded repair plus a re-frozen delta review. Stop for source ambiguity, new semantic choice, authority/dependency change, budget boundary, checker failure, STOP or session end; preserve the exact first unresolved premise and owner. R18 remains OPEN/UNADOPTED and is not in this packet.
