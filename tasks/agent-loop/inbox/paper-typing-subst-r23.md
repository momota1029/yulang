# R23 source-scope authority blocker — frozen handoff revision 1

Sprint `FULL-PAPER-TYPE-SUBSTITUTION-20261026/r23`; contract r1 SHA-256 `7fde0c40896ce366d403e394ddcb397d595a3bc80c13e0d21bc6a889fef7e18e`; baseline `9d1962d56872f551f20476b0578002c49f7d5f1d`. Exact isolated checkout `/tmp/yulang-r23-templatebody` was provisioned by primary after initial receipt. Primary recorded/committed the fresh receipt at e8578f6c11a7492616a1d62f2dc03999c5218bef and source-audit start/provisioning at b00b5e4f3f430c7b049fa5d0a3652fa7d488dcc6. Before that acknowledgement only contract/hash/runtime metadata were inspected; no source audit or writes started. All8 frozen inputs matched in primary checkout at receipt, then in the isolated checkout before/after audit. Primary source was read-only throughout.

Actual worker/sole author `/root/r17_forall`; requested registered lean_prover/role-default effort; observed model/effort UNKNOWN. Fresh actual runtime exposed shared CODEX_SESSION_ID01a172ef-fec1-72e3-bd47-bc4d7f51d6aa and CODEX_THREAD_ID01a1736a-fc42-7ab1-bc93-ddab8b55fa6d; no other agent/session identifier inferred. No descendants or contributing authors.

Disposition: SOURCE AUTHORITY BLOCKER. The source gate does not pass: a manuscript-grounded stored-body/caller D/Xi scope embedding was not located. Semantic phase remains BLOCKED. This is neither a mathematical counterexample nor a claim that the manuscript's template rule is false. No TemplateBodyTyped definition, theorem, example, audit source, checker output or generated artifact was created. The contract permits only this handoff at the unresolved gate.

## Original parent and read scope

Original parent remains `docs/yulang-operational-type-safety-ja.tex:953–977`, full-paper simultaneous type substitution with original quantifiers/source scope, then full inference/executor and A/B. Source SHA-256 a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b. Accepted R22 is a prerequisite only, as its adjudication explicitly records.

Methods were read-only rg/sed over all manuscript occurrences of template/formal/shared context/type binders/closure, followed by the complete relevant sections: declaration/body/signature129/194–196/243; graph scope264–269; expansion327; substitution953–977; graph extension981–990; preservation1089–1105; initial graph1141–1147; precise template proof1878–1879; explicit forall freshness2058–2073 and2104–2110. Actual Lean TemplateBody/mappings, resolver, invocation/inversion, common typeTransport and R21 environment helper were read. The corrected-core V1(b) account was inspected only as a research draft; it supplies no independent semantic authority or exact template embedding. No Rust implementation convention was used to invent a source rule.

## Located evidence and its exact limits

| Source | What it fixes | Missing context information |
| --- | --- | --- |
| Manuscript129 | Each registered body has an actual derivation in its prescribed formal environment. | No judgment displaying the body's declaration or graph environment under its local type parameters. |
|194–196|Each entry carries type/value arguments, result and typed body; mutual recursion refers to the same table; free captured values become explicit arguments.|This fixes neither a de Bruijn opening of D/Xi nor Xi=[]; same table identity does not prove equality of its scoped type representations.|
|243|One instance shared by formal types/result, actual arguments typed at that formal list; body typed separately.|No stored-body context schema or embedding into caller D/Xi.|
|264–269|Code free variables may close through immutable graph references; graph reference typing reads Xi; an omitted Xi is shared across the premises of a judgment.|No rule stating how a registered body's entry-local type binders open that Xi or relate it to the caller's Xi.|
|327,1105|Template expansion simultaneously substitutes type/value arguments into the actual stored body; other machine data stays in its stated operational context.|No missing body/caller scope equation is supplied by the expansion assertion.|
|953–977|A given typing derivation transports all declarations/environments/plans/results under one type substitution.|It maps whatever initial contexts the derivation actually has; it does not identify those body contexts in advance or prove mapped contexts equal caller contexts.|
|1089|The one-step theorem assumes a closed well-formed declaration table.|This is not a concrete generic template opening rule, a formal closure judgment for every D/Xi index, or authority to narrow the original arbitrary-context substitution claim.|
|2058–2073,2104–2110|Value-only forall introduction has explicit freshness against Gamma/Psi/Xi/D; that side condition explains unchanged shared graph there.|No corresponding stored-template-body freshness/opening premise is stated. It cannot be copied to arbitrary stored computation bodies as an unstated rule.|
|R22 adjudication, parent-application section|Signature instance/resolution/actual typing are accepted; registered body derivation and its execution application are explicitly OPEN.|It grants no additional body context convention.|

Accepted R21 fixes ordered term formals as `extendTupleEnvironment formals [] = formals.reverse ++ []`. Accepted R22 fixes entry-local type arity and single-vector instantiateType. Those accepted list conventions are retained. They do not independently specify the D/Xi scope on the stored-body derivation.

## Actual Lean definitions and precise unresolved seam

Names below are fully qualified under `YulangClosure.PaperTypes`:
- `TemplateBody.mk identity typeArity formals result body` stores the complete entry, but no body-typing/context evidence.
- `TemplateDeclarationResolved` retains membership/key/uniqueness of that full entry. It has no body derivation, freshness or context equality premise.
- `mapTemplateBody σ` maps formals/result/actual executable body under `liftSubN typeArity σ`; it protects entry-local parameters while mapping ambient variables.
- `mapDeclarationTable σ` maps operations/nominals/primitives/templates; `mapGraphEnvironment σ` maps every graph type. Neither is definitionally the identity for arbitrary indices.
- `PaperComputationTyped.template` and `.templateInversion` use caller D/Xi/Gamma, exact arity and ValuesTyped formal instances, retaining result equality and actual body witness; body typing is not among their premises.
- `PaperComputationTyped.typeTransport` maps D/Xi/Gamma simultaneously. `mapTypeEnvironment_extendTupleEnvironment` supplies only the formal-list environment equation.
- `instantiateType` uses `instantiateSubstitution arguments`; `instantiateType_subst` and `instantiateFormalTypes_subst` preserve signature instantiation. These are algebraic results, not a body/caller embedding.
- R16 `mapDeclarationTable_shift_substitution_commutes` and graph/type commutation laws reconcile specified shifts with substitutions. They do not assert that a particular stored-body context is the shift/opening of the caller context.

Let sigma := instantiateSubstitution arguments. Once a genuine stored-body derivation exists in D_body/Xi_body with formal environment `extendTupleEnvironment formals []`, the accepted transport's conclusion would have contexts

```text
mapDeclarationTable sigma D_body
mapGraphEnvironment sigma Xi_body
mapTypeEnvironment sigma (extendTupleEnvironment formals [])
```

and body/result

```text
mapPaperComputation sigma body : instantiateType arguments result.
```

This explains the conditional mathematical reduction; it is not a newly constructed or checked theorem. To apply it to the original invocation context D_call/Xi_call, source must identify D_body/Xi_body and their embedding, then justify the required equality or admissible weakening relation from these mapped contexts to D_call/Xi_call while preserving the same entry/body, identities and shared graph types. Term/value substitution and caller-Gamma handling are additional later obligations, expressly outside R23; none is assumed solved.

Taking D_body=D_call and Xi_body=Xi_call would merely choose the missing convention. Assuming `mapDeclarationTable sigma D_call = D_call` and `mapGraphEnvironment sigma Xi_call = Xi_call` would produce a conditional specialization without establishing that convention. A scope-opening/shift construction might yield a different route, but choosing it also requires the missing source connection. No such convention is adopted here.

The absence of generic invariance is visible from accepted definitions: for a raw graph context `[(7, Ty.var 0)]` and sigma instantiated with Int, mapGraphEnvironment changes its stored type to Int. A raw declaration with an ambient free Ty.var0 likewise changes under mapDeclarationTable. These are analytical illustrations of the map definitions, not Lean-checked counterexamples, not claimed valid closed source configurations and not a refutation of paper safety. They show why resolver uniqueness/arity alone cannot supply the needed equalities. Explicit captures do not establish graph emptiness or these invariances.

## Required handoff and owner

Stable unresolved premise `R23-TEMPLATE-CALLER-CONTEXT-EMBEDDING-1`, owner primary semantic/source-proof intake:

For each resolved complete entry, locate or authorize an exact stored-body typing schema specifying entry-local type scope, D_body, Xi_body and formal environment; relate that schema to the caller D_call/Xi_call under arbitrary allowed type instantiation. Preserve the same body/table witness, original source scope and graph identities. Any closure/freshness/weakening premise must be established at its source owner, not introduced to make the body theorem pass. Falsifier: an apparent bridge that changes a caller graph type, uses an independently chosen table/body, or needs an ungrounded same-table equality does not pass this gate.

No further semantic packet is scheduled by this leaf. If primary obtains the missing evidence and adjudicates the source gate, the original R23 construction may receive an explicit continuation within the unchanged budget/leases. Until then the proposed TemplateBodyTyped package, generic typeInstantiation, same-table specialization, two-formal polymorphic example and Force(Int) signature falsifier remain UNCONSTRUCTED/UNCHECKED. The latter is not presented as a paper counterexample. R22 remains accepted at its signature-only boundary; no accepted module is edited or invalidated by this audit.

## Checks, resources and cessation

Actual operations: read-only contract/hash/runtime checks and source/definition searches/reads, followed by this exact handoff write. All8 frozen input hashes rechecked unchanged after audit. No Lean/Lake process, version query, test, compiler/Rust run, network, dependency/global-default change, Git mutation, current/contract/status/index edit, reviewer appointment or external contact. No theorem types or axiom output exist for R23 and none are invented. Pin is the accepted Lean4.35.0 project; it was not executed here.

Worker checker calls0, checker seconds0, generated-cache writes0; full12-call/180-checker-second budget remains unspent and is not transferred to another packet. Active model time uninstrumented; no invented duration or renewal of the original1800-second total envelope. No other output or scratch path was written. New `PaperExecutionTemplateBody.lean` and `.lake/R23Audit.lean` are absent; accepted sources/cache unchanged.

STOPPED: all read/write commands completed; no active process, checker/subprocess session, child or descendant remains. After this final handoff write all writes STOPPED. The sole changed artifact is this leased handoff. Semantic phase remains BLOCKED; primary owns intake/adjudication/review and any future exact writer handoff.

Frozen input hashes:
- `docs/yulang-operational-type-safety-ja.tex`: `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`
- `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean`: `e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932`
- `notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean`: `3b1588bff2d28a3db7aa241c930495b84f090e880ad49ac8fb2d593d54943d41`
- `notes/theory/lean/YulangClosure/PaperExecutionBinderLaws.lean`: `568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a`
- `notes/theory/lean/YulangClosure/PaperTypeSubstitution.lean`: `02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861`
- `notes/theory/lean/YulangClosure/PaperTypeFormation.lean`: `29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13`
- `notes/theory/lean/YulangClosure/DeclSubst.lean`: `f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258`
- `tasks/agent-loop/inbox/paper-typing-subst-r22-adjudication.md`: `cd96e28b69535ba847025343574edf687af27a255cd24868bea1f8c95d3a5ce6`
