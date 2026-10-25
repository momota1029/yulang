# R23 independent source/spec review — frozen revision 1

Disposition: **ACCEPT THE SOURCE-GATE STOP; NO BLOCKING OR MAJOR FINDINGS IN THE HANDOFF.** No material minor finding. The missing premise is an exact source-to-Lean stored-body/caller context correspondence. This is not proof that template preservation is false or that no suitable embedding can be constructed.

Reviewer `/root/r16_independent_review`, non-author/non-repairer. Requested M1 source/spec reviewer; requested and observed model/effort UNKNOWN. Fresh receipt exposed shared session `01a172ef-fec1-72e3-bd47-bc4d7f51d6aa` and thread `01a17361-f800-7370-bd4a-8bf93d07f843`; no separate per-packet identifier inferred. The primary acknowledged committed receipt/lease `d4fa105fd7a992ee002a9f083620431b824c681d` before any substantive reading/review. No descendants.

**Source-only review: 0 Lean/Lake calls / 0 checker seconds.** No theorem, audit, model or runtime receipt was generated. Only this exact leased report was written.

## Frozen target and governing inputs

Read the target and contract directly from immutable commit `46d3c8c96067dfbdc1176b7529ac531a2fc2375b` with read-only `git show`, without reviewing moving diffs:

- `tasks/agent-loop/inbox/paper-typing-subst-r23.md`: SHA-256 `0bb37512743ab279a83ef7e4d35dddd97e435dc516139246b3f6fd317f6727ec`, exact supplied match.
- `tasks/agent-loop/sprints/paper-execution-typing-r23-template-body.md`: SHA-256 `7fde0c40896ce366d403e394ddcb397d595a3bc80c13e0d21bc6a889fef7e18e`, exact supplied match.

The eight governing inputs freshly matched the handoff/contract:

| Input | SHA-256 |
| --- | --- |
| docs/yulang-operational-type-safety-ja.tex | a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b |
| notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean | e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932 |
| notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean | 3b1588bff2d28a3db7aa241c930495b84f090e880ad49ac8fb2d593d54943d41 |
| notes/theory/lean/YulangClosure/PaperExecutionBinderLaws.lean | 568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a |
| notes/theory/lean/YulangClosure/PaperTypeSubstitution.lean | 02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861 |
| notes/theory/lean/YulangClosure/PaperTypeFormation.lean | 29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13 |
| notes/theory/lean/YulangClosure/DeclSubst.lean | f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258 |
| tasks/agent-loop/inbox/paper-typing-subst-r22-adjudication.md | cd96e28b69535ba847025343574edf687af27a255cd24868bea1f8c95d3a5ce6 |

Read only the frozen handoff/contract and exact governing paper/accepted source needed for the blocker. Root AGENTS, goal-driven sprint rules and previously read Lean skill/source/execution references remain applicable. Research drafts supply no independent semantic authority.

## Exact blocker assessment

The manuscript fixes that a table entry has a typed body in its prescribed formal environment (:129,194–196,243), that an invocation uses one type instance (:243), and that expansion substitutes the actual type/value arguments into the actual stored body (:327). The accepted R21 helper determines ordered term-environment extension, and R22 determines entry-local type arity, signature instantiation and the complete resolved entry. These do not themselves encode the declaration/graph indices of a generic stored-body derivation under the entry-local type binders.

Actual accepted Lean declarations support the handoff's reduction. `YulangClosure.PaperTypes.TemplateBody` (Syntax:134–136) contains identity/typeArity/formals/result/body, not a body derivation. `TemplateDeclarationResolved` (:627–631) supplies full-entry resolution/uniqueness, not typing or freshness. `PaperComputationTyped.template` (:814–821) and `PaperComputationTyped.templateInversion` (TypingSubstitution:538–553) retain the complete entry and one signature instance while omitting body typing at the explicitly OPEN R22 boundary.

For a genuinely supplied body derivation at D_body/Xi_body, accepted `YulangClosure.PaperTypes.PaperComputationTyped.typeTransport` (TypingSubstitution:508 onward) with sigma = instantiateSubstitution arguments yields exactly:

```text
mapDeclarationTable sigma D_body
mapGraphEnvironment sigma Xi_body
mapTypeEnvironment sigma (extendTupleEnvironment formals [])
|- mapPaperComputation sigma body : instantiateType arguments result
```

This is the correct conditional application of an already accepted theorem. To use that result for the original invocation, one must identify the source meaning of D_body/Xi_body and prove its relation to the actual caller indices D_call/Xi_call. Equality is one possible sufficient bridge; a justified embedding/weakening or scope-opening construction may be another. The handoff expressly allows such alternatives and does not require literal equality as the only possible method.

The reviewed sources do not provide an explicit entry-local D/Xi judgment or a proved correspondence supplying that bridge. That is the precise unresolved seam, rather than the already proved generic substitution algebra. The contract explicitly requires this source connection before any new semantic judgment or conditional same-table specialization; stopping at this point obeys the packet.

## Counterevidence checked and retained limits

1. **Closed declaration table preservation (:1089–1105).** This is substantial evidence for a narrower execution application: the one-step theorem assumes a closed well-formed D, keeps D fixed and, except graph allocation, uses the same H/Xi. The template case invokes simultaneous substitution into the code-table derivation. Thus the paper intends a fixed-table execution result; the blocker must not be interpreted as a counterexample to that result. Nevertheless, these passages do not supply a concrete Lean closure predicate/proof for every D field, do not establish closure/invariance of arbitrary Xi, and do not explain the de Bruijn opening of entry-local parameters in the stored-body typing indices. They therefore do not directly establish the full arbitrary-context parent or the currently missing source-to-Lean embedding. The handoff explicitly records :1089 and :1105 and does not suppress this evidence.

2. **Actual template expansion (:327–329; precise proof :1878–1879).** Expansion uses the actual stored body and a single actual type/value substitution; no fresh operational scope/receipt/View is introduced by that step. The precise proof repeats the same substitution principle for a table derivation. These constrain any later construction and preserve the common body/table witness. They do not write the stored body's D/Xi under its local type parameters or prove that generic context mapping leaves the caller indices unchanged. The handoff correctly treats the expansion assertion as a constraint, not the missing proof itself.

3. **Shared graph and graph extension (:264–269,981–990,1141–1146).** Omitted Xi is shared across premises, graph references can close code, and weakening preserves existing reference types. Graphless source plans may start empty, but the theorem also permits existing graph nodes and fresh typed extensions. Consequently explicit value captures at :196 do not establish Xi=[] for every stored-body/caller situation. Conversely, :269 is positive evidence that any proposed opening must retain the same semantic shared graph; it does not by itself identify equal de Bruijn representations across entry-local type scopes. An embedding changing an existing node's type cannot be justified by the graph-extension lemma. The handoff retains these distinctions.

4. **Forall freshness (:238,2058–2073,2104–2110).** Here the paper explicitly excludes the fresh binder from Gamma/Psi/Xi/D and concludes that graph types remain unchanged under its instantiation. This demonstrates a legitimate route to fixed shared contexts when actual source freshness is established. It does not state the corresponding premise for arbitrary stored template computations. Applying this value-only introduction rule to all stored computations or adding its freshness assumption to make a theorem work would require a justified source connection. The handoff correctly preserves that difference, without asserting that a future template-specific opening construction is impossible.

5. **Generic non-invariance illustrations.** With raw Xi `[(7,Ty.var 0)]`, instantiateSubstitution [Int] maps its type to Int. A zero-arity raw declaration field containing an ambient var0 similarly changes under mapDeclarationTable. These follow from accepted map definitions, whose transformations are not identities on arbitrary indices. Such inputs are not established well-formed closed configurations; they do not refute the closed-table preservation theorem. The handoff explicitly labels them analytical illustrations, not checked/source-qualified counterexamples. It does not use them to claim failure of paper safety or reject an accepted source program.

No omitted counterevidence found in the cited closed-table, expansion or freshness seams. The warranted conclusion is “the exact correspondence was not established in this packet,” not “the manuscript is false,” “all template scopes are ambiguous,” or “theorem construction is mathematically impossible.” The handoff stays within that qualified conclusion and asks the primary to locate or establish the source-owned bridge.

## Scope and overclaim assessment

- No body judgment, theorem, example, audit output or checker acceptance is claimed. Conditional application of accepted transport is explicitly distinguished from new checked construction.
- `R23-TEMPLATE-CALLER-CONTEXT-EMBEDDING-1` names the exact remaining premise and primary semantic/source-proof owner. It preserves one complete entry/body/table witness and all caller graph identities. It does not mandate a particular closure/freshness/shift convention.
- R21 settles the list-extension convention; the empty term-formal tail is part of the fixed R23 body schema under investigation. Neither fact establishes D/Xi embedding. The handoff uses no term/value-substitution result or caller-Gamma lifting as if already proved.
- The Force(Int) signature-only example remains unconstructed/unchecked and is not labeled a paper counterexample. R22 remains accepted at its signature/resolution/actual-typing boundary, as the exact adjudication states.
- The accepted R22 adjudication corrects the earlier review's packaging description of its tracked audit file. R23 neither repeats that packaging error nor invalidates the accepted source/kernel result.
- Full-paper simultaneous substitution, omitted rules/R18 correspondence, recursive graph guards, inference/executor, original A/B, source/native/Rust and production remain OPEN. No conditional invariance premise, proposition package or research draft is promoted to a concrete instance or semantic decision.

## Parent application and next owner

The R23 outcome records a source-correspondence obstruction and the correct conditional theorem application; it closes no new mathematical parent premise. Primary semantic/source-proof intake owns the next discriminating result: identify the precise stored-body typing scope for each resolved entry and construct its embedding into the original invocation context under allowed type instantiations, or locate the governing source that already supplies it. Closure/freshness/weakening must be established at that owner, with the same body/table witness and preserved graph types. Only after that gate passes may the original bounded semantic packet continue. No new packet, convention, reviewer or user decision is authorized by this report.

## Resource and cessation receipt

Reviewer **0 Lean/Lake invocations / 0 checker seconds**, no tests, native/model execution, source repair, dependency/install/network operation, Git mutation, children, scheduling or external contact. No new theorem type or axiom receipt exists. Exact active-time telemetry is unavailable and is not invented; the finite review ends without renewing the shared sprint envelope. Only `tasks/agent-loop/inbox/paper-typing-subst-r23-review.md` was written. No command or descendant remains active. **Report frozen; reviewer STOPPED and writes ceased.**
