# R24 independent M1 source/spec review — frozen revision 1

Verdict: **NO BLOCKING OR MAJOR FINDINGS; no material minor finding.** The result supplies separate operation-mapper adapter evidence and its actual-map substitution transport. It does not supply the omitted mapOperation computation rule, operational preservation or full-parent closure.

Reviewer `/root/r16_independent_review`, non-author/non-repairer. Availability receipt preceded inspection. The primary acknowledged the exact report lease in `cd0dbdabf`, after which a fresh actual review-launch receipt was sent and substantive review began. Exposed runtime session `01a172ef-fec1-72e3-bd47-bc4d7f51d6aa`, thread `01a17361-f800-7370-bd4a-8bf93d07f843`; no separate per-packet identity inferred. Requested role M1 source/spec reviewer; requested model/effort unspecified, observed model/effort UNKNOWN. No descendants.

**Source-only review: 0 Lean/Lake/checker calls / 0 checker seconds.** Retained primary output was inspected; no new kernel receipt is claimed. Only this exact leased report was written.

## Frozen target and hash reconciliation

Reviewed immutable commit `e3408cfb6` through read-only `git show`/`git ls-tree`, not a moving diff. Frozen blobs and checked-out artifact hashes matched:

| Artifact | SHA-256 |
| --- | --- |
| notes/theory/lean/YulangClosure/PaperOperationMapperTyping.lean | 175c307e00bea7ba6ec44ff153f50a7d9d943de8bdc3d4dccb02a41bc53dde77 |
| tasks/agent-loop/sprints/paper-execution-typing-r24-operation-mapper.md (r2) | 113e20cc94f1917c7761681037ac6d275a0d68f57f35c920680647ae2a282b80 |
| tasks/agent-loop/inbox/paper-typing-subst-r24.md | 7d8393f245adee34ed00fd1de39f2856547a3609485b25319911e93bbc307d7a |
| tasks/agent-loop/inbox/paper-typing-subst-r24-primary-verification.txt | 8e3064793034725921e91352b01ac320c5335b0b3ea6838ca9aeb72b62db6d8e |

The exact auxiliary audit `/tmp/yulang-r24-mapop/notes/theory/lean/.lake/R24Audit.lean` matches committed-handoff hash `e72f5648afd52e144802c6e1f1f62808ff0693c23a23f80b0580bb88007786d3`. Read-only tree inspection found no R24Audit path in this integration commit; its byte identity is pinned by the frozen handoff, not asserted as a separately committed audit blob.

All nine read-only inputs freshly match:

```text
a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b docs/yulang-operational-type-safety-ja.tex
e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932 PaperExecutionSyntax.lean
3b1588bff2d28a3db7aa241c930495b84f090e880ad49ac8fb2d593d54943d41 PaperExecutionTypingSubstitution.lean
568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a PaperExecutionBinderLaws.lean
29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13 PaperTypeFormation.lean
02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861 PaperTypeSubstitution.lean
f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258 DeclSubst.lean
be099fabf7a7eea06b137ebc5862a1d0058da132356c06f369ec9fe8e635bcd1 paper-typing-subst-r23-adjudication.md
b98075739888a5cb9a90e49166f78a39e79e44ed2659554c0f8ffecfa3664ed4 paper-typing-subst-r19-adjudication.md
```

Lean basenames above are under `notes/theory/lean/YulangClosure/`; adjudications are under `tasks/agent-loop/inbox/`. Read the r2 contract, actual source rules, accepted instantiate/map/transport definitions and the two adjudicated boundaries. Root AGENTS, goal-driven sprint rules and previously read Lean skill/source/execution references remain applicable. Research drafts grant no independent semantic adoption.

## Source/spec and proof assessment

All Lean names below have namespace prefix `YulangClosure.PaperTypes`; unqualified module line numbers refer to the frozen `PaperOperationMapperTyping.lean`.

1. **Directions and identity match the paper.** Manuscript :696–699 specifies one same family/member, payload `P(source) -> P(target)` and response `Q(target) -> Q(source)` using the same mapper. Its transition :703–708 feeds source payload p into a and the target response z into r before resuming the source continuation. `MapperPlanTyped.mk` (:14–24) therefore has the correct premise environments/results: source.payloadType :: Gamma yields target.payloadType; target.responseType :: Gamma yields source.responseType. One uniquely resolved operation declaration is shared by both instances. Identity is not inferred merely from equal endpoint types.

2. **Shared D/Xi/Gamma and binder basis are justified.** Source :203–207 puts captured/shared resources in Gamma; :269 uses the same Xi across omitted contexts. Source :711–716 protects free code names and treats both adapters as ordinary computations without granting a new captured environment. The single computation formal is represented by cons, consistently with paper :224 and accepted R19's binder representation. The mapper-specific input types come from :696–708 themselves, rather than being borrowed from wrap semantics or Rust. The relation fixes the same D/Xi/Gamma for both adapters and changes only the one formal at the head. These are already actual operation instances, not a newly introduced local type binder or registered template body, so no R23 context-opening premise is assumed discharged.

3. **Full type-argument witnesses are retained.** Actual `OperationInstance` has identity plus a Ty-encoded typeArguments field and payload/response fields (PaperTypeSubstitution:247–258). `OperationDeclaration.instantiate` (Formation:233–240) stores `argsSyntax witnessList` and instantiates both payload and response from that list. The new constructor carries both witness lists, both exact length equations, and full `source = declaration.instantiate sourceArguments` / `target = declaration.instantiate targetArguments` equalities. Thus no encoded argument field is dropped. Source/target can use different actual lists but instantiate the same one declaration; `MapperPlanTyped.sameIdentity` (:51–61) derives their common operation identity from those full equalities.

4. **Exact inversion recovers actual premises.** `MapperPlanTyped.inversion` (:29–48) starts from evidence for the actual `.mk source target payload response`, cases on its only constructor and returns the same declaration, both witness lists/arities/full instance equations and both actual code derivations at their original contexts/results. No independently selected response declaration, result substitution or assumed inversion conclusion is used. Resolution and body derivations remain explicit premises; the relation does not establish them for every source-generated mapper.

5. **Transport is for the actual mapped plan and arbitrary sigma.** `MapperPlanTyped.typeTransport` (:65–91) quantifies over every sigma, D/Xi/Gamma and MapperPlan. The conclusion uses actual `mapMapperPlan sigma mapper`. After inversion, the proof uses one declaration.substAmbient sigma for both sides and maps both witness lists by mapOperationArguments. `operation_declaration_instantiation_subst` (DeclSubst:74–108) transports complete instance equality, including encoded arguments; its exact arity premise is supplied for each side. `OperationDeclarationResolved.typeTransport` transports resolution. Actual `mapMapperPlan` (Syntax:465–468) maps both complete instances and both computation bodies. The two accepted computation transports preserve the same mapped captured tail, with source.payloadType and target.responseType cons heads mapped to their exact substituted fields. No substitution injectivity, table invariance, closedness, source restriction or extra context assumption is introduced.

6. **Positive/negative discriminator preserves the plan data that must stay fixed.** Definitions :94–114 use declaration identity 17, arity 1, payload/response templates var0; source is its Bool instance and target its Int instance. Both raw plans have those same instances and the same Int-returning payload. Only response code changes: Good returns Bool, Bad returns Int. `mapperPolarityGoodTyped` (:116–129) constructs evidence with literal `[Bool]`/`[Int]` witness lists and full instantiate equalities. `mapperPolarityBadNotTyped` (:133–143) negates typing of the fixed Bad plan, inverting any proposed relation witness; its response would type an Int literal return at Bool under an Int formal and is eliminated by actual computation/value constructor inversion. The negative result quantifies over every alternative witness, so it does not evade the polarity failure by changing lists or declaration. These constants test response result polarity; they do not claim exhaustive adapter behavior or execution and need not consume their formals.

7. **Accepted six-judgment surface is unchanged.** Frozen accepted Syntax/TypingSubstitution hashes match R22, and the new module imports the existing substitution module without editing it or the root. All six printed transport statements retain arbitrary sigma, original contexts and raw subjects/type indices; continuation response/result remain distinct. No `PaperComputationTyped.mapOperation` constructor is added. The new MapperPlanTyped is a separate explicit premise relation, not typing defined as safety or a concrete LocalLaws instance.

8. **No proof escape or scope overclaim.** Search of the new module and its six imported source modules found no sorry/admit/axiom/skipKernelTC/native_decide/implemented_by/unsafe/set_option matches. Audit options control display only. The worker's constructed/unchecked handoff is correctly a pre-primary-check receipt; the separate primary output supplies actual execution results. Its older r1 resource label does not revise the r2 amendment. R23, R18, full mapOperation typing/freshening/composition, term substitution and all full-parent/source-native/production limits remain explicit.

## Audit/type correspondence and all complete axiom reports

Read the exact audit source and primary verification output :2843–3032. Its 13 theorem blocks each check declaration kind, print the exact type/full axiom list, enforce the standard axiom allowlist and have complete begin/end markers. Passive text comparison confirmed all 14 #print-axioms names (13 theorems plus constructor) match all 14 output names in order. The relation and constructor signatures and the raw positive/negative definitions are also printed. Handoff statement descriptions agree with these actual printed types, including actual-map transport and whole-instance equalities.

| Fully qualified declaration | Complete reported axioms |
| --- | --- |
| YulangClosure.PaperTypes.MapperPlanTyped.inversion | none |
| YulangClosure.PaperTypes.MapperPlanTyped.sameIdentity | none |
| YulangClosure.PaperTypes.MapperPlanTyped.typeTransport | propext, Quot.sound |
| YulangClosure.PaperTypes.mapperPolarityGoodTyped | propext |
| YulangClosure.PaperTypes.mapperPolarityBadNotTyped | propext, Quot.sound |
| YulangClosure.PaperTypes.OperationDeclarationResolved.typeTransport | propext, Quot.sound |
| YulangClosure.PaperTypes.operation_declaration_instantiation_subst | propext, Quot.sound |
| YulangClosure.PaperTypes.PaperValueTyped.subst_explicit | propext, Quot.sound |
| YulangClosure.PaperTypes.ValuesTyped.typeTransport | propext, Quot.sound |
| YulangClosure.PaperTypes.ValuesAllTyped.typeTransport | propext, Quot.sound |
| YulangClosure.PaperTypes.RecordPayloadsTyped.typeTransport | propext, Quot.sound |
| YulangClosure.PaperTypes.PaperComputationTyped.typeTransport | propext, Quot.sound |
| YulangClosure.PaperTypes.PaperContinuationTyped.typeTransport | propext, Quot.sound |
| YulangClosure.PaperTypes.MapperPlanTyped.mk (constructor) | none |

No sorryAx, project axiom, Classical.choice or failed theorem appears. This is inspection of retained primary evidence, not fresh kernel checking.

Material failure evidence is preserved: primary invocation 1 used Lake-level `build -j1 -M1024` and exited 1 with `error: unknown short option '-j'` before Lean checking. Contract r2 charges it and reallocates the unchanged total envelope to worker 5 / primary 3. Primary invocation 2, `lake build +YulangClosure.PaperOperationMapperTyping`, exits 0; invocation 3, `lake env lean -j1 -M1024 .lake/R24Audit.lean`, exits 0 with all 13 parser records validated. The project supplies per-Lean -j1/-M1024. Reported tool-observed successful wall intervals are approximately 13.2 and 1.2 seconds, not separately instrumented CPU/checker time; the initial CLI error is 0.1-second process time / 0 checker seconds. All three calls remain charged. No log is rewritten as failure-free or relabeled as reviewer/worker execution.

## Parent application and first remaining premise

After primary adjudication, this artifact supplies the explicit payload/response adapter premises required by paper :718, exact inversion/common identity, and their transport under arbitrary sigma on the actual mapper. It also supplies one checked polarity discriminator. It does not prove a mapper's actual code typings merely from signatures.

The first remaining mapper seam is integration with the still-omitted mapOperation computation typing rule and its underlying computation/body derivation, then actual frame/continuation composition, response plugging, term substitution/freshening and one-step preservation. Owner: primary/source-proof intake under a new exact packet. `R23-TEMPLATE-CALLER-CONTEXT-EMBEDDING-1`, R18 correspondence, other omitted rules, full paper substitution, inference/executor, original A/B, source/native/Rust and production remain OPEN. No semantic promotion or proof of the whole parent follows from this review.

## Resource use and cessation

Reviewer **0 Lean/Lake/checker calls / 0 checker seconds**, no tests/build/install/network commands, generated output, candidate repair, Git mutation, child delegation, scheduling or external contact. Exact active-time telemetry is unavailable and is not invented; this one bounded review stops without renewing the shared envelope. Only `tasks/agent-loop/inbox/paper-typing-subst-r24-review.md` was written. No command or descendant remains active. **Report frozen; reviewer STOPPED and all writes ceased.**
