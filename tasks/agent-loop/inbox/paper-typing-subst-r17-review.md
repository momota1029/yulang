# R17.1 independent source review

Verdict: **NO BLOCKING OR MAJOR FINDINGS** within the assigned six-judgment transport and value-only forall-introduction scope.

Reviewer `/root/r16_independent_review`, independently assigned to R17.1 by `/root`; no authorship, repair, or edits to this R17 candidate. Active acknowledgement was sent before inspection. This review is source-only: **zero Lean/Lake invocations, zero checker seconds**. The supplied worker/primary kernel receipts are evidence inspected, not fresh reviewer execution. No claim of full-paper or production closure follows.

## Frozen inputs and authority

Candidate worktree `/tmp/yulang-r17-forall`; primary identifies its assigned baseline as `aacb81609`. No Git command was run to establish or modify that identifier.

Fresh SHA-256 matches:

| File under candidate worktree | SHA-256 |
| --- | --- |
| notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean | 8f4a32fd1c013ae78a161dadd52bed57cc7c99af5ae30fd30ba133de2c3f74a4 |
| notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean | b2975d38fccbf5c908741c3714b2b513b4b8706d80f3c009125c815d1b944d89 |
| notes/theory/lean/.lake/R17Audit.lean | 05e22fc223be25f2d7fc8894f8204e79e6040a3e5d6a344a419594ecbdbc9260 |
| tasks/agent-loop/inbox/paper-typing-subst-r17.md | fc23855facec8069ff3f4e72a2d7dc927680ceaaf68d2aa994cf715189b9efb6 |
| notes/theory/lean/YulangClosure/PaperExecutionBinderLaws.lean | 568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a |
| notes/theory/lean/YulangClosure/PaperTypeSubstitution.lean | 02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861 |
| notes/theory/lean/YulangClosure/PaperTypeFormation.lean | 29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13 |
| notes/theory/lean/YulangClosure/DeclSubst.lean | f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258 |
| docs/yulang-operational-type-safety-ja.tex | a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b |

Read the original contract in the main checkout, `tasks/agent-loop/sprints/paper-execution-typing-r17.md`, hash `510823d707f36c8cc33601d7d1ab78e2732015010ca705f74e1ed48c28fa69b3`, and `paper-execution-typing-r17-amendment1.md`, hash `183b789f4bb87c45cbe72074061763e65f93a733e8dce006d3e2dea11d7c0450`; both freshly matched. Root AGENTS and the already-read Lean skill/references and goal-driven sprint rules govern this leaf. No scope or budget was extended.

Revisited operational manuscript lines 203–207,237,953–977: universal introduction applies only to values, with the introduced variable fresh in the complete shared declaration/environment context; one substitution acts simultaneously throughout. The opening source-owner correction and corrected-core V1(b), read during the preceding review, remain applicable boundaries. Research drafts are not adopted semantics. Whole-parent scope is `docs/yulang-whole-proof-closure-ja.md` §1 and remains open.

## Source and proof inspection

All names below have namespace prefix `YulangClosure.PaperTypes`.

1. **Existing judgments preserved.** Direct diff against the frozen pre-R17 Syntax file shows exactly the six D/Xi parameter-to-index header changes and one new constructor block. Every previous constructor and side premise is otherwise unchanged. There are now 36 constructors: ValuesTyped 2; ValuesAllTyped 2; RecordPayloadsTyped 2; PaperValueTyped 18; PaperComputationTyped 11; PaperContinuationTyped 1. The common recursor proof contains 36 corresponding constructor proof terms. Context indices remain the same D/Xi/Gamma across all premises of each existing rule.

2. **Fresh binder represented concretely.** `PaperValueTyped.typeAbstraction` at Syntax:705–710 takes a Value body typed under `mapDeclarationTable shift D`, `mapGraphEnvironment shift Xi`, and `mapTypeEnvironment shift Gamma`, and concludes the actual `.typeAbstraction body : .poly bodyType` under D/Xi/Gamma. Its inline substitution `fun index => .var (index + 1)` is definitionally equal to accepted `shiftTypeSubstitution`. The new binder does not capture a type in any shared context: all outer free indices shift, including under declaration/template-local arities. There is no assumed freshness proposition, closed-context restriction, newly chosen witness, computation abstraction, or unshifted shared context.

3. **Arbitrary substitution is retained under the binder.** `PaperValueTyped.subst_explicit` at TypingSubstitution:114–379 generalizes each of its six recursor motives over arbitrary sigma while also indexing D/Xi. All ordinary constructor IHs use that same sigma. The new case at :217–229 invokes its body IH with `liftSub sigma`, changes only definitional inline-shift notation, and rewrites complete declaration, graph, and term-type contexts using accepted R16 commutation. It reapplies typeAbstraction to the transported body and maps the result with actual `subst` under `.poly`. Raw body mapping remains the original `mapPaperValue (liftSub sigma)`; no code map is replaced by identity.

4. **All represented constructor cases inspected.** Nil/cons transports retain whole lists. Record shape, presence, declared payload types, uniqueness and required labels are preserved; tags and ordered payload fields remain mapped. Both lambda entries retain their separate A/UA formal contexts. Intersection retains the same raw value for both derivations. Type application and roll/unroll use actual `instantiateType_subst` and binder lifting. Perform/request keep resolution uniqueness, arity, declaration identity and one mapped argument list; request additionally retains the original instance equality and correlated payload/response/result. Resume retains response/result separation. The continuation body preserves its response cons environment. All former cases remain in the proof; no case was replaced by a new premise.

5. **Six public transports inspected.** `ValuesTyped.typeTransport` (:382), `ValuesAllTyped.typeTransport` (:398), `RecordPayloadsTyped.typeTransport` (:414), `PaperComputationTyped.typeTransport` (:432), and `PaperContinuationTyped.typeTransport` (:445) retain arbitrary D/Xi/Gamma, raw subjects and result indices with only the original derivation as premise. The first three use finite list induction and the main value transport. Computation transport embeds with delay then inverts the transported delay; no other value constructor has that raw head. Continuation transport now quantifies over any Value continuation, then inverts its actual constructor, transports its body computation, and rebuilds it; this broadens the previous syntactic-head interface without narrowing any old instance. There is no circular theorem dependency: computation transport depends on the common value recursor theorem, and continuation wrapper depends on that completed computation wrapper.

6. **Concrete captured-context application checked.** `typeAbstractionSharedVariable` (:461–466) retains arbitrary D/Xi and starts with Gamma `[Ty.var 0]`. The constructor's body premise has Gamma `[Ty.var 1]`; term variable 0 therefore has type var1 and the conclusion is `poly(var1)`. It does not become `poly(var0)`. `typeAbstractionSharedContexts` (:469–479) additionally gives an actual operation declaration (identity 7, arity 0, payload/response var0), graph entry `(5,var0)`, and Gamma `[var0]`; its three displayed equalities shift each to var1. Its fourth conjunct applies the same constructor rule. The example is a concrete application, while the theorem transports retain unrestricted contexts.

7. **No dependency escape.** Imports are Syntax -> Formation/DeclSubst; BinderLaws -> Syntax; TypingSubstitution -> BinderLaws/DeclSubst. No cycle or BinderLaws edit. A source search across the six-file imported proof cone found no `sorry`, `admit`, `axiom`, `skipKernelTC`, `native_decide`, `implemented_by`, `unsafe`, or `set_option` matches. No proposition definition or LocalLaws parameter is promoted to an instance.

## Inspected checker evidence and limits

Read the complete retained invocation-6 output at handoff:9262–9404 and the exact audit source. The audit requires theorem declaration kind, prints each full type, prints complete axioms, and rejects dependencies beyond standard propext/Classical.choice/Quot.sound. Eight begin/end pairs are complete. Each delivered theorem below reports exactly **[propext, Quot.sound]**:

- `YulangClosure.PaperTypes.PaperValueTyped.subst_explicit`
- `YulangClosure.PaperTypes.ValuesTyped.typeTransport`
- `YulangClosure.PaperTypes.ValuesAllTyped.typeTransport`
- `YulangClosure.PaperTypes.RecordPayloadsTyped.typeTransport`
- `YulangClosure.PaperTypes.PaperComputationTyped.typeTransport`
- `YulangClosure.PaperTypes.PaperContinuationTyped.typeTransport`
- `YulangClosure.PaperTypes.typeAbstractionSharedVariable`
- `YulangClosure.PaperTypes.typeAbstractionSharedContexts`

The printed `PaperValueTyped.typeAbstraction` constructor likewise reports [propext, Quot.sound]; all six judgment signatures expose D/Xi/Gamma indices. The six transport printed types preserve `forall sigma`, arbitrary context/subject/type arguments and precisely the original typing premise; conclusions map all contexts and the actual subjects simultaneously. Continuation response/result remain separate.

These are retained producer audit results, not reviewer-generated receipts. The handoff records invocation 6 as `lake env lean -j1 -M1024 .lake/R17Audit.lean`, exit 0, 2.336589 seconds, with checker helper `audit_source`/`validate_audit` PASS; reported installed tools were Lean 4.35.0 commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc and Lake 5.0.0-src+eb6cafb. The primary supplied final call-12 PASS in this review assignment. No fresh checker run, generated output, dependency install, or rerun was performed by this reviewer. Earlier failures and invocation-accounting incidents remain preserved in the unchanged handoff/amendment; this review does not erase or authorize them retrospectively.

## Parent application and remaining premise

This candidate consumes accepted R16 commutation in the actual type-abstraction branch and establishes arbitrary simultaneous substitution for all **represented** rules, including that branch. It resolves the prior shared-context forall-introduction/transport seam without a new premise. It does not establish that the relation represents every manuscript rule.

The first missing introduction in manuscript table order is variant tag/payload/arity typing (`Value.variant`), followed by nominal introduction and other omitted constructors. Wrap, remaining eliminations, patterns, handlers/maps, primitive/template typing, recursive graph guards and full administrative forms still need faithful rules and transports. Owner: primary full-paper rule-coverage/source-proof intake under a new exact packet. Existing raw syntax remains intact; these are explicit omissions of the partial typing relation, not excluded accepted language features. Executor/inference safety, original A/B, source/native/Rust correspondence and production remain OPEN.

## Cessation

Only `/tmp/yulang-r17-review-report.md` was written. Candidate source, scratch, handoff, cache, main checkout and Git were read-only. No children, scheduling, installation, external contact or outstanding subprocess. Reviewer checker resources: **0 calls / 0 seconds**. Active review seconds were not separately instrumented; no exact telemetry is invented, and the finite source-review packet stops here without renewal of its 300-second bound. **Report frozen; reviewer STOPPED and writes ceased.**
