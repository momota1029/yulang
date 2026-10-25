# R22 independent source/spec review — frozen revision 1

Verdict: **NO BLOCKING, MAJOR OR MINOR FINDINGS** within the fixed invocation-instance typing prerequisite. Registered-body typing and the full paper/execution/source-native parents remain OPEN.

Reviewer `/root/r16_independent_review`, non-author and non-repairer. Requested role: independent source/spec reviewer; requested model/effort unspecified; observed model/effort UNKNOWN. Runtime environment exposed shared `CODEX_SESSION_ID=01a172ef-fec1-72e3-bd47-bc4d7f51d6aa` and `CODEX_THREAD_ID=01a17361-f800-7370-bd4a-8bf93d07f843`. These are observed environment values, not inferred new per-packet session IDs. No descendants. Before substantive review, the metadata/hash-only receipt reported zero R22 authorship, edits, checker calls and review activity. The primary subsequently acknowledged its recorded receipt in `16f68e72b` and review start in `747cd0bf6`; substantive review began only after that acknowledgement.

**Source-only review: 0 Lean/Lake invocations, 0 checker seconds.** The retained primary checker output is independently inspected evidence, not reviewer execution or a new kernel receipt. Only this exact leased report was written.

## Frozen target and hash reconciliation

Reviewed immutable commit `5fb19dddc9a3d49c0b680618cf09bbd5fb0f992e`. Read-only `git show` extracted the named blobs and compared fixed commits; no moving diff, index/ref update or other Git mutation was used. Checked-out target bytes matched the frozen commit before review and at hash reconciliation.

| Frozen input | SHA-256 |
| --- | --- |
| tasks/agent-loop/sprints/paper-execution-typing-r22-template-call.md | 190841c2881a73ad66e9461642486bd01111cf9c037ea4bac28c7e60ef62b54b |
| notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean | e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932 |
| notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean | 3b1588bff2d28a3db7aa241c930495b84f090e880ad49ac8fb2d593d54943d41 |
| tasks/agent-loop/inbox/paper-typing-subst-r22.md | b41e72765894a205d4eac7a27f14a61e5cf3dce4bced059e55ba8b175a228356 |
| tasks/agent-loop/inbox/paper-typing-subst-r22-primary-verification.txt | 64ffb5bae31657a0f4302a482a988c48203057bc6b0710fda4b4f3be4ae94290 |
| notes/theory/lean/YulangClosure/PaperExecutionBinderLaws.lean | 568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a |
| notes/theory/lean/YulangClosure/PaperTypeSubstitution.lean | 02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861 |
| notes/theory/lean/YulangClosure/PaperTypeFormation.lean | 29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13 |
| notes/theory/lean/YulangClosure/DeclSubst.lean | f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258 |
| docs/yulang-operational-type-safety-ja.tex | a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b |

All frozen direct dependencies matched. The dedicated worktree source files at `/tmp/yulang-r22-templatecall/notes/theory/lean/YulangClosure/` also match the two committed source hashes. Its auxiliary `.lake/R22Audit.lean` matches hash `ff63bb4a3a557699c7a88beca4d26008f7f71039eaa066a6324c4f1ae309182c` pinned in the committed worker handoff. This ignored scratch audit is identified by that hash, not claimed to be a separately committed source blob.

Read the exact contract, manuscript :129/:243, template context :194–199 and original parent :953–977. Previously read root AGENTS, goal-driven sprint rules and Lean proof skill/source/execution references remain applicable. Research draft status is not semantic-adoption authority.

## Source/spec and proof assessment

All Lean names below have namespace prefix `YulangClosure.PaperTypes`.

1. **One complete resolved code entry.** `TemplateBody` (Syntax:134–136) stores identity, type arity, all formals, result and executable body. `templateIdentity` (:492–493) reads only the lookup key; the declaration witness remains the complete entry. `TemplateDeclarationResolved` (:627–631) requires membership, that key, and equality of every same-key member with the complete witness. Distinct entries with the same key cannot satisfy it. Identical repeated entries may occur but resolve to the same full code entry; no occurrence-uniqueness or blanket list-Nodup theorem is claimed. The definition is a resolution premise, not a proof that every declaration table is resolved.

2. **Exact invocation instance and arity.** `PaperComputationTyped.template` (:814–821) requires resolution of `.mk identity typeArity formals result body`, exact `typeArguments.length = typeArity`, and ValuesTyped for the actual arguments at `formals.map (instantiateType typeArguments)`. The conclusion uses the literal same typeArguments vector for `instantiateType typeArguments result`, and preserves the raw invocation identity/vector/actuals. D/Xi/Gamma are shared throughout. `ValuesTyped.nil/cons` (:633–639) aligns all ordered actuals and formal types, enforcing equal list lengths without zip truncation or component permutation. No independently selected formal/result instance, scope restriction or additional safe-body assumption appears.

3. **Body preservation is concrete, body typing remains open.** Actual `mapTemplateBody` (:495–499) retains identity/arity and maps every formal, result and the actual executable Computation body under `liftSubN arity sigma`. `mapDeclarationTable` (:545–550) maps the templates list with that function; raw template mapping also retains identity and maps every type argument and actual value under the same sigma. Code is not erased or mapped as identity. This preserves the stored witness through substitution, while manuscript :129 and :243 separately require a registered-body derivation under the prescribed formal environment. No such body-typing theorem or table-well-typedness instance is delivered. The constructor, coverage comment, worker handoff and fixed contract explicitly keep it OPEN, so the invocation relation is not used as an execution-safety definition.

4. **Resolution transport has the right quantifiers.** `templateIdentity_mapTemplateBody` (TypingSubstitution:121–124) preserves the key for every sigma and complete entry. `TemplateDeclarationResolved.typeTransport` (:127–141) transports an existing resolution to the list of mapped complete entries. It obtains a preimage for each mapped member through List.mem_map, recovers the original key, invokes original whole-entry uniqueness and maps that equality. It assumes neither substitution injectivity nor uniqueness generated merely from equal signatures. It retains the exact mapped body and all other entry fields.

5. **Formal/result substitution uses one argument vector.** `instantiateFormalTypes_subst` (:45–54) quantifies over arbitrary arguments, sigma, arity with actual arguments.length=arity, and every formal list. Its equality is
   `map (subst sigma) (map (instantiateType arguments) formals) = map (instantiateType (mapTypeArguments sigma arguments)) (map (subst (liftSubN arity sigma)) formals)`.
   It applies the existing `instantiateType_subst` (:25–42) independently to each ordered formal using the same argument vector and same arity evidence. The new common-recursion case (:434–449) maps resolution and argument-count equality, applies its ValuesTyped IH at the same arbitrary sigma, rewrites the full formal list with that lemma, rewrites the result with `instantiateType_subst`, and rebuilds the constructor. The declaration body is the actual mapped body from resolution. No mathematical conclusion is moved into an added premise.

6. **Inversion retains the single witness and exact result.** `PaperComputationTyped.templateInversion` (:538–553) starts from an actual raw invocation derivation at arbitrary resultType. Constructor inversion returns one typeArity/formals/result/body tuple, the unique resolution of that entire entry, exact invocation arity, all actual-argument typings at the same formal instance, and `resultType = instantiateType typeArguments result`. It does not change the body witness or substitute an unrelated existential output/instance. The sole input typing premise is the derivation being inverted.

7. **Existing language and transport scope are preserved.** Fixed-commit comparison with accepted R21 changes only the identity/resolver definitions, partial-coverage comment, one invocation constructor, four helper/inversion theorems and one recursor case. Existing raw mappings and every prior typing constructor/premise are untouched. Independent counting of frozen blobs gives 40 judgment constructors and 40 common-recursion case proofs. The six printed transport statements retain arbitrary sigma, D/Xi/Gamma, subjects/lists and type indices, with only the original derivation as typing premise; continuation response/result remain distinct. Public wrapper statements/proofs are unchanged. R18's raw variant field is not interpreted, omitted constructors are not removed from the accepted source domain, and no new witness policy is introduced.

8. **No axiom/checker escape.** Source search across the six-module imported proof cone found no sorry/admit/axiom/skipKernelTC/native_decide/implemented_by/unsafe/set_option matches. Audit display options do not disable checking. No project axiom, circular typing-as-safety definition, assumed LocalLaws or proposition definition is promoted to a concrete source instance.

## Audit/log correspondence and complete axiom lists

Inspected the pinned auxiliary audit source and committed primary verification output :2844–2996. Textual comparison confirms all 11 #check names match all 11 axiom-report names in order (10 theorem declarations and the constructor); all 10 theorem begin/end markers are present. The audit requires `.thmInfo`, prints exact types, collects full dependent axioms and rejects dependencies beyond the existing standard allowlist. The four new theorem types and all six transport types agree with the actual statements inspected above. Full reported axiom lists:

| Fully qualified declaration | Complete reported axioms |
| --- | --- |
| YulangClosure.PaperTypes.PaperValueTyped.subst_explicit | propext, Quot.sound |
| YulangClosure.PaperTypes.ValuesTyped.typeTransport | propext, Quot.sound |
| YulangClosure.PaperTypes.ValuesAllTyped.typeTransport | propext, Quot.sound |
| YulangClosure.PaperTypes.RecordPayloadsTyped.typeTransport | propext, Quot.sound |
| YulangClosure.PaperTypes.PaperComputationTyped.typeTransport | propext, Quot.sound |
| YulangClosure.PaperTypes.PaperContinuationTyped.typeTransport | propext, Quot.sound |
| YulangClosure.PaperTypes.instantiateFormalTypes_subst | propext, Quot.sound |
| YulangClosure.PaperTypes.templateIdentity_mapTemplateBody | propext, Quot.sound |
| YulangClosure.PaperTypes.TemplateDeclarationResolved.typeTransport | propext, Quot.sound |
| YulangClosure.PaperTypes.PaperComputationTyped.templateInversion | propext, Quot.sound |
| YulangClosure.PaperTypes.PaperComputationTyped.template (constructor) | does not depend on any axioms |

The log additionally prints the key/resolver/mapTemplateBody definitions, including actual executable-body mapping. No sorryAx, Classical.choice, project axiom or failed declaration appears. The worker handoff correctly remains a constructed-but-unchecked worker receipt; the later separate primary verification supplies the actual checker results and does not retroactively attribute checker execution to the worker.

Primary verification summary :2999–3005 records four actual calls: native Lake version exit 0 (Lake 5.0.0-src+eb6cafb / Lean 4.35.0), Lean version exit 0 (4.35.0 commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc), focused source build exit 0 (7 jobs), and exact `.lake/R22Audit.lean` audit exit 0 with bundled validate_audit PASS for all 10 theorems. Exact process durations were not retained, and this review invents none. Linter warnings and successful build completion are preserved. This is source-only examination of committed primary evidence, not independent checker execution or self-certification.

## Parent application, first remaining premise and limits

R22 supplies the represented invocation-instance rule and its arbitrary-sigma preservation, conditional on the actual resolution/arity/ValuesTyped premises in the constructor. It also supplies inversion and conditional resolution transport. It does not establish concrete complete-table well-typedness from a proposition definition.

The first remaining template-execution premise is manuscript :129/:243: construct the resolved stored body's actual typing derivation in its prescribed formal environment, then prove body/term/type instantiation and execution correspondence. Owner: primary/source-proof intake under a new exact packet. It must use the same stored body witness, not replace it. Full-paper rule coverage, the separate R18 variant correspondence, nominal/switch/other omitted forms, recursive graph guards, inference/executor safety, original A/B, source/native/Rust and production remain OPEN. No semantic promotion or full-parent closure follows from this review.

## Cessation and resource receipt

Reviewer **0 Lean/Lake invocations / 0 checker seconds**, no tests/build/version/network/install commands, generated cache output, candidate edits, Git mutations, children, scheduling or external contact. Exact model active-time telemetry is unavailable and is not invented; this bounded review stops without renewing the shared sprint envelope. Only `tasks/agent-loop/inbox/paper-typing-subst-r22-review.md` was written. No active subprocess or descendant remains. **Report frozen; reviewer STOPPED and writes ceased.**
