# R21 independent source-only review — frozen revision 1

Verdict: **NO BLOCKING OR MAJOR FINDINGS** for represented tuple split typing/inversion, tuple-introduction composition and arbitrary simultaneous type substitution.

Reviewer `/root/r16_independent_review`, freshly assigned and not an R21 author or repairer. Active acknowledgement preceded inspection. Runtime environment exposed shared `CODEX_SESSION_ID=01a172ef-fec1-72e3-bd47-bc4d7f51d6aa` and `CODEX_THREAD_ID=01a17361-f800-7370-bd4a-8bf93d07f843`; these are observed environment values, not inferred per-packet agent IDs. Model/effort telemetry unavailable. No descendants.

**Source-only review: 0 Lean/Lake invocations, 0 checker seconds.** Retained checker receipts were inspected; no fresh reviewer kernel acceptance is claimed. The only write is this exact leased review report.

## Frozen target and dependencies

Reviewed immutable integration commit `c62673066ae9c366f150ec1cffa13a44f2f2a877`, with read-only `git show` extraction and a fixed-commit comparison against accepted R20 baseline `b77fe13183e7ec80a95f08f919f34e832962c977`. No moving diff or Git mutation was used. The named source/audit files' commit-blob hashes and checked-out bytes matched the assignment.

| Input | SHA-256 |
| --- | --- |
| notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean | e025922217e5c5fc6d68780936acd99ac8252267f8c262b50da790a72cf73b0e |
| notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean | db213de9e97d965fb5e105f75009c9ec4f64e02892e5fdf3a8132317cc5e5f1d |
| tasks/agent-loop/inbox/paper-typing-subst-r21-audit.lean | 6c612cd3a4025e2e8b709ce1ec32090bfc82de48c0e25fb86d88c64ee6cc93d7 |
| notes/theory/lean/YulangClosure/PaperExecutionBinderLaws.lean | 568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a |
| notes/theory/lean/YulangClosure/PaperTypeSubstitution.lean | 02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861 |
| notes/theory/lean/YulangClosure/PaperTypeFormation.lean | 29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13 |
| notes/theory/lean/YulangClosure/DeclSubst.lean | f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258 |
| docs/yulang-operational-type-safety-ja.tex | a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b |
| tasks/agent-loop/sprints/paper-execution-typing-r21-split.md | 7bdab04134682ce01ebf723010c26a4d3a896cf2d024c8df0384f25cdc44d5ad |
| tasks/agent-loop/inbox/paper-typing-subst-r21.md | 1ab3773ae5d71b877f124c7bfc3ba96ab39bdc52df9cb588a0d4de5ab99a623d |
| tasks/agent-loop/inbox/paper-typing-subst-r21-primary-verification.txt | 6188acac1bdd0a77b80a05e4b970aa874b107688e4c4c390ea0dd3584838f440 |

All frozen direct source dependencies matched. Read R21's fixed contract and original manuscript rule :229, tuple introduction :216, single-binder rules :222,226, and original simultaneous-substitution parent :953–977. Previously read root AGENTS, goal-driven sprint rules and Lean skill/source/execution references govern this leaf. Manuscript/correction research status is not new language-semantic adoption authority.

## Source, order and proof assessment

All Lean names below are prefixed `YulangClosure.PaperTypes`.

1. **Ordered context extension is grounded in the existing convention.** The paper's split premise is `Gamma, xbar:Abar |- body:B`, with component order fixed by the tuple. Existing `PaperValueTyped.valueLambda`, `PaperComputationTyped.letE` and `PaperContinuationTyped.continuation` represent a single right-appended binder by cons at the head. `lookupTypeEnvironment` reads that head at index 0. Repeating this convention for ordered `[A1,...,An]` yields `An :: ... :: A1 :: Gamma`, precisely `reverse types ++ Gamma`. New `extendTupleEnvironment` at Syntax:523–524 has that definition. In particular, `[A1,A2]` yields `[A2,A1] ++ Gamma`, with A2 at index 0 and A1 at index 1; the empty extension yields Gamma. No conflicting represented multi-binder convention was introduced. This is the local de Bruijn context interpretation; no source-name resolution or native binder-layout theorem is claimed.

2. **Exact split premises and arity.** `PaperComputationTyped.split` at Syntax:752–757 requires `binders.length = types.length`, the actual tuple at `argsSyntax types` in D/Xi/Gamma, and the actual body at the original resultType in D/Xi/extendTupleEnvironment types Gamma. D/Xi and the Gamma tail are shared. `argsSyntax` encodes component types in source order, and existing `ValuesTyped.nil/cons` pairs every value with the corresponding type without truncation. Thus tuple composition retains exact component arity; no zip, list shortening, fixed ambient scope or extra context premise is used. Raw binder names remain the original ordered list.

3. **Genuine inversion preserves the result and shared list.** `PaperComputationTyped.splitInversion` at TypingSubstitution:488–499 takes an actual raw-split derivation at arbitrary resultType. Inverting its constructor recovers one ordered type list, the exact binder/type length equality, tuple typing and body typing under the named extension. Both recovered premises use that same list, and body typing retains the input resultType directly. No new result is existentially substituted, no conclusion evidence is assumed, and no witness is independently selected for the tuple and body.

4. **Tuple-introduction composition has the requested scope.** `PaperComputationTyped.splitTuple` at :502–512 takes ordered ValuesTyped values types, explicit binder/type arity and the original extended-body typing. It builds the existing tuple introduction and then split, concluding the same resultType with the same D/Xi/Gamma. ValuesTyped enforces values/types alignment, so no payload permutation is hidden. This is a typing derivation; it does not establish split evaluation or term-substitution preservation.

5. **Extension commutation and arbitrary substitution are exact.** `mapTypeEnvironment_extendTupleEnvironment` at :19–23 quantifies over every sigma, type list and environment, with no formation/closedness hypothesis. Its actual equality maps the extended environment to extension by the same ordered mapped type list over mapped Gamma. The proof unfolds the list operations and uses map/reverse/append algebra. New recursor case :291–302 maps arity using List.length_map, rewrites tuple typing using typingArgsSyntax_subst, rewrites body environment with the extension lemma, and rebuilds split. Tuple and body use the same arbitrary sigma. The unchanged raw split map at Syntax:232 preserves the binder list and maps tuple/body together. There is no term-binder-induced type-substitution lift or component reordering.

6. **Prior cases and quantifiers remain intact.** Fixed-commit diffs show only the helper and split constructor in Syntax, and the extension theorem, one recursor case and two split theorem blocks in TypingSubstitution. All prior raw maps, constructors, premises and wrappers are unchanged. Independent counts on the frozen blobs give 39 judgment constructors and 39 common-recursion case proofs. The exact six transport signatures retain arbitrary sigma, D/Xi/Gamma, full raw subject/list and all type indices, with the original derivation as their only typing premise. Continuation response/result remain separate. No R18 variant interpretation, narrowed source domain, changed forall freshness, stronger ambient hypothesis or new witness was introduced.

7. **No proof escape.** The six-module direct proof-cone source search found no sorry/admit/axiom/skipKernelTC/native_decide/implemented_by/unsafe/set_option matches. The separate audit's options affect printed names/universes only. No project axiom, assumed LocalLaws, circular typing-as-safety definition, dependency change or proposition definition is counted as a concrete source instance.

## Retained theorem types and axiom evidence

Inspected the complete worker audit block at handoff:2911–3049, the exact audit source and the primary verification output. The audit checks theorem declaration kind, prints full types and complete axioms, rejects dependencies outside the existing standard allowlist, and prints nine complete begin/end pairs. Results:

| Fully qualified declaration | Complete reported axioms |
| --- | --- |
| YulangClosure.PaperTypes.PaperValueTyped.subst_explicit | propext, Quot.sound |
| YulangClosure.PaperTypes.ValuesTyped.typeTransport | propext, Quot.sound |
| YulangClosure.PaperTypes.ValuesAllTyped.typeTransport | propext, Quot.sound |
| YulangClosure.PaperTypes.RecordPayloadsTyped.typeTransport | propext, Quot.sound |
| YulangClosure.PaperTypes.PaperComputationTyped.typeTransport | propext, Quot.sound |
| YulangClosure.PaperTypes.PaperContinuationTyped.typeTransport | propext, Quot.sound |
| YulangClosure.PaperTypes.mapTypeEnvironment_extendTupleEnvironment | propext |
| YulangClosure.PaperTypes.PaperComputationTyped.splitInversion | propext, Quot.sound |
| YulangClosure.PaperTypes.PaperComputationTyped.splitTuple | propext, Quot.sound |
| YulangClosure.PaperTypes.PaperComputationTyped.split (constructor) | does not depend on any axioms |

The helper's definition is printed separately as `fun types environment => types.reverse ++ environment`; it is correctly not counted as a proved theorem. No sorryAx, Classical.choice, custom axiom or failed declaration appears in the retained axiom lists. The primary verification output contains a successful focused build completion and the same complete type/axiom surface. This independent review is of those source meanings and retained receipts, not a replacement kernel run.

Producer records native pinned-distribution Lake commands `build +YulangClosure.PaperExecutionSyntax +YulangClosure.PaperExecutionTypingSubstitution` and `env lean -j1 -M1024 .lake/R21Audit.lean`, both exit 0, respectively 21.260374 and 0.651341 seconds; 2 literal calls / 21.911715 checker seconds. Pin: Lean 4.35.0; LEAN_NUM_THREADS=1. Bundled audit_source/validate_audit PASS is retained. Linter warnings are visible in full build logs; no checker failure is disguised. No fresh version or checker receipt is invented by this reviewer.

## Parent application and remaining owner

The split constructor applies the paper :229 premises directly in the established cons convention. Existing tuple introduction supplies its tuple premise from ordered ValuesTyped; inversion recovers arity and original result, and the common substitution theorem now covers the represented split case for arbitrary sigma. No further mathematical premise is introduced for that local typing seam, subject to primary adjudication.

Full paper substitution and source scope remain OPEN. First unresolved manuscript-order introduction remains `R18-VARIANT-TYPEARG-CORRESPONDENCE-1`, owned by primary semantic/source intake; nominal, switch, other omitted rules and recursive graph guards retain their separate owners. Source/name-to-de-Bruijn and native tuple-binding correspondence, split reduction/term substitution, inference/executor safety, original A/B and source/native/Rust/production gates are not established by this result. The handoff preserves those boundaries and makes no completion overclaim.

## Resource use and cessation

Reviewer **0 Lean/Lake calls / 0 checker seconds**, no tests, installation, generated cache output, source repair, Git mutation, scheduling, child delegation or external contact. Exact active-time telemetry is unavailable and is not invented; this finite review packet stops without renewing the primary's shared sprint bound. Only `tasks/agent-loop/inbox/paper-typing-subst-r21-review.md` was written. No command or descendant remains active. **Report frozen; reviewer STOPPED and all writes ceased.**
