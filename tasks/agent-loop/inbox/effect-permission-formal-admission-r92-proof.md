# R92 proof handoff — frozen declaration and logical-admission audit

Sprint `EFFECT-PERMISSION-FORMAL-ADMISSION/20261101-R92`; contract revision 1, SHA-256 `a76c19080f240f5897dee4bc81e444ac4d73de28d70442877e0a8861b673e85e`. Assignment `/root/r92_formal_admission_proof`; handoff revision 1. Baseline `0bdac5f73ebb54d4049e8a8b8896330beda1c6f5`; admission commit `7462f2280` supplied by primary, not independently inspected through Git. Sole leased/changed path: this file. Author: this leaf; descendants: none. Requested role: registered `lean_prover`; requested model/effort not supplied in the fixed packet; effective observed model/effort **UNKNOWN/UNKNOWN**. Actual active assignment is this canonical task; backend worker/session identity beyond that is UNKNOWN. Startup acknowledgement sent to `/root`; first clock observation `2026-10-31 16:08:37 UTC`.

**Outcome: candidate audit and exact missing source premise; no new theorem or source-qualified counterexample.** Frozen R91 candidate remains constructed and unchecked. This leaf ran zero Lean/Lake/elan/checker, test or build commands. It constructed only a proposed in-memory input byte string, never a source/scratch file. No checker/model/runtime receipt is inferred from configuration or source text. Independent review and any authorized execution belong to the primary.

## Original claim, selected source and pins

Read root AGENTS.md/AGENTS.pre-sprint.md, current state/README, rules/goal-driven-sprints.md, rules/design-authority.md, the Lean skill plus sources/execution references, the R92 contract and its exact 105-entry manifest. Read-only Python byte/hash validation matched **105/105 unique paths**, zero mismatches. Manifest SHA-256 `080e254e9eb19dd4df54bc28aca6bdf45478eb413e9f8d8b9df76dad04c04cc2` (21,726 bytes). No manifest input was edited.

Original parent: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1,3,5,7, SHA-256 `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271`. Every supported original source program, lawful finite construction history and actual retained qualified occurrence remains quantified. Original typing/principal coverage, soundness, ordinary progress/termination, scopes, captures/providers, recursive monomorphic sharing, lawful independent uses, complete Call/effects and one original joint witness/strategy remain required. The old cross-level helper rejection is not a current counterexample: `notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6, SHA-256 `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae`, replaces qualification with paths entirely in the immutable-birth induced graph, while retaining cross-level source references.

The relevant original source specification is the selected Source-Generalize definition, `notes/design/2026-10-08-source-generalize-definition.md` §§2–3 (`46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38`), selecting construction §§3–5 in `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` (`e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`). Read especially §3.3's constructor-owned Desc/Shared/ViewLogic/EventField/EventProof distinction and §5.1–5.2's fixed dependency closure and allocation keys. Source-Generalize selects definitions and conditional local results; it supplies no missing concrete primitive/constructor law. The original paper's non-let completeness restriction in parent §3 remains intact; no new PDF examination or whole-language paper proof is claimed.

Call interface definition `notes/design/2026-10-08-call-source-interface-definition.md` §§2–4 (`20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c`) retains complete contextual declarations/references, dependent Call fields and all alternatives. Static incidence is not complete C0, membership or licensing. Authoritative top-level principles (`7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`) prohibit narrowing ordinary source behavior for proof convenience. Research drafts add no semantic authority.

R91 candidate `notes/theory/lean/YulangClosure/OriginalFormalRegistrationSupplierR91.lean`: **14,816 bytes**, SHA-256 `d5187d6dce15a3c6a8979c5e6e88a097fcd7815a53fc81ed4770fd137750de2b`. R90 App bridge: **11,964 bytes**, SHA-256 `cd836e6b12a4deff0e5acf83523faedfb883240b6d019f17ec5a7d294b8c205a`. Both are unchanged.

## R91 declaration census and parent application

All nine names below have prefix `YulangClosure.OriginalFormalRegistrationSupplierR91.`. The appendix copies every theorem's source-declared type verbatim through `:=`; these are **not emitted Lean types**. Actual R91 printed types and every complete axiom result remain **UNKNOWN / not produced**. Source lines 234–245 request `#print` of two proposition definitions and five `#check @...` / `#print axioms ...` pairs. `namePremises` and `nameCore` are additional definitions, not theorems.

| Declaration | Exact result and missing inference |
| --- | --- |
| `SharedSupply` (`def`, line 35) | Let `delivered := environment.extend (sharedBinder parameter) (environment.anchorValue (sharedBinder parameter))`; concludes `∃ after, decode readout delivered = some after ∧ formalContract after parameter = contract ∧ Judgment kernel delivered (checkedBody parameter)`. It does **not** include an explicit Shared-anchor admission conjunct or a Name readout. Defining this proposition proves no instance. |
| `EntrySupply` (`def`, line 46) | Value: **all** admitted original Return candidates imply SharedSupply at that Return extension. Computation: SharedSupply at the original incoming environment; no Force/returned Value. It is a mode-indexed conclusion, not a concrete source supplier. |
| `actual_build_shared_supplier` (`theorem`, line 58) | For arbitrary `s`, View, Introduction, FormalAssignment, Inputs, RuntimeReadout, LocalAdmissions, original Kernel, complete Prior and Lambda annotation, an actual `Satisfies (localKernel ...) ... (Build ...lambda...)` yields exact description/ViewPacket payloads and admissions, then **every** admitted invocation yields a receipt and EntrySupply for `(intro.selection assignment).contract`. Uses `OriginalFormalAdmission.actual_build_from_whole_telescope`, the two entry preservation lemmas, and actual Shared continuations. Preserves one selected contract through runtime receipt/Return/Shared, ending at checkedBody. It neither constructs the `solves` premise nor crosses EventProof/App logic or interprets Name. The proof uses actual Shared admission internally but the chosen SharedSupply result forgets that explicit conjunct. |
| `namePremises` (`def`, line 118) | Exactly the resolvedSameBinding and computedFetchOnce atoms with the whole supplied Binding. |
| `nameCore` (`def`, line 124) | Original Name rule with those two atoms and empty children. |
| `resolved_formal_name_rule` (`theorem`, line 129) | For arbitrary Name Mark/context/name/Binding, lexical lookup equality and `binding.kind = .formal`, gives the exact original sourceRules equation, with none/some annotation branches. Complete binding, entry, annotation, owner and singleUse are retained. This is syntax/lookup, with no contract semantics. |
| `resolved_formal_name_iff` (`theorem`, line 138) | For any Value type, Kernel and environment, under the same lookup/formal hypotheses, original SourceJudgment iff incoming annotation Local premises and both Name Local atoms in the same environment. Arbitrary `kernel.atom` remains uninterpreted. |
| `app_formal_name_seam` (`theorem`, line 174) | Inverts an actual annotated/unannotated App with a resolved formal Name callee. Keeps incoming App annotation premises, **one** admitted App ViewLogic witness, all App Local clauses/checks, callee annotation, both whole-Binding Name atoms and arbitrary argument SourceJudgment under that same extension. No fresh callee/argument witness; no equality with the registered formal contract follows. Applies checked R90 `app_derivation_iff` and candidate Name inversion. |
| `event_proof_replacement_admitted` (`theorem`, line 211) | For every mode, decoded incoming environment, occurrence and replacement Contract, sets base.logical to True and constructs the concrete declaration payload at `⟨body.site,eventProof,0⟩`; it is admitted and decode of its extension reads **replacement**. No original Build/body/Name judgment is established in this permissive model. There is no distinctness premise/conclusion: to refute a universal preservation assertion in this interface one must choose a model with distinct contracts. This is an interface discriminator, not an adopted interpretation or supported-source counterexample. |

The supplier's `FormalAssignment` is a function from original Parameter, route and pre-invocation `ScopeValues` to opaque `s.Descriptor`/`s.Interface`; it contains no proof of complete source formation. `Sorts.Descriptor` and `Sorts.Interface` are abstract Types. The full contract is not projected here, but retaining that opaque value does not itself establish that all original fields are represented by a concrete instance. `Telescope`/`ScopeValues` retain the ordered scope-indexed payloads and structural binder-kind checks; they do not by themselves establish original semantic admission or authentic whole-source history. No stronger hypothesis or restricted source fragment is introduced by this audit.

## First missing source law and falsifier

Let `p := intro.parameter`, `C := (intro.selection assignment).contract`, and `d` be the decoded state just after the actual Shared delivery. R91 constructs `formalContract d p = C`. In `OriginalFormalShared.checkedBody` the body branch's first extension is the actual existential `⟨p.body.site,eventProof,0⟩`. The sibling pattern derivation shares the incoming environment; it does not justify transporting a different body state. `OriginalFormalAdmission.localAdmissions` delegates **every** eventProof payload to `base.logical`. Only the exact Lambda ViewLogic Binder is locally restricted to `ViewPacket.encode`; another App ViewLogic Binder delegates to base. If an App and Lambda have equal flat Binders, that branch instead receives the Lambda restriction—no global raw-Site freshness is assumed.

`OriginalSourceEnvironment.decodeFrame` ignores the logical kind and applies `Decoded.logical`. Its descriptor/interface fields are updated with ordered `put`; later entries overwrite matching flat Endpoints. Its eta, joint witness and viewMeaning are also replaced. Actual objects/current history and fixedFrames preservation therefore does not establish the descriptor/interface or dependent logical-field invariant. R91's replacement theorem exhibits the exact allowed overwrite at the first EventProof step under permissive base admission.

**Missing constructor/law owner:** original source logical introduction/admission and occurrence-aware readout (`OriginalSourceGeneration.sourceRules`, `OriginalSourceEvents` occurrence/telescope constructors, `OriginalSourceEnvironment.LocalAdmissions.logical` / `DataAdmitted` / `decodeFrame`, consumed by `OriginalFormalAdmission`). It must construct the lawful payload and its protected-field/write relation from the **actual source occurrence and dependency telescope**, then prove that the same registered complete contract is read at its descendants. The law cannot be a new premise asserting `formalContract after p = C`, a site-only filter, or globally empty logical writes: original body inference Desc declarations and independent proof fields remain allowed at their actual scopes.

Occurrence identity is materially absent from the flat API: `Coordinate` contains declaration/route/Endpoint, but `Binder` contains only site/kind/arity; local admission dispatch compares this flat Binder. `declaration` and `formalContract` use only `⟨formal.site,descriptor⟩` in the decoded map. `distinct_routes_same_flat_binder` distinguishes coordinates while equating those flat Binders; it is not a proof of two admissible source histories. A correct constructor must account for route, incoming description frame, original proof-region path and actual event incidence, or derive an authentic source separation/readout fact. Adding a raw-Site injectivity assumption would strengthen the unchanged claim.

The source specification fixes these keys: ViewLogic `(incoming frame,q,original description-region path)`; EventProof `(incoming frame,actual event key,q,original proof-region path)`; actual EventField retains original event origin, actual parent event path and occurrence. Shared stays once at its original binder with all dependencies. Logical EventProof may differ per description frame while its runtime operands remain shared. `owners`/`forestOwners` retain descent/sibling/choice routes and extend all scope entries; `binderOwner` emits event/Shared/EventProof owners, not a general ViewLogic write/admission certificate. Those structural registrations supply no missing decoder/readout law.

Concrete falsifiers for the missing law: a supported original route resolves to another occurrence; an admitted logical payload overwrites a protected descriptor/interface or dependent fixed field; two source-distinct registrations collapse into one flat slot; a same-event alias gets another runtime tuple; or a Name consumes a different complete tuple. The current permissive-model overwrite is evidence that the interface lacks the law, not evidence that the adopted source admits that overwrite.

Even after this preservation step, a second bridge remains: the actual resolved Name must read the selected object/interface, and App must read that same callable at its returnedValue endpoint. `OriginalSourceInterpretation.ValueNameAtom` covers ordinary **Value** formals: it reads `inputs.installed event address`, while Shared writes `Decoded.installed`. The equality between those independent readouts is not automatic. Its endpoint is the Name's finalRoot, while `formalContract` uses the formal's descriptor endpoint. Required Value equations include the actual binding/address, installed bound, installed object readout, and descriptor/value/root identities at that Name; the owner must establish them from the actual retained Shared packet, not assume them. `foldedNameKernel` has no supplied concrete Computation formal interpretation. An arbitrary original Kernel passed to `localKernel` is not automatically `foldedNameKernel`. Computation Name, annotations, complete Call/effect/receiver/provider/future fields and the formal-to-Name-to-App endpoint action stay open.

Parent §5 application: checked R90 inversion can expose the actual complete App demand without splitting its witness; candidate R91 would expose the earlier selected contract and the Name's exact local atoms. There is no lawful middle equality to compose. First remaining premise is the source-owned logical occurrence/admission/readout constructor above; then both-mode Name/installed-object and App readout, authentic complete Gen-Call-0/native correspondence, and original scoped joint equality lift/allocation. These remain the source/proof owners' obligations under primary coordination. `SourceProblem.InferenceSoundness`/`SourceScopedCoverage`/`PrincipalCoverage` are proposition definitions, and no LocalLaws concrete instance is established. Original A/B, principality, termination and production remain OPEN.

## Preserved execution failures and historical checked seam

R91 outcome `tasks/agent-loop/history/effect-permission-formal-registration-supplier-20261101-r91-outcome.md` (`19e5c3588e5321b66200dd4c872a20849c04777d02a3789177ae368d9e068f83`) and final review (`abd3134f8db87e8810f59dccc3eb4e807dac0a37ad11c1fe59002691addaf4d3`) record two exhausted calls:

- Call 1: input 934,982 bytes / `d0b42e35ea434d79f41d56a7788c30a9cd3d71bbd5cecc0111b32903b10044c4`, exit 1 in 14.786s. Exact sole stdout: `<stdin>:2375:0: error: invalid 'import' command, it must be used in the beginning of the file` (94 bytes / `1a798c59f7297904df59d1b1e97f3e26af936fcf8dc996dc0a477b06a6e51d78`). Three `import Init` lines had survived; no theorem was reached.
- Call 2: input 934,946 bytes / `54333b38794858ce2dccd2c8a44f1aa1a1c4ee8832964e3307c791c223a8ae44`, exit 1 in 17.345s; stdout 27,103 bytes / `039568ae627cfb2c2a7ea93cd861ff3a2614a0b0e0ae87fd4f688f4308b683f0`. `Contracts.lean:21` had introduced `YulangClosure.Step` before `NativeDictionaryDenotation.lean:29`; `WordArena Step` resolved to that inductive constant instead of auto-implicit `Step : Type`. Dependencies reached the 100-error cap before R91 audits. Recovery `sorry` warnings establish no acceptance and do not demonstrate source holes. Complete call-2 stdout bytes are not present in the pinned review/outcome; only this authenticated recorded digest/classification is available here, so no reconstructed log is substituted.

Both historical stderr streams were empty / `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`. Historical executable: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`, SHA-256 `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`; `-j1 -M1024 --stdin`, LEAN_NUM_THREADS=1, 120s timeout. R91 did not separately invoke --version. These are prior primary receipts, not executions by this leaf.

The checked R90 seam is independently reviewed in `tasks/agent-loop/inbox/effect-permission-registration-app-r90-review.md` (`c42f034d7976645bcb7e935d4be46ed3f21ddae34645bb95672e5b9b58a5a7f6`). Call 2: exit 0, 15.340572s, 137,750-byte stdin / `3ab0d68ec6ceaec30b391d9ee5aa58306b338692ebc660f9960b898e96370eba`; stdout 12,150 bytes / `c46535a3b1822a02893fea0d22df2707b7ab90ee4dea3f1304a65024df0c03a2`. It includes all six types/full axiom lists and independent PASS. FQN prefix `YulangClosure.SourceRegistrationAppBridgeR90.`: `app_rule`, `app_core_iff`, `app_derivation_iff` depend on `[propext, Classical.choice, Quot.sound]`; `app_witness_scope_fields`, `reference_insertion_whole_action` on `[propext]`; `installed_call_app_atom` on `[propext, Quot.sound]`. This confirms the bounded App/static-incidence seam only, not standalone imports, the R91 candidate or parent closure.

## Deterministic source-closure assembly proposal

The original import graph has **22** source modules; all are in the 105-entry manifest. Deterministic assembly below is a **proposal for exact-input independent review**, with zero execution. It preserves all non-import bytes and declared namespaces and repairs both observed name-binding contexts:

1. `NativeDictionaryDenotation` must be before `Contracts`: Dictionary imports only Init and relies on auto-implicit Step; Contracts declares the conflicting parent Step.
2. `SourceSignatureConstruction` must be before `OriginalSourceGeneration`: each imports only Syntax, and Generation's private `OriginalSource.node` becomes spuriously visible through `open OriginalSource` in a single input. Signature's auto-implicit node arguments must be elaborated before that alias exists. R90 independently checked this ordering.
3. Every internal source import is satisfied before its consumer. All existing namespace/end, variable/open commands and audit commands retain their original body positions. Hoist external imports to the header: the observed external set is `{Init,Std}`; use `import Std` once (Init is implicit and Std's prerequisite), remove **all** original import lines, and never leave an import after a declaration. No prelude/module/public-import line was observed in this closure.

Exact order, original source pins and proposed body start lines follow. All paths are under `notes/theory/lean/YulangClosure/`; each original file ends in LF. The closure table plus the manifest freezes every direct/transitive source dependency.

| Order / file | Original bytes | SHA-256 | Proposed body line |
| --- | ---: | --- | ---: |
| 1. NativeDictionaryDenotation.lean | 33584 | `d44a78f08970a09ca4c3e99a1d8dea846286a299d1a2bc91ec3b5e0eabea9070` | 2 |
| 2. NativeClosureEnvironment.lean | 12152 | `39aa5cefa078dd423e54f0d9790f9a48e136326742e01f65149f317c907be957` | 730 |
| 3. Contracts.lean | 7467 | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` | 1034 |
| 4. OriginalSourceSyntax.lean | 22040 | `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1` | 1191 |
| 5. SourceSignatureConstruction.lean | 37437 | `ed07890e29b4dcb38cabd18ec0e196efde9e95c64902942a9906a470b38c3311` | 1635 |
| 6. OriginalSourceGeneration.lean | 66485 | `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef` | 2367 |
| 7. SourceIdentityWorld.lean | 25976 | `6019fd9d57cde50183e016bd0c72de2c6eee72009065d85119fb0348dbcf0168` | 3564 |
| 8. SourceFunctionMembership.lean | 7744 | `8d370ee57e486ae48607d1bab493ae5135f28bf8a5a7ff1b0ef240fc0247e424` | 4098 |
| 9. OriginalSourceInterpretation.lean | 56341 | `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef` | 4242 |
| 10. OriginalRecursivePair.lean | 78256 | `1069c185c6fa190c2a0dd776ebf4efc7bfab8ece7e36f2f4049d480e50fa65e7` | 5332 |
| 11. OriginalSourceEnvironment.lean | 81021 | `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132` | 6747 |
| 12. OriginalWorldReadout.lean | 31012 | `edb82b9ecc62be486e057ee50152e30dad709f9a90196f78cab803838f08fb00` | 8207 |
| 13. OriginalSourceEvents.lean | 66574 | `cfd5f502a1e68a97e27e11a75400fae8789f167c92596aedb08ef7dfbb724342` | 8757 |
| 14. OriginalSourceChecking.lean | 103542 | `a0ba215e28fe0152e3c66024da86ab9a63219b7950e741bf260cbc4c2897ffd6` | 9996 |
| 15. OriginalCheckingAdmission.lean | 52370 | `77a8dd74f5913814d3628f0aed189be24b4aafc4780839eaa57237676a157da7` | 11601 |
| 16. OriginalParameterWorld.lean | 33616 | `7b5f849f744dbe56f374d8be6b11a5a218176abf6eeda2fb9da8180c7b1ff802` | 12454 |
| 17. OriginalParameterSemantics.lean | 45481 | `733c5b05e0db226f95d14ff2161c46e9a389b43d86b365b000a9656ec4fd0bd2` | 13047 |
| 18. OriginalFormalShared.lean | 58542 | `abb9d69546e284fcb5fe6be9bb3c18269227e91da94e09eebf1a62e0b56e67f7` | 13791 |
| 19. OriginalRetainedParameter.lean | 55668 | `ae8915cf002019541d0658895f0604e98700ac23f47aac479fc8382cf65ef799` | 14669 |
| 20. OriginalFormalAdmission.lean | 34188 | `77230ab7984ee544db16fe4d9663b73f98b9afa9c5d2610fad59c26753d5ac7c` | 15520 |
| 21. SourceRegistrationAppBridgeR90.lean | 11964 | `cd836e6b12a4deff0e5acf83523faedfb883240b6d019f17ec5a7d294b8c205a` | 16043 |
| 22. OriginalFormalRegistrationSupplierR91.lean | 14816 | `d5187d6dce15a3c6a8979c5e6e88a097fcd7815a53fc81ed4770fd137750de2b` | 16258 |

Exact byte algorithm (no filesystem output):

```python
parts = []
for name in ORDER_ABOVE:
    data = read_exact_pinned_bytes(name)
    parts.append(b''.join(line for line in data.splitlines(keepends=True)
                          if not line.startswith(b'import ')))
stdin = b'import Std\n' + b'\n'.join(parts)
```

Proposed stdin: **934,946 bytes**, SHA-256 **`7544b797610a40a973ddbcf3fc613b7ce3e3a2cfc9124d6d24abb47059b53957`**. It has exactly one import, on line 1. No source declarations, theorem types, payloads, assumptions or proof terms are renamed/rewritten/removed. Bodies preserve trailing LF; joins add exactly one LF.

**Module-context limitation:** a topological concatenation does not literally recreate separate imported module environments or private-name visibility. Hoisting Std also exposes its declarations to original Init-only bodies. The two known collision constraints are repaired statically; this is not a general proof of elaboration-context equivalence and not a claim that every extra ambient identifier has been certified harmless. A section wrapper alone would not hide already declared parent constants. No claim that this input is a completed standalone-module verification is made. The fresh reviewer must independently inspect the exact order, bytes and ambient/private-name uses; if preservation cannot be justified within this method, return the precise blocker to Luna instead of silently alpha-renaming source or adding explicit variables. A genuine fresh-per-module check would need the normal owned import artifacts/build environment, which this packet forbids. No such expanded route is requested or executed here.

If the primary admits this exact candidate after independent review and a pushed authorization, its existing five R91 type/axiom pairs must all print. Audit the actual types against the appendix, including the unrestricted base in the replacement theorem, original Satisfies premise and the one App witness. A nonzero exit, any dependency error, recovery sorryAx, missing report, module-context collision, wrong type or project axiom is a failed check; stop as the R92 contract requires. Even a clean run establishes only kernel acceptance of these conditional/discriminator statements in the declared assembled context, with actual printed standard axiom lists; it cannot supply the missing source law. No theorem's axiom set is predicted here.

Pinned configuration reread: `leanprover/lean4:v4.35.0`; `YulangClosure` library; `-j1 -M1024`; lake-manifest packages `[]`. Pin hashes: lean-toolchain `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`; lakefile `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4`; lake-manifest `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`. Actual current executable/version check: NOT_RUN by this leaf. Historical R90 version receipt identifies Lean 4.35.0 commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; current executable identity must be observed by the primary. Proposed primary command remains that historical absolute executable with `-j1 -M1024 --stdin`, cwd `notes/theory/lean`, LEAN_NUM_THREADS=1 and hard timeout <=120s, complete stdout/stderr in memory. No call is authorized by this handoff. At most two R92 primary calls, each exact input independently reviewed and separately authorized/pushed; another context collision or mathematical defect stops execution.

The skill checker is unavailable **under this packet's lease**, because it builds/writes cache and an audit scratch file. It was not invoked; no alternative checker result is fabricated. This narrower direct-input plan does not replace independent source review or grant production authority.

## Checks, coverage, next action and write stop

Actual leaf commands: bounded `cat`/`sed`/`rg` reads of assigned authority, sources, exact definitions and frozen receipts; read-only Python SHA-256/byte validation, recursive import census, in-memory assembly and a nested-comment/string-stripped lexical scan of the 22-module closure. All returned exit 0. The lexical scan found no code tokens `sorry`, `admit`, project `axiom`, `unsafe`, `native_decide`, `trustCompiler`, `implemented_by`, or `debug.skipKernelTC`; occurrences in comments, admitted identifiers and `#print axioms` are not holes. This source scan is not a transitive kernel axiom audit. No new proof term is delivered.

Represented by the candidate's statements: both modes; arbitrary original annotations/contexts/Prior payloads; all admitted invocations and Value Returns; exact original Shared anchor and retained scope metadata; arbitrary pattern/body/argument subtrees; complete Binding; original annotation boundaries and all App Call/checking premises under one witness. No record field/default/optional case, selection, handler, effect alternative or other source constructor is removed from the parent domain. Omitted proofs: authentic complete contract/source admission, source-owned logical write/read law, both-mode concrete Name interpretation, full Call/native correspondence, effect hygiene, publication/allocation, equality lift, A/B, principality/termination and production. No smaller source fragment is relabeled as complete.

Next in-scope action for Luna: freeze this input proposal for the assigned fresh independent exact-input review; either admit one bounded primary call, or retain the exact context blocker. Separately use the source lane's occurrence/telescope/write trace to construct the missing lawful EventProof/App ViewLogic admission/readout at its owner. A valid result must compute actual permitted writes/dependencies, retain original frame/event keys and all fixed/dependent fields, and derive—not assume—the readout equality. Do not repeat a permissive-model construction as source proof or add field-only native metadata before this supplier is grounded.

Mutual TODO `R92-LOGICAL-OCCURRENCE-READOUT-1`: parent §5; owner original logical introduction/admission/readout, coordinated by primary; required inputs actual source constructor, declaration and route, typed original telescope, selected whole contract, Shared delivery, actual event and incoming frame, resolved Binding and Name/App occurrence; proposed output constructor-derived protected write/read equation plus both-mode Name readout; falsifier protected-field overwrite, route collision, changed runtime operands or another resolved tuple. Downstream native owners remain `candidate_source` registration/initialization, `candidate_call` authentication and `InferenceSession::admit_candidate_fact` App construction; no compiler writes are authorized here.

Resources: one reasoning leaf, no descendants/heavy process. <=4 simultaneous lightweight read commands in a batch; no CPU/RSS measurement, runtime model/effort UNKNOWN. Fixed maximum 1,400s; zero primary-call slots consumed by this leaf. End clock/resource interval is recorded in the final handoff message. Exact changes: this handoff only. Scratch/temp/cache/generated/build/environment/worktree paths: **none**. Git/index/ref/network/user/third-party contact: **none**. Dependency edits: **none**. Review/integration pending; no self-certification. **Writes STOPPED when this revision is submitted; no unresolved descendant lease.**

## Appendix: exact source-declared theorem types, not checker output

The following text is extracted from the frozen candidate, without proof bodies. Names use the namespace and opens stated above; implicit `s : OriginalSourceInterpretation.Sorts` and `View : Type` remain as declared in the file. These statements, plus their exact dependencies, are the audit target; no emitted type or axiom report is invented.

```lean
theorem actual_build_shared_supplier (intro : Introduction s View)
    (assignment : FormalAssignment s View) (inputs : Inputs s)
    (readout : RuntimeReadout s View) (base : LocalAdmissions s View)
    (original : Kernel (Payload s View)) (prior : Prior s View)
    (annotation : Option Declaration)
    (solves : Satisfies (localKernel intro assignment inputs readout base original)
      (priorEnvironment intro prior)
      (Build intro.parameter.context (.lambda ⟨intro.parameter.lambdaSite, annotation⟩
        intro.parameter.formal intro.parameter.pattern intro.parameter.body))) :
    let environment := priorEnvironment intro prior
    let state := OriginalParameterSemantics.replayTelescope readout prior.root.decoded intro.telescope
    let kernel := localKernel intro assignment inputs readout base original
    ∃ description view packet,
      description.data = .logical .description (intro.description assignment state) ∧
      view.data = .logical .viewLogic (ViewPacket.encode (intro := intro) packet) ∧
      kernel.admitted environment (descriptionBinder intro.parameter) description ∧
      kernel.admitted (environment.extend (descriptionBinder intro.parameter) description)
        (viewBinder intro.parameter) view ∧
      ∀ invocation, kernel.admitted
        ((environment.extend (descriptionBinder intro.parameter) description).extend
          (viewBinder intro.parameter) view) (invocationBinder intro.parameter) invocation →
      ∃ receipt,
        kernel.admitted
          (((environment.extend (descriptionBinder intro.parameter) description).extend
            (viewBinder intro.parameter) view).extend (invocationBinder intro.parameter) invocation)
          (receiptBinder intro.parameter) receipt ∧
        EntrySupply kernel readout intro.parameter
          ((((environment.extend (descriptionBinder intro.parameter) description).extend
            (viewBinder intro.parameter) view).extend (invocationBinder intro.parameter) invocation).extend
            (receiptBinder intro.parameter) receipt)
          (intro.selection assignment).contract
```

```lean
theorem resolved_formal_name_rule (mark : Mark) (context : Context) (name : Name)
    (binding : Binding) (resolved : lookupBinding context name = some binding)
    (formal : binding.kind = .formal) :
    sourceRules context (.name mark name) =
      match mark.annotation with
      | none => nameCore mark.site context name binding
      | some target => .rule .annotation mark.site context
          (SourceRegistrationAppBridgeR90.annotationPremises mark.site context target)
          (.one (nameCore mark.site context name binding))
```

```lean
theorem resolved_formal_name_iff {Value : Type} (kernel : Kernel Value)
    (environment : Environment Value) (mark : Mark) (context : Context) (name : Name)
    (binding : Binding) (resolved : lookupBinding context name = some binding)
    (formal : binding.kind = .formal) :
    SourceJudgment kernel environment context (.name mark name) ↔
      (match mark.annotation with
       | none => True
       | some target => ∀ premise ∈ SourceRegistrationAppBridgeR90.annotationPremises
           mark.site context target, Local kernel environment premise) ∧
      ∀ premise ∈ namePremises mark.site context name binding,
        Local kernel environment premise
```

```lean
theorem app_formal_name_seam {Value : Type} (kernel : Kernel Value)
    (environment : Environment Value) (appMark nameMark : Mark) (context : Context)
    (name : Name) (binding : Binding) (argument : Source .expression)
    (resolved : lookupBinding context name = some binding) (formal : binding.kind = .formal)
    (derivation : SourceJudgment kernel environment context
      (.app appMark (.name nameMark name) argument)) :
    (match appMark.annotation with
     | none => True
     | some target => ∀ premise ∈ SourceRegistrationAppBridgeR90.annotationPremises
         appMark.site context target, Local kernel environment premise) ∧
    ∃ witness : ScopedValue Value,
      kernel.admitted environment ⟨appMark.site, .viewLogic, 0⟩ witness ∧
      (∀ premise ∈ SourceRegistrationAppBridgeR90.appPremises appMark.site context
          (.name nameMark name) argument,
        Local kernel (environment.extend ⟨appMark.site, .viewLogic, 0⟩ witness) premise) ∧
      (match nameMark.annotation with
       | none => True
       | some target => ∀ premise ∈ SourceRegistrationAppBridgeR90.annotationPremises
           nameMark.site context target,
           Local kernel (environment.extend ⟨appMark.site, .viewLogic, 0⟩ witness) premise) ∧
      (∀ premise ∈ namePremises nameMark.site context name binding,
        Local kernel (environment.extend ⟨appMark.site, .viewLogic, 0⟩ witness) premise) ∧
      SourceJudgment kernel (environment.extend ⟨appMark.site, .viewLogic, 0⟩ witness)
        context argument
```

```lean
theorem event_proof_replacement_admitted (intro : Introduction s View)
    (assignment : FormalAssignment s View) (inputs : Inputs s)
    (readout : RuntimeReadout s View) (base : LocalAdmissions s View)
    (environment : Environment (Payload s View)) (state : Decoded s View)
    (decoded : decode readout environment = some state) (occurrence : Nat)
    (replacement : Contract s intro.parameter.formal.entry) :
    let binder : Binder := ⟨intro.parameter.body.site, .eventProof, 0⟩
    let data := declaration state intro.parameter replacement
    let candidate := scopeCandidate environment occurrence (.logical .eventProof data)
    let admissions := localAdmissions intro assignment
      {base with logical := fun _ _ _ _ => True}
    Admitted inputs readout admissions environment binder candidate ∧
      ∃ after, decode readout (environment.extend binder candidate) = some after ∧
        formalContract after intro.parameter = replacement
```
