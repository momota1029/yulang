# Cycle190: source変数head・実installation・V6辞書健全性

roles、registry、root、state、plan、model、有限list、名前は、明記した前提の下で全称量化する。存在結論だけを存在量化する。全公開定理名と完全な量化型はCycle190のTypes監査に記録する。以下は健全性またはその補助で、完全性・主型性・一般B4完成の主張ではない。

## sourceからfinite linear leafへ

SourceLinearShape190のnormalize_variables/variables_variables/source_shapeは有限変数headの正規化、名前列、実検査queryを一致させる。initial_entriesは実Initial+Frame+head=names.map varから、entriesと名前・point bounds・query・inputNamesの4等式を存在構成する。Nodupはこの構造補題自体には不要。

SourceOutputReady190.source_effects_readyは任意Initial、plan、rootの要求出力に対応するassociated equation coverageと、各associated RHSの正規化翻訳Completeから実EffectsReadyを導く。出力要求は非空でもよい。

SourceLinearEvidence190.selected_installable/selected_source_candidate/stable_selected_evidenceは任意Checked registry、実Initial、実V6 selectedと、選択keyの可視宣言が有限distinct-variable head・requirements=[]・上記coverage/Completeであることから、実candidate/Frame/Installableを構成する。Stableを加えるとchildren=[]かつ任意current Modelsの同じmodelに既存Evidence(root,node key [])が成立。callerにquery/bounds/Frame/EffectsReadyを要求しない。

## 任意生成需要のinstallation条件付き橋

InstallableEvidence190.request_readyは実InstallableからRootDefinedとmaterialization完了を導く。generated_committedは任意state、Stable root、実Generated root focus、focusのInstallableから意味的Committedを導く。committed_instanceは同じcurrent modelを保ち、実packet childrenを持つ既存Instanceを構成する。generated_evidenceは同じmodel/contextの子Evidence列から親Evidence。Initial・leaf・head形状制約はないが、Installableという本物の運用前提を保持する。

InstallationSound190.Availableは、生成済みかつ実Local.selectedの需要ごとに、実Frame/children一致/Installableを持つplan/supportがあるという運用条件。Evidenceを仮定する条件ではない。
- generated_children: Stable+Generated+Frame+Installableから、実Committedがjournalに記録する全子edgeを使いGeneratedを導く。
- dictionary_evidence/dictionaries_evidence: Stable rootとAvailable、任意current Models、実V6 Classify.selectedから、同じmodelの既存Evidenceへ相互再帰で接続する。
- dictionary_sound: 任意executorについて、全checked初期入力の最終stateがStableかつAvailableなら、実V6 DictionarySound。

一般Availableは現WF境界では単なる未証明でなく偽。InstallationBoundary190.known_source_not_available/not_universal_availableは既存監督WFJoinCounterexampleを正確なAvailable条件へ接続する。既存のmulti-tag materialization阻害を新発見扱いしない。境界/意味論を変更して回避していない。

## 反復captureの修復

RepeatedPointRepair190はInitial+Frameと有限variable queries/point bounds/inputNames対応を前提に、繰返し名を許す。source_equivalent/repeated_sources_equivalentは実HeadEquationsのactual head schemaからraw point sourceと共有binderの意味的同値を導く。cross_compatibleは全cross制約を導く。

repairはfresh purpose0/1 merge endpointsだけを元binder値へ上書きする有限assignment。repair_current_source/repair_models/repair_binderは現在source・実current Models・全binderの保持、repair_mergesは実lower/upper merge方程式の成立を示す。repair_actual_schema/repair_head_schema/repair_named_schema/repair_outputsはactual originとbinderを保持し、同じschema/output条件を回復する。repair_head_equations/repair_head_modelsは新assignmentのcentered headとraw private headの両方を導く。Nodup・既成merge方程式を仮定しない。

LeafWitnessInstall190.installable_of_named_witnessはInitial+selected+Frame+leaf+readyと、一つのmodelでcurrent/fullPlan/outputを満たす存在証人から実Installable。別々の存在証人を同一視しない。

RepeatedNamedPlan190.named_planは任意finite variable head/point bounds/leafについて、同一modelのprivate HeadModels+HeadEquations+named schemaからfull Plan.Holds。selected_named_planは実selectedのhead/output存在証人をrepairし、current/fullPlan/outputを同時に成立させる。selected_named_installableはそれを実Installableに接続。

SourceRepeatedEvidence190の外側はsource宣言head=任意有限names.map var、leaf、coverage、Completeだけを受け取る。**名前の繰返しを許す**。selected_source_candidateはFrame/Installableを導出、committed_or_inhabited_stepはCommittedまたは実Stepかつ後続Modelsの存在を導出。Stableを追加したstable_selected_evidenceは、任意current modelの実Evidenceを結論する。

存在証人は修復するが、最終の全称modelをその証人で置き換えてはいない。初期の反復captureが新しいmerge方程式を要するとき、Initial+Stableが成立するとは主張しない。進展の中心は実Installable/Stepまでの構成であり、Stable corollaryの非空性を全反復headに主張しない。

## 非空性と境界の回帰

TwoHeadFixture190/TwoHeadNonvacuity190はhead[var0,var1]、arity2、同じscalar source1を二入力に使い、名前付きoutput0=var0を要求する実例。Checked+Initial+Stable+selected+Models+arity2+outputs非空+Evidenceを同時に証明。40public回帰補助は一般橋の閉鎖数に数えない。

AvailableNonvacuity190.available/classified/recursive_evidenceはこの実例でAvailableと実V6 Classifyを構成し、新しい相互再帰soundness定理からEvidenceを再生する。条件付き橋に正の適用例と既知の負の適用例の両方がある。

## 13項目の定義台帳

| 項目 | 状態 | 実装先・制限 |
|---|---|---|
| Checked | 一般の定義あり | GeneralDeclarations.Checked |
| Models | 一般の定義あり | HeadStepEffects.Models、live ledger込み |
| RootPending | 一般の定義あり | HeadStepBoundary.fields |
| RootK2 | 一般の定義あり | 実中心/循環guard |
| CandidateK2 | 一般の定義あり | 同fields |
| InspectionPending | 一般の定義あり | partial translation限界を保持 |
| Survivor | 一般の定義あり | HeadCandidates、head-only |
| Reorders | 一般の定義あり | RegistryReordering |
| DictionaryEquivalent | 一般の定義あり | 既存payload比較 |
| Step | 一般の定義あり | HeadStepKernel.Step、今回variable leafの実enabled |
| Stable | 一般の定義あり | HeadStepKernel.Stable、変更なし |
| Generated | 一般の定義あり | 実journalの生成関係 |
| Evidence | 一般の定義あり、橋は条件付き/断片 | 既存RecursiveEvidence、今回実Installableとsource variable leaf |

V6にSkeleton構造がないため架空の分母は出さない。一般EvidenceNode・一般child materialization・最終Statementは未完。新たに閉じた一般target fieldは0。

## 13:56 UTC checkpoint: actual repeated installation and upstream audit repair

Added GeneralNominalRepeatedFixture190 and GeneralNominalRepeatedLocal190: a concrete checked initial source with head [var 0, var 0], two source inputs, and named output var 0. It is selected and Installable. A current model assigning bool to the fresh lower endpoint refutes semantic Committed while preserving the source assignment. Hence there is an actual installation Step with an inhabited successor, and the initial state is not Stable. This is a progress/nonvacuity regression, not a claim that repeated-head initial saturation is already stable. All 50 public regression theorems passed strict checking and standard-axiom audit.

Fresh integration d5696a2ea39565b1475f6d0ceded1fb75b09b726 was merged. Upstream commit 00b8f9ffd removes the offending pp.universes setting in the three historical Cycle189 audit files; earlier notes describing that parser defect are historical and superseded by this upstream repair. No local rewrite of those published proofs was performed.

Current full cycle190 gate: 243 declarations including generated/private, standard axioms only. Fifteen proof modules; public declaration inventory and reachability are being frozen separately. No general field was closed; Available is a genuine extra premise and is refuted universally by the known upstream counterexample. Independent full review was unavailable; author-level checks and concrete positive/negative regressions do not substitute for it.

## 完全な公開inventory（13:59 UTC、監査時点）

15 proof modules に公開 theorem 144、本体定義4、abbrev23、計171。従来の checkpoint の56/94等はその監査で列挙した宣言数であり、全公開定義数ではない。Cycle190AllPublicTypes が相互再帰内の2定理も含む171宣言の完全型と公理を列挙する。kernel gate は生成・private を含む243。これらは一般field完了数ではない。

RepeatedFixture190/RepeatedLocal190 の50定理は、固定例のChecked・Initial・selected・Installable・意味的非Committed・実Stepとその後状態のinhabited・初期非Stableの構成と補助である。2入力distinct名の40定理は別の固定例であり、そのInitial/Stable/selected/Evidenceの同時成立を示す。AvailableNonvacuity190の3定理は前者とは別のdistinct例に対するAvailable/Classify/Evidenceを示す。これらは任意到達状態の一般化ではない。

一般3root(exact/saturationTotal/orderIndependent)のconstant type/value閉包からは新規243中0、局所7rootからは243中221が到達。opaque証明本体を含めた構文依存であり、意味的最小性や一般仕様への適合をこの数字だけでは主張しない。

著者再点検: repaired modelの存在はInstallableを得るためだけに使用する。stable_selected_evidenceは受け取った任意current Modelsの同じmodelでCommittedからInstanceを得る。DictionarySoundは任意executorに対し最終StableとAvailableを別々に要求し、Availableは既知反例で一般的には偽。実repeated例にはStableを付けず、むしろnot_stableを示す。独立した全体レビューは枠不足で未実施。

## Actual repeated successor Evidence (14:05 UTC proof freeze)

GeneralNominalRepeatedSuccessor190 adds10 public theorems and1 abbrev, all strict checked. For the fixed repeated source [var0,var0] with named output var0, there exists an actual WF Step successor with inhabited Models, and EVERY model satisfying that successor has actual boundary.Evidence at that successor for root/node3[]. No Stable premise, no assumption of Evidence, and no substitution of an existential model.

current_query/current_report/current_bindings/current_capture/current_schema identify the actual inspection/allocation/schema after rebasing the packet context to packet.privateContext. current_ordinary gives an iff of ordinary private constraints in any assignment. current_branch and current_instance transport old packet satisfaction to Instance in the installed current context in that same assignment. installed_evidence uses actual install_models and successor_evidence packages a genuine novel Step and inhabited successor. These are fixed-fixture results, not arbitrary reachable-state transport or a claim of Stable/Classify at the successor. General transport beyond this fixture remains open.

Final source inventory now16 modules,154 public theorem declarations and28 definitions/abbrevs,182 total public. Earlier15/171 counts are checkpoint inventories, not the final total. No general target field closed. Full new public signatures/axioms are in Cycle190CompletionTypes.lean and completion-types.log; earlier public171 remain in Cycle190AllPublicTypes.lean.

### Completion verification snapshot

All16 source modules strict checked (first15 strict-source.log, successor-strict.log for the final module). Completion gate254 PASS; final public182 checked across AllPublicTypes and CompletionTypes. General3 roots reach0/254; local8 roots including actual successor_evidence reach232/254 (175/182 public declarations). Focused successor build --wfail passed, only the final module rebuilt; job count1121 includes cached imports, not a full build. Diff-only verification PASS with4 read-only metaprogram REVIEW notices. Full output: completion-diff-only.log.

The earlier source-sha256.tsv checkpoint predates adding the two mutually recursive public signatures to Cycle190AllPublicTypes.lean; its hash for that audit file is superseded. completion-source-sha256.tsv records the actual final27 source/audit/tool files. No proof content changed by this inventory correction.

## Generic actual-install successor adapter (14:12 UTC)

GeneralNominalInstalledEvidence190 removes the fixed-fixture restriction from the one-install current-context bridge. For arbitrary roles/registry/state/plan/support and genuine WF Installable: stored_instance takes packet.Holds in a given assignment and yields the stored-context Instance; current_instance takes Models of the actual install result and yields Instance at that result's CURRENT context, preserving the given assignment. current_evidence combines it with actual All₂ child Evidence in the same successor context/model; terminal_evidence handles packet.children=[]. No Initial or Stable assumption, no restriction to variable heads or leaves in the first three theorems. Installable is still explicit and is not derived for arbitrary reachable selections. Merely having an install result is not a proof of Step: generated focus and semantic novelty remain separate conditions.

This adapter explicitly REUSES existing GeneralDictionaryOrdinaryTrace.packet_extension and instance_extension. The old transport principle is not claimed as newly proved. The earlier repeated successor proof remains a concrete regression connecting a source-derived actual novel Step, inhabited successor and universal successor Evidence. Arbitrary installation enablement, nonempty child Evidence construction, descriptor-changing refresh and full reachable-state dictionary soundness remain open.

Final inventory supersedes checkpoint counts:17 proof modules,158 public theorem declarations plus28 definitions/abbrevs=186 public. Exact additional four types and axioms are Cycle190InstalledTypes.lean / installed-types.log.

A read-only targeted reviewer checked InstallationSound190, InstallableEvidence190 and InstallationBoundary190 (not authored by that reviewer): actual Classify decomposition, generated child edges, same-model/context and child ordering, genuine Available premise and known-counterexample adaptation. No defects found. That reviewer authored other cycle190 modules, so this is NOT independent full-cycle review, which remains unavailable.
