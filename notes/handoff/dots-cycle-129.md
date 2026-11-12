# Cycle129: dictionary order and exact nominal slot transport

**一般sourceのB4Bridges V3: 未充填12 / 全12。一般B4は未完成。**

開始2026-11-12T00:25:23Z。検証・公開・報告・writer解放を含む期限は01:20:23Z。
最新ユーザーの55分総上限を優先し、確定終了時刻・所要時間はcompleted heartbeatに記録する。
新規18 modules、公開125定理。
25分時点でも全結合の具体回帰、freshness境界の縮小、最終検証が残っていた。

## 閉じた部分目標

1. **実computed Framesの順序不変（約00:27–00:33）。** checked registryの可視宣言/where順を変えても、固定Contextのbindingsと全Framesが一致する。呼出側からFramesを渡さないraw再構成/準備のOption全体も一致し、失敗の場合を含む。full宣言が等しいと仮定せず、異なるwhere列を許す。
2. **typed finite coverageと厳密な位置探索（約00:28–00:33）。** lower/upper/outputの全出現を保持した有限列の実type-slot coverageと成功を同値にした。ID欠落とnoneも同値。reservedだけのLinked、row-only IDでは失敗し、実type slot追加後は重複した全6出現が残る。
3. **構文からfull nominal model同値（約00:29–00:39）。** 型/rowを別に保つslot埋込み、全ordinary/head/interval/nominal descriptorの正確な構文像から、全global nominal assignmentのModels同値を証明。target snapshotは入力のまま。1→2と2→3の実fixtureを構成し、後者はtype77/row43の両parameterを持つ非空descriptorと具体modelを保持した。
4. **全有限dictionary準備と同一証拠の移送（約00:36–00:45）。** source lookup、変数head/RHS、plan、再帰recipe、raw payload準備を一つの成功保存へ合成した。局所値は正確なrename、source dictionaryは木全体で同じ。全item batchも重複を残したmapに等しく、記録後のfull Modelsが同値。一つの同じreadback witnessが全target transaction modelで元/新Modelsと独立source Evidenceを持つ。
5. **独立nominal source意味の順序不変（約00:38–00:40）。** 任意full nominal assignment、同じbinder値のままInstance/Evidenceをregistry順変更へ移した。固定ContextではFramesの等しさも内部で証明される。
6. **結合前提の実同時成立（約00:43–00:51）。** checkedな実終端宣言、実raw payload、二重のexplicit output、非空nominal descriptor、2→3増加を持つfixtureで、前後実準備成功・同じ辞書・同じfull nominal joint model・source Evidenceを同時に示した。candidate Survivorはこのfixtureで主張しない。

7. **Freshの追加前提を局所化（約00:51–00:56）。** 新type/row sourceが旧mixed source所属または旧seed以下というCoordinatesBoundのもとで、generated membership・allocation source・Freshを保存した。mixed fixtureでもreserved88とseed以下row44により実成立する。新IDの型付き起源を与えるものではない。
8. **normalized viewの非自明な境界（約00:55–01:00）。** 実full nominal modelを持つ前後stateでidentity Transportが成立する一方、viewのみの変更でKnown/RootPendingが変わる反例を証明。モデル同値からreadiness同値を結論しない根拠を具体化した。
9. **新slotを本当に使用する実準備（約00:57–01:02）。** reserved ID88が旧type slotにないため実raw準備はnone、新slot2追加後には実辞書・二重output・full nominal joint model・source Evidenceが得られる。同時にRootPendingも証明して候補受理と区別した。

最初の小目標で停止せず、evidenceNodeへ必要な準備/全model/同一木の橋を続けた。
終了理由はI-15(a): 最新指示の55分総上限を守り、最終検証と公開・報告を含めて約50分で閉じるため。

## 復元・範囲・残る前提

- integrationを`a97bf63ffc3b2f207a978dc5a6721b90ec8158c7`へ取り直し、standing orders/inboxを全文確認。ACTIVE、cycle128 completed/released、前writerと重複なし。upstreamの追加Astra成果を取り込み、公開済みcycle128終盤追記も保持した。crash復旧や未公開source喪失はない。
- 既存Lean実装を変更せず、新moduleとYulang/Audit/READMEの追記のみ。spec/plan/lake、Astra項目1/2/3、一般Step/I-20需要併合（終盤I-21でAstra担当）には触れていない。全体build/Audit/AxiomGateはlocalでは実行しない。
- Transportはtarget snapshotを構成せず、追加source IDの型付き起源/権限、sourceからの生成を保証しない。元のnormalized viewを新stateが保つことも仮定/結論に入れていない。モデル同値をcandidate/readiness同値として扱わない。
- source成功移送は同じglobal Framesに限る。異なるContext間のcomputedFrames同値、異なるdriver順の最終state同値は未達。元のfailureは新slotで成功へ変わりうる。
- 変数head/RHSの現在のcompiler制限、captured endpointの同じID条件、root output/readiness/freshness/coverage guardを弱めていない。nominal/compound/default RHSの一般compilerや実candidate森林の生成は未完成。

## SourceBoundary 全13項目

| Field | 状態 | 今回の位置と残り |
| --- | --- | --- |
| Checked | 一般certificate定義あり | Astra所有。complete checker境界維持。 |
| Models | 一般full nominal state定義あり | 構文Transportと全dictionary batchで任意full assignmentの同値。一般source更新ではない。 |
| Step | MISSING | 開始時は担当未割当。終盤I-21でAstra担当へ。今回未着手。 |
| Stable | MISSING | EOFと兄弟fixpoint。 |
| Generated | 一般emission/Plan部品あり | 実source/driver生成は未接続。 |
| RootPending | 一般partial定義あり | Astra既存定義。view間のRootPendingが異なる実反例を追加。 |
| RootK2 | 一般partial定義あり | Astraのcoverage境界を維持。mixed recurrence回答を読んだが担当外。 |
| CandidateK2 | 一般carrier上partial定義あり | 全inspection/materialization範囲は未充足。 |
| InspectionPending | 一般carrier上保守的定義あり | unsupported coverageを残す。 |
| Survivor | 一般carrier上partial定義あり | guard維持。今回のslot移送はSurvivorの保存を主張しない。 |
| Evidence | 一般carrier上supported-variable定義あり | 実raw準備・同一source木・全nominal model・slot移送を結合。完全field代入は未達。 |
| Reorders | 一般構造定義あり | 固定Contextのcomputed Frames/Option/独立source意味を不変にした。driver順は未達。 |
| DictionaryEquivalent | 一般source/payload構造定義あり | 同じsource辞書木を保持。一般boundaryの観察意味の全接続は未完成。 |

## 検証・公開

正確な全定理型と日本語の範囲は[dots-cycle-129-theorems.md](dots-cycle-129-theorems.md)。
コマンド、出力全文、exit code、public tree照合は[dots-cycle-129-verification.md](dots-cycle-129-verification.md)。

最初のsource `3422acd820109ff6f676e72d611d197581ace327` は6module/51定理。
全2503 tracked paths/modes/types/blob SHAを照合、差分0、truncated=false。
Hosted core/proofともsuccess、full1453jobs/9244audit entries、51/51追加名と許可外公理0。

第二source `0031756d286a732970df0ba0cca8f4002f490c09` は13module/94定理。
全2510 tracked paths/modes/types/blob SHAが一致。focused602jobsと修正後のscoped auditは成功。
検証helperの初回は未対応表示optionでexit1となり、optionを除去して再実行した。
その初回を成功には数えない。全体検証とlocal focusedの結果は区別する。
第二source hosted core/proofもsuccess、full1460jobs/9287audit entries、94/94追加名、許可外公理0。

最終source `3bba9c845697a0a8a41d03ff62f880a8b8a7aef3` は18 modules/125定理。
focused609jobs、scoped125/125axiomsと全型取得、append-only gateはexit0。
全2515 tracked paths/modes/types/blob SHAを照合し、差分0、truncated=false。
追加3報告を含む最終報告treeの予定総数は2518。実照合済み値とreport commit/treeはcompleted heartbeatに残す。
最新integrationからの差分は、cycle128公開済み追記の復元を含み、Lean18新moduleと3追記ファイル、design・報告・heartbeatからなる。
最終hosted core/proofともsuccess。full1465jobs/9318audit entries、125/125新定理、許可外公理0。実new ID88 runtimeはfalse → some(301,1,2)。全stdout/exitとrunリンクはverification報告へ記載。

## Yulang2照合と次の接続

work/dots-auditを取得し、ROLE-MORE-001–008と文書の境界を読み直した。旧advertised-whereの挙動を新specへ輸入しない。正本はspec06§6.3のwhere連言、兄弟安定後解決、source identityと関連等式である。今回新Yulang2実機試験はしていない。新言語意味論の決定をしておらず、質問ノートは0件。

次の候補:
1. 担当source-state側で、必要なtyped IDからtarget snapshotとTransportを実生成し、正規化viewと所有権を保存する。
2. 辞書担当の次の局所目標は`reconstruct_frame_local` → `prepare_frame_local` → `prepare_transport_frame_local`。同一source木で訪問したnodeのcaptureと完全child occurrence列の一致を用い、global Frames等式を必要箇所の一致に弱める。Frameにはallocation/identityもあるためcapture一致だけでは不十分。型付き前提と未証明の3段階をdesignへ記録した。実candidate Contextからその一致を導く仕事とは区別する。
3. nominal/compound/default RHSと非singleton captureについて、独立source意味を先に定義し、既存guardを維持してcompiler範囲を拡大する。

開始・終盤とも空き37GiB。既存cacheのコピー/削除なし。使用量上限は不明。

## 終盤の新upstream・I-21（次サイクルの最優先）

01:12 UTCの再fetchでintegration `a5e2eecf619b7237fb545faea6fa7e5a52cb0ce9`を確認。I-21はAstraへ項目4（Step/Stable/Generated/I-20）、dotへ新`GeneralNominalRecursiveCandidates.Survivor`に対する`Evidence`とV3 `evidenceNode`を割り当てた。前節の暫定的な次候補より、この新指示を優先する。

新`recursiveFields`は一般nominal carrier上の9項目を持ち、RemainingはStep/Stable/Generated/Evidenceの4つ。新しい言語全体の網羅性はなお部分的。今回のSourceBoundary表と検証済みsourceは開始時a97bf63のsnapshotについての記録であり、終盤の新14modulesを無検証で混ぜてはいない。一般B4は12/12未充填のまま。

新Survivorは実BranchModelsの存在を含む一方、evidenceNodeは元stateの全Modelsについて要求する。次の最初の監査はこの量化の接続とprojection/反復capture/output義務。存在するbranch modelを任意modelの代用にせず、独立したsource Evidenceを定義してから具体境界のnode結合を証明する。詳細をdesign末尾に残した。今回新sourceは変更せず、次サイクル開始時に新integrationを統合する。
