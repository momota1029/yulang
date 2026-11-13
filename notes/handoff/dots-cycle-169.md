# dots cycle169 — 名前付き出力の構造的辞書coverageと通常継続

開始2026-11-13 16:28 UTC（定期run16:27:19 UTC）。ユーザーの55分上限を優先し、17:22:19 UTCまでに検証・公開・報告する。前168のcompleted心拍・公開報告・全worker終了を復元してから開始した。並行する前サイクルwriterはない。

## 復元・公開範囲

- `integration/m1-final` を取得し直し、常設指示、inbox I27まで、前168報告を再読。基点 `b95d31b190f25633851ec805553bb57c792ffad7`。Astraのground production追加を統合し、定義は変更していない。
- 16:50前後の再読でもintegrationは同じ、inbox SHA `df1d2623a16552048310f6bb6e8c7a21f676bf23`、ACTIVE。STOP・最大サイクル上限なし。
- GitHubアプリのブランチheadをlease付きで更新。gitのbranch名fetchはcycle167を指す遅れた参照を返したため、APIで確認した正確なcommit SHAを取得した。初回心拍の古いblob SHAは409で拒否され、現在SHAを読み直して成功。重複更新はしていない。
- 書き込みは `work/dots-main` のみ。`spec/`、`notes/plan/`、Astraの既存定義、lake設定、既存production/監査行を変更していない。Yulang.leanはimport追記のみ。

## 今回の成果

**12新module・53公開定理**。補助定理を完全性・主型性の完成として数えない。

1. source-ID/seed/計算report/schemaの構造的移送の合成を証明。通常制約だけが増える実際のShared継続で、同じMixedTreeを保持する。意味的Evidenceを初期前提にしない。
2. 同じ現在context/modelでselected key・順序つき子一覧を照合し、現在の子Evidenceから親を組み立てる。Shared Stableを用いる一般補題はInstallable・Generated・完全なPacketGuardを明示的に要求する。
3. child-closed domain上の局所構造Node coverageと選ばれた子関係のAccから、有限MixedTreeを構築。SourceFormedを加えると、一つのpayloadが全現在モデルで働く。後述8により、この局所coverageからAccは追加仮定なしに導けた。coverageをStableから導いたわけではない。実際のDisplay→Int例で旧MixedTreeを前提にせず適用した。
4. Shared actionがあれば同じfocusのValue actionが**何らかの**終点に存在することから、Value Stable⇒Shared Stableを証明。install終点が等しいとは主張しない。既存の初期named-output例が実際のShared関係でStableと示せた。これはterminal・零stepの例で、一般停止性や新しい非終端安定化ではない。
5. **旧MixedTreeの具体的なcoverageの穴を形式的に示し、拡張した。** 空journalかつoutputs非空なら旧MixedTreeはどのpayloadにも存在しない。一方、実際の初期例にはSourceFormed・Shared Stable・モデル・semantic Evidenceがある。これはV5の反例ではなく、旧証明書が狭すぎるという事実である。
6. 新LeafShapeはscalar入力と、実計算reportのbindingsから作る**実際のnamed materialization requests全部**の有限source観察を持つ。RootDefinedも要求するが、Models/BranchModels/Instance/Evidenceを含めない。これからBranchModels・Instance・Evidenceを導いた。三引数nominal named-output例で非空虚性を確認した。
7. 新NamedTreeは旧MixedTree、記録node、新named leafを再帰的に混ぜられ、同じ現在モデルで解釈できる。実例でNamedTreeあり・旧MixedTreeなしを証明し、通常Shared継続で新証明書自体を保存した。descriptor refreshの一般保存は含まない。

8. 固定された有限journalの親identityの最大値をMとし、実allocatorが子identityを真に増加させることから、rank=(M+1)-identityの減少を証明。任意の旧Mixed局所coverageだけからAccと有限MixedTreeを導く。SourceFormedを加えると全現在モデル共通のEvidence payloadを得る。domain有限性・Accを追加仮定せず、実行中のjournal増大や実行停止は扱わない。

既存のDisplay辞書やnamed-output辞書そのものを新しい言語範囲の成功として数えない。新しさは構造的十分条件、真のcoverage拡張、Shared関係での安定性確認と証明書の保存である。

## 13境界とV5

| 境界 | 状態 |
|---|---|
| Checked | 一般nominal定義あり、変更なし |
| Models | 一般定義あり。現在journalモデルと明示的な実例モデルを使用 |
| Step | 一般Shared定義あり、変更なし。通常継続は実関係の制限 |
| Stable | 一般Shared定義あり。旧関係の有効action不存在からの十分条件と初期実例のみ |
| Generated | 一般定義あり。guard付きStableでpacketの子生成を導く補助定理 |
| RootPending | 一般定義あり、変更なし |
| RootK2 | 一般定義あり、変更なし |
| CandidateK2 | 一般定義あり、変更なし |
| InspectionPending | 一般nominal定義あり、全Shared境界への統合は未完 |
| Survivor | 一般nominal定義あり、変更なし |
| Evidence | 一般定義あり。今回named-outputの構造的coverageとcurrent解釈を拡張 |
| Reorders | 一般nominal定義あり、変更なし |
| DictionaryEquivalent | 一般nominal定義あり、変更なし |

V5は引き続き**未証明8/14**。既存の数え方を維持し、新Shared境界の全フィールドを閉じたとはしない。全Shared evidenceNode、Stable/Reachableからの局所coverage・適切なguard/Installableの一般導出、完全性・主型性・全言語網羅性は未完。

I26のguardは弱めていない。semantic Evidenceの定義自体にはDecisionGuardが入らないため、ReadyAtがないことだけから一般にEvidence不存在とは結論しない。前167のcaptured consumerの保留を解消したとも主張しない。

## 検証

- focused `lake --rehash build --wfail`、最終対象 `Yulang.GeneralDictionary169CoverageAccessible Yulang.GeneralDictionary169NamedPersistence Yulang.GeneralDictionary169FiniteDisplay Yulang.GeneralDictionary169Selected`: **784 jobs、exit0**。job数はキャッシュ込み。
- 新しい小auditをすべて `lean -j1 --trust=0` で実行。5つの依存公理gateはprivate/generated定義を含めて **218宣言（32+87+77+11+11）** を検査し、exit0。許可公理はpropext/Classical.choice/Quot.soundのみ。
- 全repo build・巨大Audit.lean・全依存のゼロからの再構築は行っていない。焦点を絞った依存build済みcacheを使用。
- 初期公開 `62a23899e33010a1536667fdc7ef2fd6ae1b6747` の4moduleを別worktree・新しい出力libraryへtrust0で再コンパイルし、小audit3本・32宣言gateを再実行してPASS。最初の出力library設定はLeanのnamespace探索で継承依存が見えず失敗し、継承依存への個別symlinkと新module出力の分離を設定してやり直した。成功前の失敗を隠さない。
- 11moduleのsource公開 `3b7ad17f86af7b43e4b79dcdfa426875f69024d4`。ローカルと公開tree SHA `c66be8fb18e29ea479a7dcd7d027b782089a1c6d` は一致。別worktreeの公開11moduleすべてを新しい出力libraryへtrust0で再コンパイルし、13小audit・207宣言gateを再実行してすべてexit0。48公開定理のprint監査missing0。
- `bash tools/verify-lean.sh . b95d31b190f25633851ec805553bb57c792ffad7 --no-build`: PASS、exit0。5 REVIEWは新しい読取専用auditのrun_cmdのみ。production定理をメタプログラムで生成していない。全文をverificationログへ公開する。
- 独立した読取レビューで、構造的前提、実requestsの一致、同じ現在context/model、非空虚性、異なるinstall終点、coverageの穴とV5反例の区別、append-onlyを確認した。

## 失敗・制限

- 初期elaborationの型推論とPropからTypeへのExists除去を修正してから成功した。未検証のsourceを成功として公開しない。
- exact-SHA fetchを含むcommand runnerが「network approval was cancelled before a decision was returned」で終了した。対象commit objectが取得済みで、後続mergeが未完了と状態を確認。生きたgit processがないことを確認し、残った空index.lockを削除せず別名保存してローカルmergeを完了した。認証制限を迂回していない。
- 自分の初期公開と後半追加のmergeでimport/index/設計ノートが競合した。両側が自分の既知成果であることを確認し、後半追加を含む版を保持。後でappend-only・公開tree照合をやり直した。
- 使用量の枠・token使用量は不明。

## Yulang2との照合

`work/dots-audit` を取得し直し、既存 `x-oracle.md` のX1 Display where実使用とC3-PARENT/NEGの記録を読んだ。基点 `55574b6052ef1534fd0fc36d6d3617ebede59a0e`。既存の具体的runtime結果と今回のShared/NamedTreeの一般同値は未証明。新しい実機実行はしていない。旧runtimeの仕様差を今回の意味論へ持ち込まない。

## 次の仕事

1. NamedTreeの局所coverageを、実際のShared selection・完了条件から導く。旧MixedTreeの万能coverageは今回の反例で否定済みなので使わない。
2. 固定journalの旧Mixed coverageからAccは今回導出済み。次はNamedTreeの局所nodeへ拡張し、実際の完了条件からcoverage自体を導く。CoverageをV5境界へ仮定追加して解決扱いにしない。
3. 一般のdescriptor refreshで必要なreport/schema対応を精査し、同じ現在snapshotの子Evidenceへ接続する。通常拡張の定理を任意refreshへ拡張したと言わない。

## 公開53定理の量化・前提台帳

以下の一般定理では、記載のないroles・registry・状態・需要・宣言・payloadも任意に量化する。`現在モデル`は当該Shared状態の `Models current model`、`sourceモデル`はcontextの `GeneralNominalState.Models` を指す。固定実例の定理はその実例だけの主張である。全項目は補助または健全性補助であり、V5の完全性・主型性・全言語coverageの証明ではない。

### GeneralDictionary169RelocationComposition（3）

- `report_comp`【補助】: 任意の三つのsnapshot、二つのslot写像f,g、最初のreportについて、fによるmoveReportの後のgによるmoveReportは合成g∘fによる一回の移送に等しい。
- `at_trans`【補助】: 任意の三context、二slot写像、同じ需要とkeyについて、first→middleおよびmiddle→lastの `RelocatesAt` を仮定すると、合成写像によるfirst→lastの `RelocatesAt` が成立する。前提は計算report/schemaの対応であり、Evidenceではない。
- `packet_extension`【補助】: 任意の旧・新Shared状態とpacketについて、旧状態への `Relocates` と旧→新contextのordinary `Extension` を仮定すると、新状態への `Relocates` が成立する。packet membershipはこの構造的移送だけには不要。

### GeneralDictionary169LeafPersistence（1）

- `spine_query`【補助】: 任意のsnapshot、追加reserved/ordinary atoms/allocated一覧、有限Spineについて、ordinary拡張後に構造的に写したSpineのqueryは元と等しい。descriptor変更は含まない。

### GeneralDictionary169MixedPersistence（6）

- `packets_steps`【補助】: 任意の実際のShared Step列before→afterについて、beforeの全記録packetはafterにも存在する。
- `extension`【補助】: 任意の二Shared状態について、全旧packetのmembership保存、ordinary context Extension、旧MixedTreeを仮定すると、同じ需要・payloadの新MixedTreeが存在する。初期Evidenceは仮定しない。
- `ordinary_steps`【補助】: 任意の実際のShared OrdinaryStep列と旧MixedTreeについて、同じ需要・payloadのMixedTreeを終点で得る。
- `current_evidence`【健全性補助】: 任意のOrdinaryStep列、終点SourceFormed、始点MixedTree、終点の任意の現在モデルから、終点contextで同じ需要・payloadのEvidenceを得る。
- `source_formed_steps`【補助】: 任意の実際のShared Step列と始点SourceFormedから、終点SourceFormedを得る。
- `source_dictionary_steps`【健全性補助】: 任意のOrdinaryStep列、始点SourceFormedとMixedTreeから、終点の同じMixedTree、および任意の終点現在モデルに対する同じpayloadのEvidenceを得る。終点モデルの存在自体は結論にしない。

### GeneralDictionary169Selected（8）

- `relocated_selected`【補助】: 任意のSourceFormed状態、記録membershipとRelocatesを持つpacket、現在モデル、およびpacketと全く同じ需要でのFeedbackK2.Local selected判断について、packetのkeyと順序つき子一覧がselectedのkey・子一覧に一致する。別需要のalias移送ではない。
- `relocated_selected_evidence`【健全性補助】: 上記の前提に、selectedの子一覧に対応する同一現在context/modelのAll₂ child Evidenceを加えると、selected keyとそのpayload一覧による親Evidenceが成立する。
- `stable_current_instance`【健全性補助】: 任意のShared Stable状態、rootから生成済みのpacket需要、Installable packet、supportに対する完全なShared PacketGuard、現在モデルから、その現在contextでpacketのkeyと子一覧を持つInstanceを得る。StableだけではなくguardとInstallableを明示的に要求する。
- `stable_generated_children`【補助】: 同じStable・Generated・Installable・完全PacketGuardの前提から、packetのすべての子が同じrootからGeneratedであることを得る。モデル前提は不要。
- `stable_current_evidence`【健全性補助】: 同じStable・Generated・Installable・完全PacketGuardと現在モデルに、packetの子の同一現在context/modelでのAll₂ Evidenceを加えると、親Evidenceを得る。
- `child_payloads`【補助】: 任意の有限需要一覧について、各memberに同一context/modelのEvidenceを持つpayloadが存在するなら、元の順序・重複を保持するpayload一覧とAll₂ Evidenceが存在する。
- `installed_dictionary_exists`【健全性補助】: 任意のInstallable packetとsupportについて、実際のShared install後の現在モデル、および各子の同じinstall後context/modelでのEvidence存在を仮定すると、子payload一覧と親Evidenceが存在する。install後Stableは結論にしない。
- `actual_nonterminal_exists`【健全性補助・固定例】: 既存のShared Display install後状態で、現在モデルと長さ1の子payload一覧が存在し、key1の親Evidenceを持つ。既存の実行・辞書を新しい言語範囲として数えない。

### GeneralDictionary169FiniteCoverage（4）

- `node_tree`【補助】: 任意の局所構造Nodeと、そのNodeの子一覧に対するMixedTreeのAll₂証拠から、Nodeのkeyを持つ親MixedTreeを構築する。Node自体は記録packet+Relocatesまたはscalar/spine shapeで、semantic Evidenceを含まない。
- `accessible_tree`【補助】: 任意の需要部分domain、各memberへの局所Nodeを選び子closureを持つCoverage、およびdomain内rootについて、選ばれた子関係でのrootのAccからpayloadとMixedTreeの存在を導く。全有限木を前提にしない。
- `wellFounded_tree`【補助】: 上記Coverageの選ばれた子関係がWellFoundedなら、domain内の任意のrootについてpayloadとMixedTreeが存在する。WellFoundedをStableから導いたとは主張しない。
- `uniform_dictionary`【健全性補助】: 任意のCoverage、domain内focusのAcc、SourceFormed状態から、一つのpayloadとそのMixedTree、およびすべての現在モデルで同じpayloadのEvidenceを得る。payload存在量化はモデルの全称量化より外側。

### GeneralDictionary169FiniteDisplay（3）

- `accessible`【補助・固定例】: 実際のDisplay→Int install後状態のdomain={Display root,Int child}に選んだ局所Nodeの子関係で、rootはAccである。親から子へ一段だけで、子はsource scalar leaf。
- `uniform_dictionary`【健全性補助・固定例】: 上の局所coverageとAccから、一つのroot payloadとMixedTree、およびすべての現在モデルで同じpayloadのEvidenceを得る。既存MixedTreeを入力にしていない。
- `nonvacuous`【健全性補助・固定例】: 同じ実例についてpayload・MixedTree・現在モデルとEvidenceが存在し、全モデル結論が空虚でないことを示す。

### GeneralDictionary169SharedStable（5）

- `value_action_exists`【補助】: 任意のShared At(before,focus,after)から、同じbefore・focusでValue Atを持つ何らかのnextが存在する。SharedとValueのinstallの終点一致は要求せず、trace変換でもない。
- `of_value`【補助】: 任意のregistry・Shared状態・rootについて、ValueSteps.StableならSharedSteps.Stableである。同じfocusで有効なactionが存在しないことを用いる。
- `actual_stable`【補助・固定例】: 既存の有限ternary named-output初期例は、実際のSharedSteps関係でStableである。
- `actual_formed`【補助・固定例】: 同じ初期例は空journalのInitialSourceからShared SourceFormedである。
- `actual_stable_named_dictionary`【健全性補助・固定例】: 同じ例でSourceFormed・Shared Stable・明示モデルのModels・名前つき出力非空が成立し、任意の現在モデルでterminal payloadのEvidenceを持つ。非ゼロstepの新実行は主張しない。

### GeneralDictionary169NamedGap（3）

- `empty_named_not_mixed`【補助】: 任意の状態と需要について、journal=[]かつ需要outputs≠[]なら、すべてのpayloadについて旧MixedTreeは存在しない。recorded constructorは空journalに、scalar/spine constructorはoutputs=[]要件に矛盾する。
- `actual_not_mixed`【補助・固定例】: 上のnamed-output初期例では、すべてのpayloadについて旧MixedTreeは存在しない。
- `stable_named_coverage_gap`【補助・固定例】: 同じSourceFormed・Shared Stable・現在モデル・semantic Evidenceが存在する状態で、旧MixedTreeはすべてのpayloadについて不存在。これは旧証明書のcoverageの穴でありV5の反例ではない。

### GeneralDictionary169NamedLeaf（7）

この群のLeafShapeはterminal要件、scalar入力の実slot/head/query/arguments、入力binderなし、RootDefined、および実計算reportのbindingsから作る実際のmaterialization requests全部の有限Observed証明を持つ。outputs=[]は要求せず、Models/BranchModels/Instance/Evidenceはshape内に含めない。

- `report_exact`【補助】: 任意の上記LeafShapeについて、実計算reportは一つのinspected pointと二つのchecked pointからなる指定reportに等しい。
- `branch_models`【健全性補助】: 任意のregistry/context/root/declaration/checkedとLeafShape、任意のsourceモデルから、その実slotに対するBranchModelsを導く。実named materializationの全義務を含む。
- `ready`【補助】: 任意の同じLeafShapeからRootDefinedかつ実generated schemaのunknown=false、すなわちRequestReadyを導く。モデルは仮定しない。
- `instance_of_shape`【健全性補助】: 任意の同じLeafShape、宣言の可視性、Metadataとsourceモデルから、宣言keyと空子一覧のInstanceを導く。選択判断やpacketは仮定しない。
- `evidence_of_shape`【健全性補助】: 上と同じ前提から、宣言keyのterminal payloadに対するEvidenceを導く。
- `actual_evidence`【健全性補助・固定例】: 実際のternary named-output例の任意のsourceモデルに対し、一般LeafShapeの解釈からterminal Evidenceを導く。
- `actual_nonempty_output`【健全性補助・固定例】: 同例のLeafShape存在、outputs非空、およびsourceモデルとEvidenceの存在を示す。既存辞書そのものではなく新しい構造的十分条件の適用。

### GeneralDictionary169NamedTree（4）

- `current_evidence`【健全性補助】: 任意のSourceFormed Shared状態、NamedTree、現在モデルから、同一context・需要・payloadのEvidenceを導く。NamedTreeは旧MixedTree、移送可能なrecorded node、実named LeafShapeを再帰的に混ぜられる。
- `actual_tree`【補助・固定例】: 実際のnamed-output初期例に、一般named LeafShapeからterminal NamedTreeを構築する。
- `strict_coverage`【補助・固定例】: 同じ例にNamedTreeが存在する一方、旧MixedTreeはどのpayloadにも存在しない。新証明書coverageが真に拡張されたことを示す。
- `stable_named_interpretation`【健全性補助・固定例】: 同じ例でSourceFormed・Shared Stable・NamedTree・明示現在モデルが共存し、全現在モデルで同じterminal Evidenceを持ち、旧MixedTreeは全payloadについて不存在である。

### GeneralDictionary169NamedPersistence（4）

- `observed`【補助】: 任意のsnapshot、ordinary追加一覧、interpretation、request一覧について、元のObservedが成立すればordinary拡張後も同じrequest一覧のObservedが成立する。descriptor変更は含まない。
- `extension`【補助】: 任意の二Shared状態について、全旧packet membership保存、ordinary context Extension、旧NamedTreeから、同じ需要・payloadの新NamedTreeを導く。旧Evidenceを仮定しない。
- `ordinary_steps`【補助】: 任意の実際のShared OrdinaryStep列と始点NamedTreeから、終点に同じNamedTreeを得る。
- `current_evidence`【健全性補助】: 任意のOrdinaryStep列、終点SourceFormed、始点NamedTreeと終点現在モデルから、終点で同じ需要・payloadのEvidenceを得る。任意のrefresh・任意のStableからのcoverageは主張しない。

### GeneralDictionary169CoverageAccessible（5、追加後合計53）

- `packet_child_above`【補助】: 任意のpacketと、その実childrenに属する子について、子のliteral identityはpacket親需要のidentityより真に大きい。registry可視性・SourceFormed・モデルは仮定せず、実emitterとallocatorの定義から導く。
- `child_rank`【補助】: 任意の固定Shared状態と旧Mixed NodeのCoverageについて、選んだ子edgeごとにrank(child)<rank(parent)。rankは有限journalの親identity最大Mに対する(M+1)-identityで、leafからedgeは生じない。
- `coverage_accessible`【補助】: 任意の同じCoverageとdomain内focusについて、選ばれた子関係のAccが成立する。Acc・domain有限性・SourceFormed・モデル・実行停止は前提にしない。
- `covered_tree`【補助】: 任意の同じCoverageとdomain内focusから、payloadと旧MixedTreeの存在を導く。外部のAcc前提を除いた構築定理であり、Coverage自体の存在は証明していない。
- `covered_dictionary`【健全性補助】: 任意の同じCoverage・focusとSourceFormedから、一つのpayloadとMixedTree、およびすべての現在モデルで同じpayloadのEvidenceを得る。固定journalについての結果であり、実行中のjournal増大や全Shared Step停止は扱わない。

## 最終source検証

最終source `e791991e45150f47094f2b61289ea4622563427c`、tree `0fc79cb903ac5ff1bb270c1724bcc5a65114cbd0`。公開済みexact SHAを新しいworktreeへ取得し、12moduleの既存oleanを排除した別libraryへすべてtrust0で再コンパイル。15auditすべてexit0、5gate計218宣言PASS。53公開定理のprint監査missing0。依存libraryは既検証cacheを継承しており全repoのfresh buildではない。公開append-only gateはexit0、5 REVIEWは新規auditのみ。完全ログ・manifest・量化台帳を添付。

## 最終読取レビューと次回引継ぎ

公開sourceとローカルのNamedLeaf/NamedTree/NamedPersistenceの一致を再確認。NamedNodeはrecorded/scalar/spine/namedの一nodeだけとし、全MixedTreeをlocal coverageに埋め込まない。named leafは子なしなので有限journal rankの拡張が見込めるが、今回は未実装。鍵・子順序のcoherence、実Shared終了状態からの局所coverage存在が次の主な義務。詳細はnext-groundノート末尾に記録した。

## 終盤のintegration更新

17:12 UTC再確認でintegrationは `2433dc974cc71201cf22bd15782b977e112f1f4a` へ進んでいた。8新Astra moduleの差分・ground-factorizationノート・主要型を読み、inboxは同じI27 ACTIVEと確認。今回は基点b95で検証済みのsourceを保ち、終盤の追加は未merge・未build。次回最初に統合する。新しいbranching operational Accと有限capture意味ラベルは、実snapshotの辞書coverageを自動で供給しない。この差と具体的な次の接続をnext-ground末尾に記録。

終了前空き容量37GiB/63GiB（39%使用）。開始時の正確な容量は本報告に保存できておらず不明。個別olean symlinkによる依存共有で巨大cacheの複製はしていない。

## 最終整合性確認

53定理すべてが量化台帳に存在し、12moduleのmanifest SHAが公開sourceと一致。既存Lean変更はYulang.lean末尾の12importのみ、その他27Lean pathは新規。新productionにsorry/admit/axiom/native_decide/unsafe/run_cmdなし。中間公開の検証worktree2個はdirtyなし・最終公開の祖先であることを確認して除去し、最終公開worktreeと再現ログは保持した。旧サイクル作業場には触れていない。

## 終了台帳

2026-11-13T17:17:26Z、最終検証完了（開始から49.4分）。最終公開sourceから5gateをもう一度実行し218宣言すべてPASS、exit0。公開report・JSONのreadback一致、最終notesまでLean差分なしを確認。全proof worker・compile終了、承認待ちなし。完了心拍とこの台帳を同一treeで公開する。55分上限内。
