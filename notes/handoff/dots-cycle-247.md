# cycle247: guarded recovery and executable ordered rebase

## 状態・時間

- 開始: 2026-11-17T20:30:33Z。21:15頃まで証明・実ソース境界のレビューを継続し、その後に本報告を作成。
- 本周の最終 Lean 成果: 30 新規モジュール、503 定数の依存公理監査 PASS。
- 検証済みコード公開: `aa0d947ec199ef3523a873a9b8d481884094329d`。
- 公開 tree: `cc873f7c26444d53a7064e5da2e640b43637a292`。ローカル全 tree の独立再計算と一致し、GitHub の branch/commit/tree を取得して照合。
- integration は開始時・最終確認とも `a1c54ee3887603466d82b10515d887c78dbb017d`。standing orders と inbox を再読し、I47 を継続。新しい STOP はない。
- 本報告・receipt・完了 heartbeat の公開を含む最終時刻は heartbeat に記録する。21:25 UTC が親から指定された終了期限。
- 使用量の枠は不明。全体ビルド・verify-lean.sh は実行していない。
- この周全体で変更・追加する公開ファイルは62（30 Lean、4監査、barrel、設計・検証・報告等）。未採用 draft は含めない。

## 復旧と制限

前周246の最終公開・検証を20:30までに確認してから本周を開始した。246で期限を超過した事実は246報告に記録済みで、成功扱いに置き換えていない。

本周21:09頃、短いコマンドの開始時に `exec-server transport disconnected; recovery timed out after45s` が発生した。長いビルドは既に完了しており、原因は特定できない。環境へ再接続でき、未公開6モジュール・監査ログ・source hashが残っていることを確認した。再接続後はこのスレッドのファイル操作が読み取り専用になったため、GitHub APIで回収ファイルを公開した。30/131 source hashの再照合は変更なし。最終のファイル群を失っていない。

読み取り専用のため、最終commitをローカルへfetch/mergeしたとは主張しない。ローカル HEAD は `6012681fd`（phase3）のままで、公開済みの6モジュール等がローカルでは未追跡/未commitとして残る。次周は最新remoteを取得し、bytesを比較してから整理すること。二重公開や未追跡成果の削除をしない。

## 主要定理と前提（名前の先頭 GeneralPresence は省略）

### 1. guarded の実モデルを回復する

- `GuardedRecovery247.models_equations/recover_values/extend_compatible/all_recovered`: 任意の246 guarded body、targets、parameters、代入について、実 block のモデルをCommon guarded closureの方程式へ移し、そのモデルと構成された拡張は型の双方向部分型・全rowの等号で対応する。既存モデルの回復であり、無前提で任意方程式のモデル存在を仮定していない。
- `GuardedAbsorption247`: old/fresh が同じ固定targetを使い、old parameterがそのtarget外なら、old拡張はfresh拡張を吸収する。fresh bodyのparameter分離をこの吸収だけの前提にはしていない。
- `GuardedConsumers247`: typed readsがtarget外の任意consumer集合について、guarded definitions追加の存在射影は元consumerの成立と同値。row readsは全row不変なのでprivate nameを含んでよい。
- `GuardedAllocation247`: supplied parameters/consumer typed supportより大きいNat列を一度予約し、injective targetsと分離条件を構成する。extra予約nameの完全性や、毎refreshで再予約することは保証しない。
- `GuardedEnvironment247/GuardedRebase247.public_models_iff`: 明示的closure environmentで旧解釈を残し、任意consumer（private readを含む）の公開解集合を保存する。新しい表現上の定理であり、実journal/cache adapterそのものではない。
- `GuardedCommutation247/GuardedCompression247`: disjoint targetsと相互のparameter独立性があるowner間の交換、および独立な中間closureを挟んだ局所圧縮を証明。全履歴の一律正規化や長さ上界は主張しない。
- `GuardedExamples247/GuardedRebaseExample247`: recordDefault/arrowを含む相互再帰とprivate/self row readを扱う具体例。raw private値の一部の不等号は構文の不等号であり、常に意味上の非同値を示すわけではない。

**重要な修正:** 実 `GeneralNominalAllocation.lower/upper` は root var/union/inter を含む。246のpayload-guarded文法ではこれを一般には表せない。そのため次のactual TyTerm用の別経路を実装した。guarded経路だけで実lo/hiを覆ったとは報告しない。

### 2. actual Presence TyTerm の順序付きblockを解く

- `OrderedBlock247.block_satisfied/arbitrary_public_model`: 任意ModelのsubTy反射性とSafeOrderの下で、RHSを順に評価して型座標だけを書き込む実行版solveが実equationsを満たす。全rowとtarget外の全値はそのまま。SafeOrderは後のRHSによる前のtargetの参照を許し、前の式を後の書込みが壊す参照・自己型参照・重複targetを禁止する十分条件。
- `OrderedCheck247.check_exact`: 有限Bool判定がSafeOrderと同値。root aliases、union/inter、arrowのprivate rowを含む回帰を検証。
- `OrderedRecovery247.solve_compatible/all_recovered`: 任意245.Laws modelと既存blockモデルについて、順序条件なしでsolveとの型同値・row等号およびconsumer成立同値を得る。循環blockのモデルが存在するとは主張しない。
- `OrderedDependence247.solve_equal/solve_absorbs`: old SafeOrderとfresh target包含の下、old solveはfresh書込みを文字どおり吸収する。吸収だけにはfresh SafeOrderは不要。
- `OrderedSubstitution247.mapping_eval/rewrite_exact`: 任意有限entry列について、実CompTermへの有限mappingを構成し、その評価がsolveと文字どおり一致する。任意Atom列の置換はsolve下の成立と同値。guarded環境と異なり実有限構文に留まる。
- `OrderedRebase247.public_models_iff/common_public_models_iff`: old/fresh SafeOrder、fresh target⊆old target、公開名がold target外という明示条件の下、任意consumerについて旧block付きモデル存在と、旧mappingでconsumerを書換えた新block付きモデル存在が、同じ公開boundaryごとに同値。Common具体Lawsでインスタンス化済み。
- `OrderedRebaseExample247`: 2=var0、3=union(2,1)、4=inter(3,0)のactual構文と別のfresh blockで、任意private consumerに上記を適用。mappingの具体展開とrow不変を確認。
- `OrderedCycleLimit247.public_equivalence_fails`: old self-aliasを無条件に展開/置換すると、Commonモデルでも公開解を失う閉じた補助表現の反例。SafeOrderを勝手に削除できない。source到達可能性や言語の反例ではない。

### 3. 順序・重複・初回supportを実行版で供給する

- `OrderedSupport247.safe_independent/safe_pool/safe_full_sources_pool`: distinct targetsと、全RHS typed readsを覆うpoolからtargetが分離される条件でSafeOrderを導く。full source poolは十分だが、rowまで禁止するので必要以上に強い。
- `OrderedAllocation247.safe_entries/initial_add_definitions`: 任意のactual TyTerm RHS列、consumer、extraKnownを列挙し、そのtyped supportより大きいtargetsを予約してSafeOrder・consumer分離を構成。任意反射的Modelでconsumer成立と全support値・全rowを保つblock拡張の存在が同値。初回専用でありrefreshの再割当て規則ではない。
- `OrderedDedup247.targets_nodup/block_all_iff`: keep-firstで相対順を保って重複targetを除く。targetsNodupは任意listで成立。元blockとの成立同値は同一targetのRHSが一致するCoherentを前提とし、衝突した異なるRHSを勝手に捨てない。
- `OrderedCoherentAdapter247.original_satisfied/pool_extension/original_public_models_iff`: 内部だけdedupし、元の重複entryを含むequations全体のモデル構成・公開解保存へ戻す。
- `OrderedSort247.sort_sound/sort_complete`: finite fuelのtopological sortが成功すると入力のPermutationとSafeOrderを供給（targetNodup前提）。各block内typed dependencyが厳密に小さいNat rankを持てば成功する。rankの実sourceでの供給は未証明。sort失敗をsource拒否にはしない。
- `OrderedPrepared247.prepared_models/prepared_extension/prepared_public_models_iff/prepare_complete`: coherent dedup→sortを一つのprepareに繋ぐ。成功時、元blockの成立を正確に保存し、元blockの公開解保存に使える。成功証拠を使う経路とrankによる成功保証を区別する。

実 `Declaration.inputNames` は単なる変数列の連結で重複しうる。Definitions241.coherentからNodupが自明という誤った前提を置かず、dedup adapterでこの穴を処理した。ただしactual Definitions241へのimport付き適用とfreshness producerは未接続。

### 4. 同じconsumerの再展開と、private queryを扱う

- `OrderedRewriteAbsorption247`: 任意Modelで再書換えの意味的吸収。
- `OrderedSyntax247.mapping_closed/type_absorbs/rewrite_idempotent/rewrite_absorbs`: SafeOrderのmappingはold targetへのtyped readを除き、row readは残す。fresh targetがoldに含まれるなら、旧mappingで書換え済みのconsumerにfresh mappingを適用しても文字どおり変わらない。
- `OrderedRefreshSequence247.run_preserves`: 明示的にSafeOrder/target包含を満たす任意有限refresh列で、同じ公開解集合を保持。
- `OrderedRefreshSyntax247.first_refresh_stabilizes`: consumerを追加しないこのrunでは、最初の展開後のconsumer構文は固定される。新しいpacket/history atomの追加、live RHSの成長、cross-owner仕事やsolver停止は含まない。
- `OrderedQueries247.query_exact/query_forward/observed_public_models_iff`: 任意の明示的tagged CompTerm query bundleを同じmappingで運ぶ。型の双方向部分型とrow等号に安定なobserveについて、consumerと列挙された全observationを**単一のwitness**で同時に満たす公開モデル存在を保存する。Common query probeは全depth/rankで保存。
- `OrderedQueryLimit247.raw_private_changed/transported_private_preserved`: old2=var0、fresh2=exactEmptyという双方safeな例でも、raw private address2の値は意味上変わりうる。一方で置換queryは保存される。private名を公開リストから消すだけでは実source観測を扱えない。

## 検証

Lean 4.35.0。各対象について `lean --trust=0 -DwarningAsError=true` を使用。

1. `python notes/verification/cycle247/verify-final.py`: EXIT0。30対象を依存順に再構築し、`Cycle247Final.lean` が **503 constants /30 modules PASS**。出力全文は `final-build-audit.txt`。
2. `timeout 7m python notes/verification/cycle247/verify-focused-closure.py`: EXIT0。独立した空cacheへ129モジュールのfocused依存閉包を厳格再構築、176.55秒。出力全文は `focused-closure-build.txt`。
3. 上記clean cacheでQueries247/QueryLimit247を追加コンパイルし、同じ最終監査もPASS。計131 source hashは `clean-final-source-sha256.json`。観測した追加検証コマンド/出力は `clean-final-audit.txt` に記録。
4. 公開前と環境復旧後に30/131 source hashを照合し変更なし。禁止token scan PASS、diff --check PASS。新規公理なし。監査の許容依存はpropext/Classical.choice/Quot.soundのみ。
5. `lean/Audit.lean` と `lean/README.md` は変更なし。barrelはappend-only。旧Leanモジュールを変更せず、新規モジュールと独立監査を追加。
6. 全体ビルド、verify-lean.sh、実sourceの旧回帰199/202/204/206/218/230/239/240の後継での再検証は未実行。Definitions241依存閉包は710/未cache625と測定し、その巨大buildは開始していない。

## 受け入れ条件と残り

I47の置換表現の実装部品は進んだが、後継SourceBoundary・12法則・solver Acc・無条件EvidenceNodeは未完成。言語の受理範囲を狭めていない。I45の既存point descriptor条件も変更していない。

次の作業は3段階に絞る（詳細はfinal-boundary-review）:
1. 実source/metadata adapter: Definitions241、243Origin/packet/history/cache等を一つのwitness上へ接続する。promoted base.source/descriptorを隠さない。actual source rank/freshness・循環時の意味保存を作る。OriginView243のexact readbackへmapping_evalを繋ぐ5補題案を設計ノートに記録したが、未実装。
2. 後継の同一public-model解釈と実操作: projected Models(boundary)なら既証明iffが同じboundaryのstepModelsを供給する。しかし旧full Assignment解釈・current packet/Evidenceとの対応、実有限進捗・その他bridge・旧回帰の移植が残る。有限名/有限sort/固定consumerだけからAccを宣言しない。
3. 実selected-node EvidenceNodeと最終composition。I40で取り下げられたFreshCompletion/一般GeneratedChildrenを新義務として復活させず、既存211/220のselected-tree経路を移植する。

追加の意味論判断をユーザーへ要求する新しいsource反例は今回示していない。補助表現の二つの反例は境界の誤用を防ぐ回帰である。

未採用 `notes/recovery/cycle247/GeneralPresenceGuardedNormalization247.lean.draft` はglobal normalizationの途中案で、採用・import・監査・定理数に含めない。既存244の未検証draftも今回の成果に数えない。これらを検証済み成果として公開していない。
