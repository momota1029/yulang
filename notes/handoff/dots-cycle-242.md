# Cycle242 — 実到達状態の有限ownerと、射影を保つrebase部品

開始:2026-11-17T14:30:13Z。研究目標15:15、検証・公開の上限15:25 UTC。
I47を継続。新しい全SourceBoundary、一般Acc、EvidenceNodeは未完成。

## 開始と復旧

integration a254e23eのstanding-orders/inbox、241報告と完了心拍を再読。
STOPなし、競合プロセスなし、永続treeと241成果はclean。統合を取り込んだ。
開始直後に実行接続が切れたが再接続で復旧。永続領域のファイルは残り、
今回の未公開証明の消失はない。再接続後の書込制約は許可された範囲で確認した。
15:01の再取得でもintegration/inbox更新なし。spec・notes/plan・既存proofは未変更。
凍結Audit.lean/READMEは統合版と一致。作業開始時空き39GB。

## 最重要の結果

1. **任意の実PointSourceBoundary240到達状態から有限owner集合を生成**した。
   `BirthWitness242.source_owners`の追加前提はSourceReachableのみ。
   終状態Modelsの非空性、Bounded、仮想trace、深さ上界を追加前提にしていない。
   実初期GroundRootsからラベル質量を取り出し、実installのcommon witnessで
   子誕生時の深さを制限し、後にModelsが空でも所属を構造的に保持する。
   固定初期context版もあり、終状態ごとに別のpoolを選んで有限と呼んでいない。
2. そのowner列挙を重複除去して`Fin`索引と単射を生成。任意bindingsについて、
   stable rebase allocatorの全private targetを固定有限domainへ包含した。
   **旧240の無限version名が有限になる定理ではない**。既存非停止反証はそのまま。
3. 旧private名を読むordinary consumerを消さず、旧定義をinlineして
   base・全他ownerを保つStore射影iffを証明。全raw nominal descriptorも
   `RawInline`という意味pullbackで保持した。raw Stateへの実行可能な書換えは未構成。
4. 新RHSが旧private名を参照する場合、実lower/upperのvar/union/inter断片は
   旧代入で外部化できる。旧External・coherentと新target包含から新Externalを生成。
   一般row位置の消去、未定義の新activeセルまで無条件に広げていない。
5. 有限fact schedulerを、任意block serviceから現在factsのcompile結果に限定。
   新factは全ownerをdirtyにし、cleanなら現在blockと一致。停止・最小閉包・
   順序独立を証明し、実行可能なfind?とrankをfuelにするrunまで構成した。
   230の実merge式で`run initial = final`が計算(rfl)で通り、raw source・actual W・
   publicAtomsを保持する。一般source境界のexecutorではない。
6. B4.stepModelsの同一model量化子を再確認し、private値を内部存在量化する
   PublicModel242を構成。**同じpublic assignment**で局所raw/atom置換のModels iff。
   実230 old/new entriesでも同じpublicモデルで旧新Modelsが成立する。
   旧新内部assignmentの同時両立を主張しない。

## 追加定理の範囲（量化子と前提）

全て補助・将来の健全性/完全性/停止性接続の部品。M1三つ組完成ではない。

- Birth/Genealogy/Batch/Ground: 任意実Plan/Frame/Holds/Coverage、親登録、registry/seed/
  algebra一致、全既存live centerのBackExtensionのもとで、実正準全子の追加と
  任意有限birth/rebase traceに沿うdepth+mass予算を保存。GroundRootsから初期予算生成。
- Install/Operational/OperationalOwners/BirthWitness: 上の追加前提を実旧kernelの
  install/step、metadata、登録、source initialから生成。非空前提のある中間定理も
  残した上で、最終source_ownersでは誕生時witnessを使って終状態非空前提を除いた。
- OwnerUniverse/OwnerIndex/DistinctOwners/PrivateUniverse: 任意実Generated需要と可視宣言の
  ownerを固定有限配列へ写す。単射と、stable private cell数
  `ownerCount*(全registry inputNames数*2)`の列挙上界。endpoint/RHS全体の有限性とは別。
- EscapedProjection/Replace/Store/Merges: 任意有限旧新定義についてcoherent、RHS外部性、
  newtargets⊆oldtargetsを明示し、任意ordinary consumersを含む正確な存在射影iff。
  実merge entriesの外部性はFresh+Endpointsから、target包含は多発条件から生成。
- MergeExternal: 任意newbindingsの実lower/upper RHSを旧substitutionで書き換え、
  全旧targetへの非参照を生成。旧coherent/Externalとnewtargets⊆oldtargetsが必要。
  評価は「新物理target」と「旧patch上で評価した新RHS」の等価で、旧新defsの同時保持でない。
- RawProjection/PublicModel: 任意raw snapshotの完全Models（nominal/rowを含む）とordinary
  atomsを対象にした射影/同一publicモデル保存。Private外exact値・全row一致を保持。
  Whole livecenterのreadbackや独立Evidenceの内部witness不変性は未構成。
- AggregateFinite: 明示有限endpoint poolに含まれる任意非空boundsのlower/upperに、
  **一つの代表を先に選び全modelで同値**な有限候補を生成。候補数2^pool.length。
  有限source名列ならpair pool長はsourceCount²。pool生成と、任意nested式の有限化は別。
- Scheduler/Order/Executor: 任意有限fact/owner、ownerAt単射、compile/discoverについて
  clean-table invariant、全状態Acc、runの経路/停止/閉包。最小閉包とtable順序独立には
  discover単調性を追加。実source discoverの生成は未証明。
- Lookup: 有限List.find?から実行可能なsubstitution/patch/RHS rewriteを生成し、coherentな
  旧定義に対して既存の意味的patchと一致。全row保持と自己参照書換えの計算回帰。
- 230Scheduler/Executor/Public: 実230の旧新merge、raw snapshot、actual、publicAtomsを用いた
  計算/モデル回帰。全historical journalや新境界EvidenceAtの完成ではない。

新29モジュールの全宣言名・実際の型はLeanソースを正本とする。
`Audit/Cycle242All.lean`は生成定義を含む全29モジュールの推移公理を検査する。

## 局所的に不採用としたshortcut

`NewCellObstruction242`は、olddefs空、旧consumer cell=a、新def cell=bで、
private対象をold/new unionへ広げるだけでは射影が保存されないことを実O/Wで検査。
consumerを消すとモデルが復活するため、その削除は制約喪失となる。
この偽の一般化は追わない。**I47 option A全体への反証でも、意味論判断待ちでもない**。
新規activeセルの未使用性/全consumer非干渉を別に生成する必要がある。

## 検証

- 全追加モジュール: `lake env lean --trust=0 -DwarningAsError=true`、個別および最終通し検証。
- 全追加定義の推移公理: propext/Classical.choice/Quot.soundのみを許可。最終ログ参照。
- 公開前の禁止語scan、ソースSHA256 manifest、凍結一致を記録。
- 実operational接続の不足依存44本を小並列で焦点再ビルド。全体buildではない。
- 一度、一覧末尾改行不足で最後の例をビルドせず監査がmissing objectで失敗。
  当該例を直接検証し監査再実行PASS。別のmissing dependencyも全て焦点再ビルドで解消。
  失敗ログを隠さず、訂正監査ログと最終通し検証ログを併置する。
- `git diff --check`が指摘したのは依存ビルド生ログの末尾空白のみ。ログ全文を保持した。
- 全体lake build/verify-lean.shは監督専有のため未実施。CI成功は主張しない。
- 使用量の残枠は不明。

## Yulang2との照合と回帰

work/dots-auditを取得しx-oracleの既存Parent/child・幅部分型記録を参照。
今回のprivate rebase表現をYulang2実機で再実行してはいない。旧実機の成功を
新source境界の証明と数えていない。199/202/204/206/218/239/240の既存ソースを保持。
新全境界が未定義なので、それらの新境界への回帰輸送完了とも主張しない。

## 残りの3群と次回

1. **実行可能な射影state/readback**: raw descriptor・全livecenter・output・子certificateを
   式viewへ写し、独立Evidenceとの意味対応を生成。新activeセル、循環、旧RHSの外部化を
   実到達不変条件として保証。PublicModelの存在witnessを子ごとに混用しない。
2. **finite fact閉包**: 今回の実owner/target有限性から、全endpoint・source promotion・row/
   output・descriptor・観測式までの有限閉包を生成。単なる有限名前数やhelper数では足りない。
3. **完全な操作写像**: 実操作をnewfact/dirty serviceへ写し、run閉包から実Stable/Local/
   Evidenceを導く。B4の14フィールド対応はcycle242-b4-bridge-mapを参照。

I47の範囲で次回を継続可能。新しいユーザー意味論判断待ちや全作業STOPはない。

## 中間公開

- faf6be79: 7 modules/92 constants、公開treeとローカル差分0。
- e1c6389a: 26 modules/341 constants、tree7fad5dd6、local d86e7c670と全tree差分0。
- 最終焦点検証:29 modules/373 constants、全direct buildと推移公理監査exit0。
- runtime実評価:`(facts0,dirty0,block.length)=(true,false,8)`、rank `(2,1,0)`、lookupの存在/不在はtrue/false。
- 終了時空き39GB。最終公開SHAと所要時間は取得照合後のreceiptに記録。

## 最終公開・照合receipt

成果commit `b6c99bab299a441de096435457bc28f5176dc192`、tree
`2427f538ddd5cefcbc12cd3399eea448356a6a4e` をGitHubから再取得し、
local `5ec13f763dfb8ec0958ba1317e3c2565499e5aaa` と全tree差分0。
29ソースのmanifest hashを再計算して一致、作業tree clean、凍結2ファイル一致。
サイクル前e6c5883eから60ファイルの追加・変更。未公開の検証済み成果なし。
GitHub commit statusesは空配列。CI/監督全体検証のPASSは主張しない。
照合記録 2026-11-17T15:13:35Z、経過43.4分。約45分の範囲で研究・検証を進め、55分上限内で公開完了。
残る作業はI47のproducer/後継boundary構築。次の定期wakeまで追加作業しない。
