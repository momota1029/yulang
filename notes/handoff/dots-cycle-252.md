# dots cycle252 — I49再開、有限owner／正規形、展開深さの実source反例

## 結論

開始2026-11-18 08:30:13 UTC。最新integration48627b59eのI49に従い停止性設計を再開。
前回cycle251は正常終了、work/dots-mainの全tree一致・競合writer不在を確認した。

**I49のmax深さ上界をpublicなground展開形に適用すると破れる実source例を閉じた。**
これを受けて08:47頃に新実装を停止し、独立再検証・監査・公開に切り替えた。
I45のpoint-preserving source境界でも、全guardを満たす実Step/Reachable/モデルを
含めて閉じている。言語の非停止、意味論の矛盾、生のjournal構文の深さ増大を
主張する反例ではない。表現上の上界の解釈または修正を監督役へ返す。

全12新規moduleの229個の明示public宣言を監査。さらにprivate/generatedを含む
全389宣言をcollectAxiomsで検査した。許容依存はpropext/Classical.choice/Quot.sound。

## 反例の内容と量化

主定理: `GeneralDictionaryOutputDepthInstall252.point_public_readback_exceeds_max`。

- registryはchecked。headは型変数a、whereなし、associated output=F(F(a))。
- ground入力はF(Int)、output slot3は初期には未拘束。実binderは入力slot2。
- 一回の実I45 install後にoutput=F(F(F(Int)))が成り立つ。
- `output_forced`: **任意assignment**について、install後のModelsならslot3の型は
  この深い出力と同値。都合のよいモデルを一つ選んだだけではない。
- `point_step` / `point_reachable` / `installed_model` はactual source/kernelのもの。
  safe、cache、materialization、candidate choice、inspection positions、alternatives、
  common witness、noveltyを全て供給。入力は循環せず、point descriptorを変えない。
- 入力ground patternのdepth=2、RHS template=2、代入後ground pattern=4。
  `expanded_value`が代入後patternの意味を実RHS値に接続する。

pure nominal chainなので、union重複やhidden fieldを削ってもこの展開は縮まらない。
ただしraw journalはvar参照を保持するのでtemplate自身の深さは2のまま。
I49のDを**opaque public名を保持した生構文だけ**に限定するなら、この証明だけで
その上界を反駁しない。その場合も、public ground readbackと有限basisの関係を
別に説明する必要がある。新rebase境界の実行やAcc否定へ読み替えてはいけない。

Counter fixtureは3modules（OutputDepth252/Cycles252/Install252）。専用worktreeで
構成し、main側へコピーした後に独立strict再buildと全179宣言監査も再実行した。

## 反例までに閉じた不変条件

### 実sourceの有限owner key（2 modules）

`GeneralNominalOwnerCandidates252` は既存MixedAncestry237の実traceからの
`depth+mass(labels)≤mass(rootLabels)`をInvocationAncestry.frontierへ接続する。
型の有限集合とidentityを同一視していない。actual allocatorの有限生成pathを使う。

- 任意source formation/ground point root/coverageと実mixed pathについて、installable
  かつnovelなeffectの(root identity, declaration id)は明示有限list ownersに入る。
- branching Bをregistryのwhere節数の和とすると、frontier列挙長は(1+B)^depth。
  owner候補列挙長は(1+B)^mass(rootLabels)×宣言数。重複を含む上界列挙である。
- `GeneralNominalSourceOwnerCandidates252.mixed_finite_owners/point_finite_owners` は
  **actual initial sourceだけ**から、一つの有限keysが全後続traceのinstallationを
  覆うことを示す。finite depthを追加仮定しない。I45 pathはmixed pathへ消去する。

これは現source版での成果。rebase後継Stepが同じreadback/ancestryを保存する橋は
未完成であり、source Accや全metadata/slot名の有限性と混同しない。

### 有限pool上の集約正規形（7 modules）

- UnionNormal252 / InterNormal252: unionまたはintersectionを再帰的にflattenし、
  pool順の所属filterからfoldする。任意assignmentで、全atomがpool内なら意味同値。
  再正規化は同じsyntax（冪等）。poolがNodupなら代表listもNodup。
  全型・行readを調べたprivate非流出と、元termのtypedReadsから増やさないこと。
- NormalFinite252: pool長nに対し2^n個の候補を明示列挙。重複・順序に依存しない
  atom集合なら同じ代表。SnapshotGrowth251の全tree(n)がvar0へ正規化される。
- SnapshotNormal252: 実ordered mappingでsnapshot代入した後の正規化の意味を
  `raw.eval (solve old assignment)`と同値にする。前提は各旧atomの代入結果が
  pool内に閉じること。sourceがその条件を満たすこと自体は仮定のまま。
- CheckedNormal252: pool内所属を検査しOptionで返す。成功 iff 所属+正規化結果、
  成功時の意味保存・再準備成功・private非流出。異演算は一つのatomであり、
  pool外のinterをlower union poolで読む例はNone。空式として誤受理しない。
- NormalBlock252: 実定義blockのtarget list、SafeOrder、同一assignmentでのblock
  Modelsを保存。実materialized frameのModelsも全atom supportedの下で同値。
  persistent snapshot後の正規化もSafe・旧target list保持。
- FiniteBlocks252: 固定target list全体の正規化済みblockを明示有限列挙し、長さを
  各slotの2^(pool長)の積で与える。実persistent refreshの結果もその列挙内。
  SnapshotGrowth251の任意nから一回の正規化refreshでdefinitions0へ戻る回帰。

これらは一般のmixed union/intersectionやnominal全体の正規形ではない。
異演算/constructor内部は原子として扱う。source閉包、sourceの全段生成器、
metadataの反復、全Stepの厳密な進捗までは証明していない。

## 設計上の残りと停止判断

I49の1は現source上で有限identity pathを再利用できた。2の表現局所不変条件も
閉じた。しかし3のmax-depthはground展開に適用できず、2の固定basis closureと
4の将来public escape全体はまだ閉じない。5は有限性だけでなく、同値な再見直し
を除外して各Stepが新factを増やすという厳密進捗の証明が必要。

次は表現上界を監督役が判断する。候補はtemplate代入の加算・output依存に沿う
assembly上界を使うこと、またはopaque public nameを保った有限表現とground
readbackを明示的に分けること。どちらも言語受理を変えずに検討すべきであり、
勝手に上界を差替えてAccへ進めない。停止中の設計研究はI49が許可しているが、
この反例を無視した実装継続はしない。言語意味についての新質問はない。

## 検証・公開・時間

Lean4.35.0、全12moduleを依存順にtrust0/warningAsErrorで再検証し、229 public名
および389全宣言を監査。最終command列・出力はfinal-build.sh/txt。旧依存追加は
MixedAncestryまでの5modulesとTerminal232の計6modulesのみでstrict build済み。
前回1600依存sourceのhash不変、今回のimport closureもhash記録。旧Leanは凍結、
barrel追記のみ。全体lake build/verify-lean/Yulang2は実行せず監督役担当とした。

途中の失敗ログは履歴として保全し、最終成功はCompleteAudit-final/Full-final/
final-buildで区別する。監査helperのprivate名解決を修正し、private/generatedを
含むFull監査も行った。新しい公理・禁止語なし。使用量枠は不明。

開始・10分・20分心拍を公開。実source反例により約17分で新実装を止め、その後は
監査・保全。停止条件が優先なので残り時間を部品追加で埋めない。最終公開head、
全tree照合時刻、ファイル数はpublication-receiptに記録。既存247/248 quarantineと
248/249 lockは未対象。cycle252成果の未公開残しや他writerとの競合はない。
