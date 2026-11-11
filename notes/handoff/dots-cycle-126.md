# Cycle126: checked declarations to computed whole dictionary recipes

**一般sourceのB4Bridges V3: 未証明（未充填）12 / 全12。一般B4は未完成。**

開始は2026-11-11T21:27:19Z。最新ユーザー指示により、検証・途中成果公開・報告・writer解放を
含む期限を22:22:19UTCに固定した。終了と全tree照合の時刻、所要時間はcompleted heartbeatに
記録する。終了理由はI-15(a): 約50分の枠で実装・複数checkpoint・検証・報告まで収めるため。
文書中の「55分まで実装を続ける」より、全作業を55分以内に終える最新指示を優先した。

## 復元、最新指示、担当範囲

- 開始時integration/work headは`2fc64bb6e4b67958dd75e84d85f0eed472938c62`。
  cycle125のcompleted heartbeatと公開済み報告から復元し、前writerの解放を確認した。
  既存workspaceとLean cacheを継続利用した。crash復旧・source喪失・並行writerはない。
- standing orders、inbox、前報告を再読。開始時inboxはACTIVE、hash
  `2631f8a557ab1a3b3551556a3f516746e3e8fa65`。I-19のV3修正は既に検証済み。
- 21:56頃の再取得でintegrationが`2129088d05e1e77a1f4d14031914aa582fe41da2`、
  inboxが`653af61b4f1c9b2d97cca093030c41d7c68beac3`へ更新されたため取り込んだ。
  最終sourceはこのintegrationを親として含む。22:03頃の再取得でもACTIVE・同hash。
- 新しい補遺4では、すべての無名引数の下界headが既知になるまで解決を待つ。
  変数だけの候補位置も「不要」として外さない。今回のterm materializationは解決器や
  candidate inspectionではなく、このpending guardを省略する道ではない。
- Astraは項目1・2・3を担当。dotはI-18項目5の辞書Evidence/Reordersだけを進めた。
  宣言・状態・候補の既存定義、spec、plan、lake設定を変更していない。

## 閉じた部分目標と時間

各時間は実作業の概算区間。検証と例の作成が重なるため合計はelapsedと一致しない。

1. **同じ実checked visible宣言からoutputとcanonical子を計算、21:28–21:38頃。**
   source occurrence、選択key、root role、frameを一つのlookupで結び、cycle125の実RHS
   binder compilerを使う。headだけを独立の残存predicateに分離した。成功した各nodeから
   全childを含むTransactions.Validと、同じ宣言のSourceInstanceを構成する。
   24定理・539 jobsを検証し第一checkpointへ公開した。
2. **output-only有限木の限界を一般に証明、21:37–21:40頃。**
   任意checked宣言でoutput-only binderの出力には非空outputを持つproducer childが必要。
   任意有限Built木の根のoutputは空でなければならない。この障害を隠さず、既存のProducedや
   child完全性を弱めなかった。これは旧部分interpreterの限界で、言語全体の拒否ではない。
3. **終端を作れる実input変数RHS、21:39–21:51頃。**
   正規化した明示RHSがinput変数で、captureの上下端が同じsource IDの場合だけordinary
   source変数へ変換する。区間中心を任意に選ばない。旧output binder成功を同じ結果で保存し、
   独立Materializesとのiff、fixed入力での可視宣言/where順序不変を証明した。
   本物のchecked二node例は、rootの別々のtarget3/4からproducer2を通ってterminal input0へ
   接続する。共同ordinary modelを一つ構成し、その全modelで出力の同値を証明した。
   81定理・547 jobsを検証し、開始25.53分で第二checkpointの全treeを照合した。
4. **手渡しoutputのない全tree準備、21:49–21:57頃。**
   Recipeはoccurrence/key/Inputs/子Recipeだけを持ち、output vectorを持たない。
   prepareが各nodeのoutputを計算し、再帰成功した子の完全なoccurrence列とcanonical列を
   照合する。欠落・余分・同じdemandでも異なるidentityの子は全体deferとなる。
   成功とheadだけの再帰証明からBuiltおよび全model共通の固定辞書witnessを得る。
   focused541 jobs、実行結果`[true, false, false, false, false]`を確認した。
5. **capture実現とactual variable head、21:56–22:02頃。**
   Realizesを「input値が捕捉区間内、output値が捕捉sourceと同値」と独立定義し、任意の
   その実現でactual variable RHSと計算termが一致することを示した。HeadlessInputsには
   headもoutputも入れず、実宣言の各headが正規化変数で捕捉上下端のsourceが等しい場合に
   head vectorを計算する。独立HeadDenotesとのexactnessとterminal例の成功、nominal rootの
   deferを証明した。whole Recipeとの自動合成はまだ残る。
6. **最終検証・公開・全報告、22:02以降。** 17新moduleと109公開定理の全件監査、
   source全tree照合、hosted CIのexact checkout照合、全量化子・13項目台帳を含む報告を行う。

## 量化子、効く側、受け入れ条件

[全109定理の日本語命題と正確な型](dots-cycle-126-theorems.md)に、暗黙parameterを
含む`#check @`出力と各公理監査を記載した。健全性31・完全性10・補助68という分類は
この部分実装内の分類であり、B4の109フィールドを閉じたという意味ではない。

- **同一宣言の辞書生成（健全性）。** 任意checked registry、state、各occurrenceのframe、
  head-only predicate、有限木について、実lookup成功と再帰的head証明から、実生成された
  全子を持つ辞書と同一宣言のRHS解釈を得る。一つのrecorded batchについて、一つの固定
  source witnessがそのbatchを満たすすべての最終modelで正しい。一般のmodel存在は結論しない。
- **部分materialization（限定的完全性）。** 関連型名が重複しない任意実宣言、capture、state、Inputsとlocatedに
  対し、独立Materializesとbuild成功のiff。registry lookupも同じvisible key/role/子を
  持つ宣言と独立materializationの存在に対応する。unsupported宣言を完備に扱う意味ではない。
- **順序（補助）。** registryとwhereの許された並べ替えの下、同じframe、capture、state、
  key、inputsを固定するとbuild/lookupの返す全packageが同じ。candidate探索順や最終stateの
  不変性ではない。全ての失敗結果についても同じ部分lookupの結果を保存する。
- **capture意味（健全性）。** 任意model、任意そのcaptureをRealizesする変数値について、
  計算source termはactual normalized variable RHS値と同値。Realizesそのものをhead照合から
  導いたとは主張しない。inputは上下端が同じsource IDの場合だけ実装する。
- **head（限定的完全性と健全性）。** 任意checked宣言とrole一致、capture、headless位置に
  対し、成功builderは実positional headの独立変数解釈を満たし、入力の上下端とtargetsを保存。
  compound/nominal headは返さない。候補の適用性やcaptureの生成を証明したものではない。
- **有限例（補助）。** 実checked leafとrootのordinary equationsに共同modelがあり、全modelで
  targetがつながる。rootの供給head `.var 0` はnominal binderWrap headから導かれていない。
  したがって、この例だけで完全な言語role modelやend-to-end解決成功を主張しない。

I-18項目5のEvidenceの実RHS側、Reordersのfixed-input側、辞書全体の計算入力を縮めた。
新しい断片Classifyは作っていない。一般SourceBoundaryやB4Bridgesへの代入は未完了。

## SourceBoundary 全13項目

| Field | 現在の状態 | 残り |
| --- | --- | --- |
| Checked | 一般certificate定義あり | 完全checkerとconstructor/Common対応。Astra項目1。 |
| Models | 一般shared-state定義あり | 完全な宣言/role modelではない。 |
| Step | MISSING | 一般状態更新・需要の再生成。 |
| Stable | MISSING | EOFを含む兄弟fixpoint。 |
| Generated | 一般emission/Plan/lookup部品あり | 実candidate frame/freshness。Recipeは全canonical子を検査するが一般生成driverではない。 |
| RootPending | 一般partial snapshot定義あり | 最新補遺4のallUnnamed Neededが意図。実lower-head観察との一般接続。 |
| RootK2 | 一般partial normalized定義あり | 実source正規化との対応。 |
| CandidateK2 | MISSING | 実candidate inspection。Astra項目3。 |
| InspectionPending | 実source fieldはMISSING | V3 schemaは対応済み、実predicateなし。Astra項目3。 |
| Survivor | MISSING | computed planは候補選択ではない。Astra項目3。 |
| Evidence | full role fieldはMISSING | actual variable RHS、有限computed transactions、capture実現を接続。一般head/capture/選択/default/compound/nominalが未接続。 |
| Reorders | 一般構造定義あり | fixed入力の部分compilerの全package不変を追加。最終state/candidate順序との対応なし。 |
| DictionaryEquivalent | 一般source/payload構造定義あり | full boundaryの観察意味との接続。 |

## 検証と公開

- 最終focused build: **553 jobs、exit0**。17moduleすべてを明示した。
- 最終scoped trust-zero audit: **109 public theorem、exit0**。名前集合がソースと完全一致し、
  許可されたpropext/Classical.choice/Quot.sound以外は0。Auditへの登録も全件確認。
- prepare、variable head build、output buildのruntime定義3件も監査し、許可外公理0。
- 全signature出力、diff-only gate、git diff --checkはexit0。
- [実行コマンドと出力全文](dots-cycle-126-verification.md)。修正前の証明エラー、未commit
  状態によるgate失敗、signature出力の未知pp.width optionは成功に数えていない。
- local full lake build、local full Audit、監督役の独立AxiomGateは実行していない。

第一source: [d8892fd9bed56ec6330170ae7e05ab5c5696bca1](https://github.com/momota1029/yulang/commit/d8892fd9bed56ec6330170ae7e05ab5c5696bca1)。
21:38頃公開、**2418 tracked files全tree一致**。exact commitのhosted core/proof成功、
runner checkout一致、full build1381 jobs、今回の24定理がfull Auditへ出ることを確認した。

第二source: [22b5de4e84852c0ac5f54903c36455d200dcc383](https://github.com/momota1029/yulang/commit/22b5de4e84852c0ac5f54903c36455d200dcc383)。
21:52:51照合、**2427 tracked files全tree一致**。hosted core/proof成功、checkout一致、
full build1390 jobs、今回の81定理の出力と許可外公理0を確認した。

最終source: [cb899edd91b7d414202886b2c1b9c6e3095dceec](https://github.com/momota1029/yulang/commit/cb899edd91b7d414202886b2c1b9c6e3095dceec)。
tree `d4720a64140f622716de5b55276f5296c1b72f0f`。
**2432 tracked filesを全件read backしlocalと一致、truncated=false**。最終sourceのhosted
検証は下の追記へ記録する。integration2129088dを追加親に持ち、その上の変更はheartbeat込み
23path（17新module、Lean集約/README3、design/INDEX2、heartbeat1）。報告3つを含め最終26path。
非force・expected-headのGit APIでwork/dots-mainだけへ公開し、Git blobとtreeのhashを照合した。

## 制限、Yulang2照合、次の部分目標

未対応の場合は全packageをdeferし、言語の拒否・不可能性と混同しない。capture、allocation、
location、選択key、有限tree形状は引き続き入力である。headless builderはまだregistry/Recipeへ
合成していない。head適用性、shared stateのjoint feasibility、一般model存在は別の義務。

Yulang2の`work/dots-audit`にある`y2-claims-role-boundaries-cycle-2.md`を再取得した
（hash `9d17b670c28c04fcc74ba2476a7832d999bdbbf1`）。ROLE-MORE-001〜008と実装経路を
読んだ。旧advertised-whereを新specの候補前提へ輸入していない。正本はspec06 §6.3の
普通の型変数と等式、output-onlyのユーザー決定。新しいYulang2実機試験は実施していない。

新質問ノートは0件。未指定のinterval中心、nominal符号化、default意味を独断で選ばなかった。
quotaは不明。開始時と終了前の空き容量はともに38GiB。cacheの複製・古いcache削除はない。
21:56の心拍でinbox hashを一時的に旧値のまま記載したが、読取と取り込みは新値で行い、
次の心拍で訂正した。実行中の検証・未公開source・不確実なref更新を残さずwriterを解放する。

次の最初の部分目標:
1. **HeadlessInputsを実registry lookupとRecipeへ合成する。** 同じ実visible宣言からheadと
   outputを計算し、whole-tree側の手渡しheadを対応範囲で除く。compound/nominalはdeferを維持。
2. **実captureのRealizesを、Astraのcandidate結果から受ける境界を接続する。** 項目3自体には
   手を出さず、返されるcapture/role一致/全無名引数の既知headの前提を明示してEvidenceへ渡す。
3. **辞書順序不変をcomputed whole Recipeへ上げる。** fixed-input局所package等式から、
   同じ完全child構造の生成辞書・recorded batch・観察同値までつなぐ。最終state独立と区別する。

## 最終sourceのhosted検証（22:08UTC確認）

exact source `cb899edd91b7d414202886b2c1b9c6e3095dceec`について:
- [core](https://github.com/momota1029/yulang/actions/runs/43108794096/job/130819016760): success。
- [proof](https://github.com/momota1029/yulang/actions/runs/43108794068/job/130819016872): success。
- runnerのcheckout SHA一致、**full build1395 jobs**、full Auditの8550公理依存出力、
  今回の109定理がすべて出力されたことを確認した。timestampを除去して複数行の公理一覧を
  連結した結果、propext/Classical.choice/Quot.sound以外は0。
- hostedでの検証結果であり、localで全体検証や監督役AxiomGateを実施した意味ではない。
- これ以後の変更は報告3つとheartbeatだけ。報告treeの再取得・全件照合・完了時刻は
  completed heartbeatに記録する。
