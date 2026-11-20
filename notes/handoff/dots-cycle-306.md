# cycle 306: 実状態の有限制御と、選んだ観測を保つ最小商

開始 2026-11-20 21:25:41 UTC（11-21 06:25:41 JST）。完了時刻と実所要時間は
同じ公開の完了心拍に記録。C305 完了
`a9b7b3aa5c93d4aa351e5afc7f5811b55ab9adb5` を確認。統合版
`079158c78d4dc46b0a8107e9f4927c7405052ca2` から standing orders・inbox を再読し、
ACTIVE / I51–I54 を適用。作業中に統合版が
`b7fcac3da0a905a5a745fa6e4acc5717f007107c` へ進んだ。指示2本は不変、
統合された既知の Lean 36モジュールを手元とバイト照合済み。barrel 追記以外の
既存 Lean 変更なし。公開先は `work/dots-main` のみ。

## 何が分かったか

二スカラー・深い出力の実プログラムは、raw 状態をそのまま数えると C305 の
無限分岐を持つ。しかし、このプログラムの**初期からの任意の実到達状態**を対象に、
次の手を正確に保つ有限商を構成できた。最小クラス数は何を観測として残すかで違う。

| 残す情報 | クラス数 | 区別の根拠 |
| --- | ---: | --- |
| ステップの名前を忘れ、実 raw の手だけ比較 | **5** | 最小の強双模倣。「二スカラーを同時更新」と「install・スカラーを別々に完了」は分ける |
| 実 raw の手と、どの assignment が全 Models に属するか | **6** | install 済みかと残りスカラー数。同じ診断でも install は代入を落とす |
| install / source 0 / source 1 それぞれの手の有無 | **8** | install 済みビット＋二つの Known。全8コードが実到達し、名前ごとの可否で互いに区別できる |

I54.1 の observer を solver の進行判定と混同しない。同じ有限 V8 入力で両相とも
`selected 0 []` を得るが、全 Models をその辞書の証拠で覆えるのは据え付け後だけ。
「残作業数が同じなら最短の raw 停止距離も同じ」は実到達状態上で反例がある。

## I54.1–2: 実 source への正確な制御・診断

- `GeneralMixedControlAtoms306.reach_facts` は任意の install 後 raw path に沿って、
  二つの source の scalar 方程式、source 初期化、記録済み cache の正当化を保つ。
  `GeneralMixedCheckedPromotion306.certify` は選んだ slot に対し型の正規化証拠と
  新観測の信頼証拠を別々に要求し、他の観測を保持する。
  `GeneralMixedControlBisim306.labelled / unlabelled` は任意の到達代表から、
  すべての有限 mask edge が実 strict refresh に戻ることを示す（同じ successor
  コードの存在であって、raw successor の同一性・列挙ではない）。
  install 後だけならラベル無しは残りスカラー数0/1/2の3クラスで最小。
- `GeneralMixedFullControlCode306.marker` は任意の初期到達 path で、packet の存在から
  実 phase を判定する。C286 の実 install 存在・pre/post 分割を再利用し、
  `GeneralMixedFullControlStep306.exact_labelled` は各任意の到達代表・event・目標コード
  に対して、有限判定が真 iff 同じコードの実後続がその event を持つことを証明。
  install はスカラーを変えず、refresh は phase を変えないが両スカラーを一度に
  観測できる。ラベルは strict refresh 証明の source。両方を初めて観測する edge
  には、根拠に選ぶ source によって二つのラベルがあり得る。
- `GeneralMixedFullControlTrace306.exact_checker / all_constructible` は任意の
  到達代表から任意の有限な event＋目標コード列を双方向に解釈し、8コードすべての
  実到達を証明。`GeneralMixedFullControlMinimalRaw306` では raw 到達状態を対象に
  任意の強双模倣が5分類を保ち、5分類自身も双模倣で、全クラスが実到達。
  `GeneralMixedFullControlModelClasses306` は全 Models まで保つ任意の双模倣が
  6分類を保ち、その逆も証明。`GeneralMixedFullControlDistinctions306` は具体的な
  到達代表を取り、モデル観測と停止コストを落とした商の二つの限界を示す。
- `GeneralMixedFullControlCost306.finishing_lengths`: 任意の初期到達状態から、
  丁度 `k` 回の実ステップで停止できる iff
  `未install (0/1) + スカラー残あり (0/1) ≤ k ≤ 未install (0/1) + 残スカラー数`。
  `fast/slow` は区間両端のコード列を作る。検査を通した任意の終端コード列を実停止へ
  lift し、選択・安定性・深い出力型と辞書証拠の条件を
  `GeneralMixedFullControlFinish306.compiled_route` が確認する。初期からなら
  最短2、最長3。これはこの実 source の結果で、一般 raw の長さ上界ではない。
- `GeneralMixedPreInstallSigns306.exact_on_any_prior_path` は任意の refresh のみの
  初期 prefix で実計画を移送し、固定2行の pass/reject 表が実装出力の存在・棄却に
  正確であることを証明する。任意の source の証拠行生成を仮定・解決したものではない。
  `GeneralMixedFullControlObserver306.exact_diagnostic / exact_evidence` はすべての
  pre/post 到達状態で有限 V8 から局所診断を正確に得て、同じ代入のモデル付き証拠
  が `FinalTypeCheck m ∧ payload = node 0 []` と同値であることを示す。

## I54.1 と 3: 汎用有限表、任意深さの既存実 ladder への適用

- `GeneralFiniteColoredExact306.exact_checked` は任意の有限な遷移閉リスト、decidable
  な色、任意のリスト内2点について、生成表の関係 iff その点を関係づける色保存強双模倣
  が存在することを証明。安定しない反復では保持された対の数が真に減るので、リストの
  対数以内に停止する。`GeneralFiniteColoredEarlyStop306.exact_fast` は実装の早期停止
  と全段を積む版が同じ入力について同じ保持ペアリストを返すこと。循環グラフでも正しく働く。
  `GeneralFiniteColoredQuotient306.exact_edges / projection_minimal` は代表を実際に
  生成し、任意の入力ノードから商 edge の双方向の lift と最粗性を証明。
- `GeneralFiniteColoredCertificate306.certificate_exact` は提出された射影が
  遷移閉域で色保存強双模倣になるかの実行可能な検査。二スカラー例で、残義務数だけの
  射影と不完全な域を拒否。観測無しなら5、phase 色を残せば6を**同じ汎用実装で計算**し、
  実 raw 状態で手作業の最小商と一致する。`GeneralFiniteRawPresentation306` により、
  生状態が無限に分岐してもよいが、**到達部分の閉性・色一致・全代表からすべての射影
  edge を lift する実証明が別途必要**である。
- `GeneralLadderCompiledMinimal306.exact_count / countdown_edges`: 任意の深さ
  `n` の C304 実 deferred-ladder、全 raw 到達点について、上の一般実装が
  `n+3` 個の最小ラベル無しクラスを生成。辺の**集合**は残り回数を1ずつ減らす
  （リストには同じ射影先が重複し得る）。`GeneralLadderCompiledRun306.compiled_terminal`
  は任意の到達 prefix から、代表コードで計算した残り手順を実 raw 経路へ戻し、
  全長 `n+2`、必要な fuel で得られる深い辞書、および全端点モデルに対する
  既存の正確な辞書証拠に接続する。この例では色を保たない商。一般の EvidenceNode を
  置換したものではない。

## 検証・公開・残件

- Lean 4.35.0。新規40モジュール、全追加は `lean/Yulang.lean` に同じ公開で一度ずつ
  import。既存 Lean の削除・差替えなし。spec・plan・lake 設定変更なし。
- 対象を指定した `lake build --wfail` の成功ログを `notes/verification/cycle306/`
  に保存。単独監査7本・98宣言を一つずつ `lake env lean --trust=0
  -DwarningAsError=true Audit/Cycle306…lean` で再実行。標準公理
  `propext` / `Classical.choice` / `Quot.sound` のみ。核で評価した小例も含む。
- `tools/verify-lean.sh <checkout> 2c105891b --no-build` の出力全文は
  `diff-verify-*.txt`。差分 PASS。別の純 Lean 実行テストでは深さ 0,1,2,3,5,8,16
  で 3,4,5,6,8,11,19 クラス、二スカラーで 5/6、初期 schedule は2/3手。
  全体 Lake・既存監査全部・CI・Rust は未実行。
- 実成果 pin `2e476c8494adcf6907c1cefb0667bb36a63d4b22`。途中 pin
  `62b7cce1ecf5bc155bfd0ac3dcc0cbecd87c354a`、
  `14020746a246a2a50274166822c1126afe4b3e16`、
  `954f7de40a20c834bbd861af417c99e60a32c181`。実成果64パスをまとめて exact readback
  （既存 barrel の末尾に40行だけ追加）。開始と10/20/30/40/50分の心拍、最後に
  完了心拍とこの報告を expected-head / non-force で公開。今周の変更は重複を除いて
  心拍込み74パス。詳細は検証 summary。
- Lean 初回依存が冷えた箇所、局所型エラー、一時的な作業接続切れは再開・再検証済み。
  不明な利用枠以外の制約なし。新しい意味論判断や Rust 要求は不要、質問ノートなし。

次は実 source の任意の候補について、棄却割当てと独立した history/class slice を有限
射影へ落とし、色だけでなく全代表からの successor-lift 証拠を構成する。候補の一つは C238
`GeneralDictionaryCompoundStep238`（明示出力と一つの実 child を持つ）。二つの child を
持つ `GeneralDictionaryOutputMergeSuccess` は現状古い境界の例なので、後継 raw
境界への移送を証明してから回帰に使う。一般の有限 raw presentation の存在、全 raw
停止性、無条件の B4 主定理はいずれも未証明。
