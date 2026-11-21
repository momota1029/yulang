# C311: 別発生点の peer に、記録済み選択を移す条件

開始 2026-11-21 02:30 UTC / 11:30 JST。前回完了
`dc299f9c74b87687dc075612dec1f83b2cfcb780`。開始時に
integration `5df350afcf817a22337ffae5d5409eef5dd85c52` の standing orders と inbox
を再読し、I-55 の型推論健全性を優先。停止性には取り組まない。
作業中の integration `9e1ac23910ea8f3866c4d5714eb4479ec5ae3de4` でも
二文書の blob が同じであり、適用順に変更がないことを照合した。

## 実 source で先に install できる経路

- checked root は `List[List[Int]], List[Int]` に対する二入力パターンを照合し、
  独立に `U=List[Int]` と `T=Int` を捕捉する。最初の実 install により、
  直接の `Receiver(Int, item=z)` と中継の `Route(List[Int])` を生成する。
  `z` は名前付き出力の要求先であって、通常入力の一部ではない。
  `GeneralLatePeerRoot311`、`GeneralLatePeerFirst311.step / models`。
- 直接の receiver を先に実 install できる。公開入力を一切変えず `z=Bool`
  とした妥当モデルが、この install の前には存在し、後で除外される。
  任意の同じモデルについて「前の Models かつ `z ≃ Int`」が後の Models と同値。
  `GeneralLatePeerDirectInstall311.step / models / bad_before`。
- 続いて Route を実 install すると、直接 receiver とは別発生点で同じ
  `Int` を受け取る peer を実生成する。peer にローカルの出力要求はない。
  Route install 自体はモデルを減らさない。`GeneralLatePeerRouteInstall311.step /
  reached_emitted / peer_list / models`。逆順で同入力の未 alias peer が
  既に登録済みなら先の install はできない
  (`GeneralPeerInstallationOrder311.no_install_before_join`)。

- 次の実 merge は old receiver とこの後発 peer を alias にする。peer に
  `item=z` が class request として継承され、既に記録した receiver の式
  `z ≃ Int` が全妥当モデルに残る。新たな output equality atom は追加されず、
  merge 前後の全 Models は双方向に同値。
  `GeneralLatePeerMerge311.step / reached / inherited / models`。

- 後発 peer に自分自身の記録済み plan はなく、現 peer への ordinary replay
  は存在しない。それでも class に旧 packet が実在し、実 alias の先にある
  旧 key は現在の選択と互換になる。この互換性には下の一般移送を使い、
  role に候補が一つしかないことによる互換の近道は使っていない。
  `GeneralLatePeerTransfer311.actual_peer / genuinely_not_replay / nontrivial`。
- peer は実 `Local selected(2,[])`。中継 Route も実選択済みで、宣言的
  `Classify` は非空の辞書 `3[2]`。任意の最終妥当モデルで Route と peer の
  Evidence を同じモデルで構築した。モデルの実在も示した。
  `GeneralLatePeerCurrent311.picked / leaf_evidence`、
  `GeneralLatePeerRecursive311.actual_recursive`。
- peer にはローカル要求がないので、継承した `item=z` のローカル要求代表を
  前提とする C310 の削減を適用できない。ここでは現出力式の実評価・既記録の
  `z ≃ Int` から、任意の**同じ**妥当モデルで据え付けの意味条件を満たす。
  (4a) も合わせて actual Installable に至る。これは merge 後に新たな install が
  実行されたという主張ではない。`GeneralLatePeerJoint311.not_locally_represented /
  jointly / enabled`。

## 一般の (4a) に使える Lean の削減

`GeneralVersionedPeerChoice311.prepared_at_peer / choice` は、異なる発生点に
古い Prepared を移すのに発生点の同一性や先験的な候補 key の一致を要求しない。
過去の owner と普通拡張を検証し、通常入力の**観測 bounds の一致**、両発生点の
独立な fresh allocation、同じ型モデルでの head 解釈の移送を示す。使う名前ごとに
捕捉元がちょうど一つなら、集約式は空なので最後の head 互換条件は自動的に成り立つ
(`linear_head_iff`)。一般の複数捕捉を、単に型が同値だから同じ bounds とみなさない。
過去の候補と現在の候補の key はこの移送の結果として一致し、仮定ではない。

さらに `GeneralVersionedAggregatePeer311.prepared_at_fresh_peer / choice` は、
複数捕捉を許す。同じ read bounds から旧モデルの raw/cross/self-check/射影を取り出し、
新発生点で**現在 raw に未出現**の集約名だけを実現し直す。そこ以外の raw
source に代入は触れない。通常の Fresh に加え、集約名が raw pool にないことが
条件で、予約鍵が未割り当てなら `apart_of_unallocated` で導ける。この補強は存在型の
Prepared に使うものであり、補正後の代入が journal 全体の `Models` だとは
主張しない。同一全モデルで証明すべき (4b) と分離した。

## I-55: 最終定理に残る橋

- **(4) 一般の辞書健全性: 2 本。** (4a) 任意の受理 alias と本当に観測が変わった
  refresh について、旧鍵と現鍵の互換を導く。今回、同じ bounds・確認済み Fresh・未出現の
  私的集約名を持つ複数捕捉に進んだが、一般 alias にこれらを導く補題と、既に現 pool にある集約名の
  分岐は残る。(4b) 現候補の
  materialization、順序付き子、現在 class/output の式を個別の存在証人でなく
  一つの妥当モデルで満たす。今回はローカル代表なしの継承要求の実一例も閉じたが、
  全称の未収載選択についての橋は残る。
- **(2) 停止して返った場合の部分正当性: 2 本。** (2a) 現 Frame、alias、履歴を
  読んで任意の実 endpoint の Local 行と対応する observer/compiler。(2b) 実 Sat の
  成功返却に対して、実 Step 路・その地点での停止証拠・返した診断木の照合を揃える。
  成功返却を仮定し、停止保証そのものは対象外。今周期は (4a) を優先し、(2) に
  新たな一般橋は追加していない。

本数は未証明のインターフェース群であり、補題数の見積もりではない。
[前回の入出力と定義の一覧](../design/2026-11-21-cycle310-dictionary-soundness-bridges.md)。
Rust、CI は未実行。全 Lean build の成功は主張しない。

[次の証明対象と実例の擬似ソース](../design/2026-11-21-cycle311-late-peer-choice.md)。

## 検証の条件

- 機械検証は実際に変更した 19 モジュールに限定した。各 source を
  `lake env lean --trust=0 -DwarningAsError=true` に個別に通し、監査も独立に実行。
  Barrel は追加モジュール分の末尾 import のみ。既存の証明・仕様・lake 設定は未変更。
- merge の試作で大きな definitional equality の elaboration が時間・メモリ制約に
  当たったため、観測列・role 同値を独立に証明してから適用する形に分割した。
  検証コマンドのリスト生成を一度訂正し、空引数で始まった default build は直ちに中断。
  以降は明示した差分対象だけをビルドした。全体の build/audit は未検証。
- 質問ノートは不要（受理範囲は変更なし）。使用枠の残量は不明。開始・終了・所要時間は
  完了心拍も参照。この周期の手法上の候補を上記 design ノートに三点記した。

19 モジュールの focused Lake build、19 source の trust=0、10 回の独立監査、
差分ゲートはすべて PASS。明示的な public 宣言 302 個を監査し、重点項目の
再掲を合わせて 340 件、非標準公理 0 件。
完了版の変更は 49 ファイル（心拍を除く）。
[コマンドと結果](../verification/cycle311/verification.md)、[追加全体の公理出力先頭](../verification/cycle311/axioms-00.txt)、[全差分ゲート出力先頭](../verification/cycle311/diff-00.txt)。
