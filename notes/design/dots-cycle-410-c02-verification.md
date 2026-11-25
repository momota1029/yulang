# C410: C02 / X8 の判定と独立した根の切断証拠

spec/06-roles.md §6.5（不変の `list`）と K2（X8）。追加規則は、元の同じ一引数が実 nominal point、head の子が一つの plain variable、空 where/出力で、元 role・宣言が実在し、可視候補が singleton の場合。この宣言の検査は C357 の実 source mode を使う。endpoint の一段目から得る同じ payload の点を、同じ選択イベントの変数に捕捉する。型のモデル値や期待したレポートから入力の名を選ばない。plain variable に構造 visit は無いので、その payload の循環を理由に拒否しない。literal `where Show 'a` で子の根まで降りる X9 はこの行の対象外。

## 実行 witness と同じ raw graph

初期の単一色 checker は、書かれた全 RHS の名前と色の単調性から十分条件を得る。その後、本番の `checkExactEscape` では色と alias 用の順位を分けた。順位は ordinary Bound と flat alias の一致を検査するためだけ。構造辺は、その式を実際に `shapeOf` が解釈した children だけを見る。候補の可否や未完の由来で Graph を剪定しない。実際の alias は同じ色、根側の 0 から構造辺を一度渡ると色 1、以後は色 1 から出ない。従って本来の根 alias へ帰れないが、色 1 内では循環できる。片方向 Bound を即 alias にせず、decoder が構造辺を認めない join からも仮の辺を足さない。有限証人を探す solver や一般完全性は証明していない。

## X8 のモデルと対照

resolved B4 入力は根 0 の `list(ν)` と、1 で自己に戻る raw `ν = :tag ν`。実際の構造辺 0→1、payload 根自身の raw K2、全グラフ rank による証明不可能をそれぞれ確認。にもかかわらず C02 は true。型の全有限深さで `ν` とその一段展開が同じとなる正則モデルを作り、この **同じ循環 snapshot** の `Fits` と元の選択辞書を得た。別の型で循環を消した非循環の control ではない。alias で 1→0 の帰路を加えると新 branch は false、以前の raw K2 証人を使う分岐は true。誤った報告、元 origin ordinal、色も false。片方向 Bound と未解釈 join の対照では初期の十分条件は false だが本番は true。これは raw 観測・論理入力の検証で、Yulang Rust パーサや全言語の実行検証ではない。

## 変更しない証明

`List410.R2 = R1 ∪ listLocal410`。元の局所 veto/曖昧を広げたり飛ばしたりせず、固定 `DictionaryEvidence` を保つ `dictionary_sound_R2`。`List410.check` は前分岐をそのまま呼び、追加分岐の witness は origin 番号・順位列・色パレットだけ。`check_sound` は同じ Problem と exact Report に対し、同じ State の任意の fitting model で元辞書・書込み順を維持する。前枝との同時受理なし／任意の成功証人間で結果が一意も検証。今回の範囲外は false、追加の言語判断はない。
