# C468 / I-91: G04 の未発行座標は誰の仕事か

**結論・勧告。** G04 はまだ閉じない。いまの「既発行 native Write を読める」を最終前提にすると、関連出力を一度も要求しなくても起きる仕様の inline/bound の field 検査が落ちる。G04 には、**候補の照合時点の同一入力から、実際に訪れる非変数位置を source 由来または既完了出力由来として raw 座標に照合する**役割を残す。別需要が関連出力を完了して後続に開けるようにする発行は G18 に置く。前者をすべて後者の Native360 board 発行で代用しない。前者の未命名の座標には下記 (b) の表現の判断が要るので、これを監督に送って Lean を増やさない。採用・範囲の変更はまだ行わない。

## 1. 仕様が定める責任と時点

根拠は正本 `yulang3@fd8ca48129d94bc47a121f99cb3c87f86e474ccc` の `spec/06-roles.md`（blob `16da40eb041bf38daa9d8b2acb7ea0ddf22d907e`）、統合の同節 blob `2732b1d76476e382489803943a9f44fa18aef544` と照合。正本の行番号を下に使う。§4 の record/variant の既存 shadow/merge の意味を変えない。

| 時点・責任主体 | 許されるもの／許されないもの |
|---|---|
| 普通の型付け・ソース制約からの入力 provenance | §6.3 L157–197 は、候補を調べる入力の頭を支える独立根拠として**ソースの制約または片付いた需要の出力**を挙げる。前者に associated output や Native360 発行は要らない。照合用の座標をまだ持たない場合、既存の source/捕捉から**観測の表現**を作る仕事は現在の候補の入力側。候補の書いた型だけ・たまたま同じモデル値・まだ片付いていない出力からは、今認めたことにできない。 |
| 消費側の単一需要、実 head 照合中・選択前 | K2 L491–505、特に L497–502。根の既存 raw K2 と、実際に非変数 pattern が constructor を調べる field の K2 を区別。変数捕捉だけでは開かない。nominal は経路上の実引数のみ、body を開かない。§6.5 L385–412 の中心は共有用であり、中心を発行したことにして端点の訪問に置き換えない。§6.3 L213–226 の未完出力の等式による**根**の K2 は保留に隠さず、しかし新しく候補内を開く根拠にも使わない。 |
| 選択された**別**の生産側の関連出力と完了 | §6.3 L88–95/L238–249。選択で元の名前つき出力の既出固定先に等式を加える（上書きしない）。宣言があるだけ・候補を調べているだけで発行しない。L157–197 の「片付いた」は where の子まで。型の頭を後続へ公開する根拠は、この完了を要する。未完の等式も ordinary・合流・raw K2 には残る。Lean の board/grant/stamp は実装の証拠であり、仕様はそれを唯一の発行機構とは言わない。 |
| 宣言の受理（GD） | §6.3 L98–116 の `StableSmaller` 等を宣言ごとに一度準備する。要求発生前なので、この要求の発生位置・raw ordinal・実 captured target・関連出力の grant は作らない。G04 は既検査表を読む。 |

例は正本 L498 の `impl Check {box: {tick: 'a}} where Check {box: 'a}` に `Check {box: μ}`、`μ = {tick: μ}`（型の略記）。入力の実 field の constructor を調べる時点で拒否する。関連出力のない要求でもこの判断は必要で、GD 時や選択後の別需要の発行を待つ規則ではない。一方 `impl Check {box: 'a}` はその field の μ を捕まえるだけで、それを開いた K2 と報告しない。仕様上の対照であり、新規 Yulang2 実行結果ではない（既存 audit x-oracle X10/X11 は record head のこの到達を確立していない）。

## 2. 何が無いか

| 区分 | 無いもの・現物にあるもの |
|---|---|
| **(a) 既存定義上の証明** | 既に source/physical owner/route と同相の raw 名がある枝の一般化。C460/C463 の全 carrier 文法と元 path・実 raw ordinal、C458 の有限 trail / cycle、C464 の同じ元 issuer を保つ supplied projection、C465 の pinned same-hop / exact release は利用可能。単一 visible と GD のもと、同一の独立入力判断→同じ report の有限 wire と全 `FitsFull` 健全性を結ぶ残り。以前発行した output に限定すれば C467 の実 C361 read は既存 address を保持するが、現在の全 G04 局所規則にはならない。 |
| **(b) 入力側の表現** | 未命名の inline/bound 位置で、現在の元 occurrence・実宣言/引数・元構文位置と consumer が実際に読んだ入力構成子の元根拠・選ばれた子座標・同一 raw phase を結ぶ有限 event/receipt がない。I65 `Origin` は slot/issuer/endpoint、`OriginRoute` は direct または**既存** route。C458 `OriginalInlineField` は既に parent/payload 二つの `.ordinary` を同じ issuer の保持行として表し、両実 route、raw 子と payload の Alias、選んだ field の一致を検証する。したがって (b) は `.ordinary` が書けないことではなく、その二行（または同等な入力 provenance）を元の実 compiler event と同相に結ぶ生成・検証用の証拠の形。現在の C458 reader は Native360 board を前提にはしていない。既存 ledger だけから作成経緯や完全な stamp を復元しない。C444 の `FullState.retained` は主として元関連出力の保持等式であり head 観測 event ではない。既存 compiler が生成した全 Model で整合する ordinary 座標から native 側が自動で生まれる定理ではない。 |
| **(b) raw 観測との接続** | C466 の実 C332 が raw3/target7 の `ordinary` 行を追加して真正な旧 `Supported` を得る例でも inline owner の `shapeOf` は none。独立に渡した安全な named raw 投影で shape を得ても、既存 native route は生じない。C467 ではその同じ authored capture/spans が C360 の実 prepare に入るが、prepared ordinary は相違（旧モデルを延長できることは同相でない）、当該要求には関連出力がなく `compile` は全 witness で none。逆に既存 board が同じ・全モデルで真の ordinary 等式でも、raw 表現を書き増して元の K2 が不変とは言えない（C464 checked cut の存在/不在を比較）。従って未命名箇所の source→raw 接続を単に「既存 `shapeOf` 成功」や Model の値等式で証明し直せない。 |
| **(c) 他行との境界** | 既完了の別需要からの typed output の正確な release・version・owner と後続 authorization は **G18**（必要な保持は G00/G11、親子の伝播は G16）。選択後の元 where 子生成は G15、未完のみの支持保留は G17、需要合流・整合は G19/G03b。G04 には G18 全行閉鎖は前提にせず、既発行枝では独立証明つき局所接口を読む。GD は事前検査表。候補全体 G05/G10、残余 join G08、tail G06/G07、一般 nominal mode/kind/arity G20/G21 は既に別。このノートで新しい行を足したり行を閉じたりしない。 |

## 3. 監督に承認を求める最小境界

暫定名 `InputInspectionOrigin` を **既存の nominal native 出力 ledger と区別した、compiler 相に結び付いた入力側の資料**として設計することを勧める。まず既存 records/relations の組で持てるか再確認し、不足する場合だけ別の証拠入力を足す（ここでは FullState 編集・導入はしない）。

- 独立判断は元 occurrence、可視宣言と全元 ordinal、head 引数、original/normalized path、選んだ既存元制約と正確な provenance、同相の raw query/owner/child と出所を結ぶ。出所は「ソース制約からの constructor 観測」と「既に release 済みの完了出力」の和。前者に架空の Write・version・grant を要求しない。後者では完全な board address と完了の由来を G18 の資料で照合する。源の issue とは無関係な lexically 等しい path などは代用しない。
- exact 指標のある実命名が利用できればそれを使う。未命名の場合の projection/導出を有限にする設計は監督承認待ち。新物理名を足すか旧 source 側の occurrence を参照するか、どの compiler event がその根拠を所有するかはこのノートでは決めない。別 snapshot を作るなら、追加の等式・実 raw 観測・それ以前の位置の対応を個別に証明し、従来の `FitsFull`、source と K2 をひとまとめに「同じ」としない。すべての新しい本物の循環を不変にせよという要求でもない。
- 合格基準: 元の出力なし inline source から実 field 到達の exact report と有限 wire、同じ `FitsFull` の全モデルで健全。未訪問の sibling・違う原位置/物理順位、前の相のみで正しい出力/旧 version、未完出力だけ、metadata のみで該当 raw alias なし、を個別に区別。既発行枝の成功はそれ自体、出力なしの source-only 枝の成功でない。
- **既発行のみの縮小案は採らない。** GC/gate の退避ではなく source-only の実例を失うため。仮に監督が細分化するなら、G18 への移動は別需要の typed output 発行に限る。未命名の普通入力の正確な source-to-raw 検査は追跡される未完行として残す。G04 は現カウントの未完、24 行中残り 20。Lean・spec・canonical checker は変更しない。
