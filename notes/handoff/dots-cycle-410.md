この周に閉じた C の行: C02 / X8「`Len (list 'a)` が再帰 payload を展開せず `len [loop 1]` に当たる」（`dictionary_sound_R2`, `List410.check_sound`、work/dots-main で三条件を検証）。

## 対象と出発点

- I-74 inbox `b99a214965f1e236ab62e6cffa13b77b617543cb`。I-65 の三定理は前周までに integration に掲載済み。前周 C01 の完了報告と心拍を確認し、integration `a6a88060218fe5b53340c9c705a6719bdb900fce` の C409 新規 5 ソース・3 独立 Audit・barrel の 9 パスが、先の検証済み blob と全て一致することを確認した。I-74 の [今回の一覧](../design/dots-cycle-410-c-coverage.md) は C02 だけを完了にした。
- spec/06-roles.md §6.5（再帰的な `list` は invariant）と K2 の X8 を対象にした。単一の実 authored role、singleton の可視宣言、同じ元の点入力を持つ一引数、literal 一変数の payload、空 where/出力。型の既知の名前と捕捉だけを読む範囲。一般の interval、複数候補、row 引数、実 where 子まで完了とはしない。

## 規則・検査器・健全性

1. [listLocal410](https://github.com/momota1029/yulang/blob/946e899804616347f41fc361a876253e73e5ff3f/lean/Yulang/GeneralDeclarativeI65I74InvariantList410.lean#L137) は、同じ元の宣言・mode・point input から本来の literal な捕捉を作る独立規則。モデルや checker の成功を前提にしない。これだけを `R1` に足した `R2` について、任意の State・要求・辞書で `Classifies R2 s q (.selected d)` なら任意の同じ fitting model で固定 `DictionaryEvidence s m q d`（[dictionary_sound_R2](https://github.com/momota1029/yulang/blob/946e899804616347f41fc361a876253e73e5ff3f/lean/Yulang/GeneralDeclarativeI65I74InvariantList410.lean#L158)）。plain binder が実構造 visit を作らないことと、既存の候補 K2・曖昧さの枝を隠さないことを示した。
2. [List410.check](https://github.com/momota1029/yulang/blob/946e899804616347f41fc361a876253e73e5ff3f/lean/Yulang/GeneralDeclarativeI65I74ListEntry410.lean#L171) の追加 branch が読む証人は元 origin ordinal、alias 順位列と色パレットだけ。実役割・現に見える宣言・mode をチェックし、元グラフの根だけに対する [checkExactEscape](https://github.com/momota1029/yulang/blob/946e899804616347f41fc361a876253e73e5ff3f/lean/Yulang/GeneralDeclarativeI65I74ExactEscape410.lean#L59) を検証。構造辺は無濾過の元 rows を `shapeOf` で実際に読んだ edges。普通の Bound の順位は alias の一致用で、全構造辺の減少を求めない。根の色 0 から一度出た辺は色 1 に閉じ、色 1 の循環は許す。raw 根に帰ると root alias の同色性に反する（[exact_escape_refutes_raw_root_K2410](https://github.com/momota1029/yulang/blob/946e899804616347f41fc361a876253e73e5ff3f/lean/Yulang/GeneralDeclarativeI65I74ExactEscape410.lean#L90)）。
3. [List410.check_sound](https://github.com/momota1029/yulang/blob/946e899804616347f41fc361a876253e73e5ff3f/lean/Yulang/GeneralDeclarativeI65I74ListEntry410.lean#L207) は同じ元 Problem・exact Report の成功から本来の `SourceTrace R2` と診断・出力順を反映し、同じ State の**任意の fitting model** の `ReportEvidence` を保つ。旧 branch はそのまま呼び、古い実 trace を移しても書込みや子順を変えない。[checked_report_retains_actual_payload410](https://github.com/momota1029/yulang/blob/946e899804616347f41fc361a876253e73e5ff3f/lean/Yulang/GeneralDeclarativeI65I74ListPriority410.lean#L138) は同じ選択 event の捕捉を元の payload 点に固定する。旧新両 witness が異なる答えを受理できず、全成功 witness の結果が一意（[checked_results_are_unique410](https://github.com/momota1029/yulang/blob/946e899804616347f41fc361a876253e73e5ff3f/lean/Yulang/GeneralDeclarativeI65I74ListPriority410.lean#L184)）。未対応の false は言語上の拒否と同じではない。

## X8 の実例・検証

- [元の X8 受理テスト](https://github.com/momota1029/yulang/blob/946e899804616347f41fc361a876253e73e5ff3f/lean/Audit/Cycle410I74ListSpecX8.lean#L67) の raw graph は、要求根 0 の `list(ν)` から 1 の `ν = :tag ν` へ実際に降り、そこでは本当に自己循環する。根自体には帰らない。全グラフ rank はどの順位列でも作れないにもかかわらず、この checker は true。正則 carrier に `ν` とその一段展開が全観測深さで等しいモデルを作り、**同じ循環 snapshot** の `Fits` と [辞書証拠](https://github.com/momota1029/yulang/blob/946e899804616347f41fc361a876253e73e5ff3f/lean/Audit/Cycle410I74ListSpecX8.lean#L170) を得た。
- alias で 1→0 へ帰路を足した別入力では正 branch は false、旧 raw K2 branch は同じ元 root に対し true（[対照テスト](https://github.com/momota1029/yulang/blob/946e899804616347f41fc361a876253e73e5ff3f/lean/Audit/Cycle410I74ListSpecX8.lean#L81)）。誤った報告、origin 番号、色は false。片方向 Bound と decoder が構造辺を持たない join は、初期の単一色の十分条件では不合格でも最終の exact guard は通る。独立の実行結果 `[true, false, false, true, false, false, true, true]`（順に X8、旧全体 rank、追加帰路の正 branch、旧 raw K2、誤った報告・origin、片方向 Bound、join）。
- 技術 pin `946e899804616347f41fc361a876253e73e5ff3f`、Lean tree `8943ce3be8a4232691a49f1f77805903ae89666a`。固定 Git bytes を別の生成物ディレクトリへ取得して Lean 4.35.0（`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）の `lake env lean --trust=0 -DwarningAsError=true`。新規 6 ソース、独立 Audit 3 本、追加 import の集約、全て exit 0。重複を除く 45 宣言で標準 `propext`、`Classical.choice`、`Quot.sound` のみ（部分集合を含む）。巨大な既存 barrel の prefix bytes と追記 6 本、凍結二ファイルは内容を読まず blob ID を照合した。
- 別の作業出力先から、現 integration の C409 と exact C410 を順に 11 ソース・6 独立 Audit で再構築した場合も exit 0。C02 内の追加の独立ピン再生では、同じ受理 event の束縛 3 が実 payload `(1,1,1)` であること、また別の regular nominal 展開を用いた片方向 Bound の対照にも fitting model と実辞書があることを strict Lean で確認。さらに、片方向 Bound と flat alias が輪になる別の fitting R2 選択では、現在の公開 witness が全て false になることを検証し、[証人の境界](../design/dots-cycle-410-c02-verification.md) に記録した。raw 根 K2 ではない。flat を色で照合する修正候補の健全性と旧 positive 証人の保存は別途検証済みだが、今回は公式入口に入れていない。これらの追加確認で別の C 行は増減させない。

## 引継ぎ

- expected-head non-force で work/dots-main のみ。公開差分は報告・心拍込み 15 パス。C410 の成果はこのブランチで検証。全体の `lake build`、監督役向け `verify-lean.sh`、Rust／Yulang2、パーサ、NoFalseRejection、停止性は対象外。利用枠は不明。
- 次は C03 / X9。X8 の「payload の変数捕捉は visit ではない」を保ち、`impl Show (list 'a)` の実 `where Show 'a` を元の位置で生成し、初めてその子の根に対する既存 raw C350 証人を使う。親を根 K2 にすり替えない。C02 の空 where 証明をそのまま X9 と数えない。

- 最終 integration `a6a88060218fe5b53340c9c705a6719bdb900fce` と同一 I-74 inbox を再確認。

- 最終照合開始 `2026-11-25T06:20:20.085Z`（50 分経過）。

**C の残り: 20 行（C03–C22）。**
