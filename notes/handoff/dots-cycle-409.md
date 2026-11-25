この周に閉じた C の行: C01 / X12「名前付き再帰型 `enum tree` に `impl Show tree` を名前で当てる」（`dictionary_sound_R1`, `Named409.check_sound`、work/dots-main で三条件を検証）。

## I-74 と選んだ範囲

- I-74（inbox `b99a214965f1e236ab62e6cffa13b77b617543cb`）は I-65 (1)–(3) の統合完了を確認した。開始 integration `2ef814b90274efe30e8a07388a6f3cde2698f6dc`、I-74 確認時 `455069b0b629199c8c0fa63aa4b2ccaaafd9391b`。`dictionary_sound_R0` の blob `8af8804db399afe2753bfdb68c55b22b460e6b1f`、公開 `Checker408.check/check_sound` `ac7180641a745302f038e61afb0d29f57456c6ec`、関連 standalone audit の exact blob を確認。開始時に C408 の Lean 差分 17 パスがすべて独立 replay 済みの bytes と一致した。
- [C 一覧](../design/dots-cycle-409-c-coverage.md) を作り、spec／X 番号別の 22 行へ、初期 C407 分類と C380 の未対応範囲を重複なく移した。先に例のある C01/X12 のみを進めた。本文を開かない、型引数 0 の named head を対象にする。1 引数、元 role/decl が実在、可視 singleton、元の同名・同点の端点、空 where/出力の例。別の origin・非点・複数候補や各種 where まで完了とはしない。
- 単に普通 C349 の coverage を使うと、具体的 X12 の正しい declared nominal を弾くことを確認。C357 の元宣言の mode／constructor coverage、空 where の source readiness でその宣言を照合した。元の名前を中心のモデル値や普通の同値から作らない。`RootCycle` は無濾過のままで、元グラフの有限 rank を検査。rank を渡せない場合の false は言語上の拒否ではない。

## I-74 の三条件

1. [namedLocal409](https://github.com/momota1029/yulang/blob/7ce2f27199f48e8c7142abd1883d046698d5ecce/lean/Yulang/GeneralDeclarativeI65I74NamedLeaf409.lean#L93) の選択規則だけを R₀ に足した `R1`。任意の State・要求・辞書について、`Classifies R1 s q (.selected d)` ならその State の任意の fitting model で**固定 C402 の `DictionaryEvidence s m q d`** を得る（[dictionary_sound_R1](https://github.com/momota1029/yulang/blob/7ce2f27199f48e8c7142abd1883d046698d5ecce/lean/Yulang/GeneralDeclarativeI65I74NamedLeaf409.lean#L114)）。同じ有限混合 trace・where 順・support を扱い、既存の `other` は変えない。追加の named head に競合する旧局所枝や隠れた候補内 K2 がないこと、raw 根 K2 は以前同様に優先することも証明した。
2. [Named409.check](https://github.com/momota1029/yulang/blob/7ce2f27199f48e8c7142abd1883d046698d5ecce/lean/Yulang/GeneralDeclarativeI65I74NamedEntry409.lean#L142) の `.bareName` は、元 `Problem` に対する origin ordinal と有限 rank だけを証人にもらう。モデルも受理の証明も受け取らない。関係のある元 EndPoint と宣言・role 行、枝の結果・実書込み列を再計算して比較する。未対応形は false。旧入口は全入力で rfl のまま、旧 raw／nullary が新 named と同一 Problem で両方通ることはない。
3. [Named409.check_sound](https://github.com/momota1029/yulang/blob/7ce2f27199f48e8c7142abd1883d046698d5ecce/lean/Yulang/GeneralDeclarativeI65I74NamedEntry409.lean#L178) は任意の Problem・報告・証人について、true なら同じ要求・診断木・実書込み順の実 R1 分類と、同じ State の**任意の fitting model** の `ReportEvidence` を返す。既存の証明は `liftTrace` で元のイベントを変えずに移し、辞書の固定意味を変えない。[checked_results_are_unique409](https://github.com/momota1029/yulang/blob/7ce2f27199f48e8c7142abd1883d046698d5ecce/lean/Yulang/GeneralDeclarativeI65I74NamedCompatibility409.lean#L54) で成功証人が複数でも報告が一致する。

## 具体例・検証・引き継ぎ

- [X12 の独立 Audit](https://github.com/momota1029/yulang/blob/7ce2f27199f48e8c7142abd1883d046698d5ecce/lean/Audit/Cycle409I74NamedSpecX12.lean#L58) は、実際に自分の名前を参照する tree の宣言 body、元の required role、1 引数、元 authored nominal 観測をコンパイルした resolved B4 入力。名前の照合で入口は true。明示的 fitting model とその場の辞書が存在する（[同じ model の辞書](https://github.com/momota1029/yulang/blob/7ce2f27199f48e8c7142abd1883d046698d5ecce/lean/Audit/Cycle409I74NamedSpecX12.lean#L104)）。異なる origin ordinal、違う nominal 名、混入した無名構造ループ、違う辞書、旧 nullary 経路は false。独立 `#eval` 出力 `[true, false, false, false, false, false]`。Rust やパーサで動かした主張ではない。
- 技術 pin `7ce2f27199f48e8c7142abd1883d046698d5ecce`、Lean tree `b44598ae4530b5aa0bbd7ea55d1c0b86c8a4bfed`。 exact Git bytes を別の生成物ディレクトリへ取り直し、Lean 4.35.0（`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）の `lake env lean --trust=0 -DwarningAsError=true` で新規 5 ソース、独立 Audit 3 本、追加 import の集約を検査（最終全て exit 0）。`#print axioms` は重複を除いて 28 宣言、標準 `propext`、`Classical.choice`、`Quot.sound` のみ（部分集合を含む）。旧 barrel 全 prefix と 5 import だけの追記、凍結二ファイルは内容に触れず blob ID で確認。途中の集約だけ namespace が未指定で失敗したので集約監査スクリプトを修正し、最終技術 pin を取り直して通した。既存の直接依存 4 本は integration と技術 pin で exact bytes を照合。既存依存の追加の cold rebuild は C353 のタイムアウト 124 で打ち切ったため、全依存の再ビルドは主張しない。
- 回復: C408 は報告あり・作業者終了が明記された時間上限引継ぎで、クラッシュとは扱わなかった。C409 冒頭の I-73 typed-output 基礎は設計ノートだけ。I-74 が入った時点で Lean 草稿を留め、C11 を閉じたとは数えない。初期の strict import は共有実行環境の遅さで timeout 124 があったが、C01 の最終の独立再実行は完了した。全体の `lake build`、`verify-lean.sh`、Rust/Yulang2、停止性、NoFalseRejection は未実行・対象外。利用枠は不明。
- expected-head non-force で work/dots-main のみ。公開差分は報告・心拍を含めて 14 パス。C01 は作業ブランチの成果。次は C02 / X8（`Len (list 'a)` / `len [loop 1]`）。X8 の payload 循環は許されるので、C01 の全グラフ rank で弾かず、根から実際に必要な検査位置だけと構造循環を区別する。

- 最終 Integration `455069b0b629199c8c0fa63aa4b2ccaaafd9391b`、I-74 inbox の同一性再確認。

- 最終照合開始 `2026-11-25T05:21:16.271Z`（50 分経過）。

**C の残り: 21 行（C02–C22）。**
