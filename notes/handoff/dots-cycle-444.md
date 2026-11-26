この周に閉じた G の行: なし（G00 の FullState / FitsFull と旧 State の空持ち上げを定義・検証）。G の残り: 22 行（G00 を含む）。

# cycle 444 — G00: 元の型付き固定先等式を保持できる状態

実開始 2026-11-26T15:30:00.001Z。I‑81（inbox `48b627611c0dad7ec9b0235c105d016a23e90a8a`）。開始時正本 integration/m1-final@90dd90f10c9639b27190490524a0dd5e96d600d6、Lean tree `54677fdcb38877f141f5065ea342fd362471afdd`。使用量の枠は不明。

## この周の定義とテスト

- [新しい FullState モジュール](https://github.com/momota1029/yulang/blob/a83d47c4d58231239c9ca15574873fc5af7ebc18/lean/Yulang/GeneralDeclarativeI65I74FullState444.lean)。既存 State に、元要求・出現・宣言 frame と ordinal・元の出力 ordinal を依存型で結び、B6 本体・型付き RHS・元の固定先を保つ等式の列を足した。関連出力全体は value kind、入れ子の row/value kind と捕捉は元 tree に残る。固定先は元要求から読むため別の値として書き込めない。Fit は旧制約と全保持等式の連言。payload にはモデル、等式の成立、または完了の証拠を前提として入れない。
- `fits_iff_fitsFull_liftState`: 任意の旧 State とモデルで、旧 Fits と保持行が空の FullState の FitsFull は同値。一般 Audit は、任意の保持行について同じモデルで元の型付き本体を評価した値が元の固定先に同値であることと、元の出現／宣言／出力番号・本体を指したままであることを確認。
- C442 実 replay から、元の固定先 21 が**すべての FitsFull モデル**で、同じモデルの元 row 捕捉・value 捕捉で作る `ref` 値と同値（`all_original_full_fits_retain_mixed_target444`）。旧 source 自体は row 変数を全モデルで一つの値に固定しないため、signed row は元捕捉が signed の場合の一般系と、実際に適合する明示的 signed model で別に検査（`signed_model_really_fits_original_full444`）。保持前の空 row 対照は旧 Fits のまま、元保持込みでは不適合。
- 同じ本体・元捕捉を読んだ別要求の実固定先 22 に適合する一つのモデルは、元先 21 の保持に適合しない（`wrong_slot_does_not_substitute444`）。22 は 21 の代用ではない。先に 21 が Int の State は旧モデルと source replay を持つが、21 に混在 RHS の保持を追加すると**どのモデルも**適合しない（`conjunction_with_preexisting_int_has_no_fitting_model444`）。旧 Int 等式は上書きしない。新たな言語診断は発行しない。

## 検証・公開

- [不変の技術 pin](https://github.com/momota1029/yulang/commit/a83d47c4d58231239c9ca15574873fc5af7ebc18)、Lean tree `ad3f986f65f00e0c7587a54980b3d84aea2fdce1`。公式 Lean 4.35.0、production 1 本を `lean --trust=0 -DwarningAsError=true -o …`、独立 Audit 2 本を production-only path・他の Audit を含まない個別位置から同じ厳密フラグで実行。全 exit 0、16 宣言は標準公理のみ（公理なしを含む）。Audit の import: Yulang.* 以外 0 件。Git の実バイトが検査済みファイルと一致。全体ビルド、verify-lean.sh、Rust は実行せず。
- 既存 production 7,694、既存 standalone Audit 2,083、修正対象外の Lean 直下31項目の blob/tree IDs が不変（凍結 Audit.lean/README.md は ID のみ）。集約 import 末尾に 1 行追記だけ。公開は新規 Lean 3 本、集約 1 本、報告と心拍の計 6 paths。work/dots-main のみ expected-head nonforce。
- 公開外の focused Lean 点検では、任意の既存 Event の元出力順で保持行を作ったときの FitsFull と旧 Fits ∧ 同じ Event の FixedTargets の同値、追加列は連言、真正 receipt の別 target への読み替え不可、実際に読む typed 座標の依存を確認した。旧端点射影 lane の既存三行から同じモデルで得る意味も、FullState の元制約を投影して保存。新しく保持するコンストラクタは indexed named output 用で、名前なし射影起源を一般に新築したとは言わない。補助 QA は公開 Audit 16 に含めない。
- 終了時の正本 integration/m1-final@90dd90f10c9639b27190490524a0dd5e96d600d6（Lean tree `54677fdcb38877f141f5065ea342fd362471afdd`）。今回の Lean tree の採用は終了時点では未確認。証明と対照は work/dots-main に固定。

G00 は土台のみ。保持行を実際の規則・生成器から作る接続、独立な規則・data-only checker と同じ State の正確な報告／証人は未実装。R_full、check_full、G01 以降、A の証明、B、診断網羅性、停止性は対象外。旧 I72.State/Fits/規則/checker/固定声明は無変更。言語意味の新決定・質問ノートなし。
