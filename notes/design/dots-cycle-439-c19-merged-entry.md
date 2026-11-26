# C439: 同じ名前なし入力に対する、同じ関連出力の矛盾

I-74/C19、[現行 §6.3 の原例](https://github.com/momota1029/yulang/blob/ff86b00b59d6439ac9584767cdf95e35950ab3d0/spec/06-roles.md#L231-L259)。元の `P int`、`R(out=int), R(out=:tick int)`、nullary `impl R`。C438 は正本 `ff86b00b59d6439ac9584767cdf95e35950ab3d0` に統合済み、Lean `2bba5d89d1e8d9c2d94c5fc3a8a359c3b3b63421`。I-79 inbox `63620853fb52ce1319c2bd85d2b42b2cca7b2e72`。変更は既存の意味・旧規則・I-65 外形に対し加法的。曖昧を拒否に読み替えない。

- 宣言的 `Original439` は同じ State の実 P 頭・元の2 where clause（同じ role、空の名前なし入力、同じ関連名）・実の singleton R 候補・元の Compiler350 frame/ports/発行行を持つ。両 output cell と元親入力 cell を混同しない。元の2要求を位置0/1に保持し、併合された代表要求の場所を0に置く。旧 `WhereForest` の元の2子を勝手に1子に縮められないことも証明。旧 Tree/Result を変更せず追加の source/report rule だけが `.selected P [.rejected]` を返す。
- `replay439` の証人は元の親入力 origin の locator と有限の raw 非循環データだけ。入力型、実候補、発行先、期待判定は証人から受け取らない。実ブック、型翻訳、元の分離した保持行と区別される cell、元の where 位置を読んで既存の `preparation` / `whereBatch` / `execute` を実行し、exact compiler/frame/kids を照合する。異なる型 metadata に、raw int 行だけで適合させない。
- 先行ヘッダの bounded `stableSchema` は unary から binder への形しか直接反映できない。この原例では閉じた `P int` と nullary R なので代入は何も変えない。新しい `closedNullaryDescent439` のその分岐だけから、同じ counts / strict-small / conservative / capture-stable 条件が導かれる。既存の先行 checker は変更しない。
- 全適合モデル m で、元の別々の出力は int と :tick int にそれぞれ同値。二つの同名出力を併合して同値にする場合だけ矛盾する。元の State がそもそも不可能、とは仮定しない。実際の非空モデルを明記した。親を K2 拒否するのではなく併合子だけを拒否し、raw K2 は旧 entry から区別して通る。候補を削って singleton にすることはなく、実の可視 nullary 候補が2本の例では Conflict 分岐は false。
- 三条件: `MergedOutput439.R19` と `dictionary_sound_R19`、proof-free の新しい public `check`、`check_sound` と `verified_R19_result_classifies_in_same_State439`。全旧 witness 入力/報告で従前 Bool と定義的に同じ。scope 外の false は言語としての拒否ではない。

## 実 entry 検証

元の宣言 P=37/R=38、親入力[7]、元子[7,0]/[7,1]（clause42/44）、名前0の出力 cell1/2。併合代表位置は[7,0]、保持する出力は二つ。実例に proper report で true、root-only/重複拒否/誤った親候補/同じ slot で別 issuer/別関連名/親入力 cell 流用/実の有効な rival/誤った constructor metadata で false。raw self-cycle の対照では旧 raw-report true、新 merged-output report false。全体の曖昧さの完全判定・solver・Rust・停止性は主張しない。

## Exact Git + Lean

```text
59d54225daeee48cc6d7a2ae148d1729289ca3a9  lean/Yulang/GeneralDeclarativeI65I74MergedOutputSource439.lean
c6ef50466f22dbe374b1b5fac94652e0ac207e82  lean/Audit/Cycle439I74MergedOutputSource.lean
183169a168adab95c7b03c1d5ca8652b65e5b709  lean/Yulang/GeneralDeclarativeI65I74MergedOutputHeader439.lean
a6316682ca4b95399e99440a329f9b4e0be44926  lean/Audit/Cycle439I74MergedOutputHeader.lean
f1c41c6bd50ee2b19fb452eda81bb0264fb93839  lean/Yulang/GeneralDeclarativeI65I74MergedOutputRead439.lean
ba155bfd2f9a49762df149891779ae3d28330277  lean/Audit/Cycle439I74MergedOutputRead.lean
1548de70fecb83448e273cb49e7f199d432b774e  lean/Yulang/GeneralDeclarativeI65I74MergedOutputEntry439.lean
47249609bf3442d61398775be915bf5ca488494d  lean/Audit/Cycle439I74MergedOutputEntry.lean
e57ee538b8cd0717a0bbee248bdf0b485bfae3ac  lean/Audit/Cycle439I74MergedOutputEndToEnd.lean
```

公式 Lean 4.35.0、各新 production 4 本の `lean --trust=0 -DwarningAsError=true -o ... module.lean`、Audit 5 本をそれぞれ空 source cwd/production-only cache で同 strict flags で物理ファイルから独立実行、すべて exit 0、全 28 公理出力は標準のみ。Audit の import: `Yulang.*` 以外 0 件。正本 snapshot の既存 4,075 dependency sources は exact cache provenance との比較; 全再 build ではない。旧モジュール・テスト・凍結ファイル ID と意味変更なし。barrel の末尾に実 imports 4 行を追加。監督役の全検証/Rustはこの周では行わない。
