# I-73: C の初期一覧（R₀ で扱えない形）

I-65 の 1 と別に数える。以下は R₀ 対 spec の構文別の範囲差であり、言語エラーや反例リストではない。2・3 の前に新しい形を実装しない。

| 項目 | 現在 R₀ が扱う側と、残り |
|---|---|
| 可視 impl の非重複構造 head（複数行） | R₀ の正の規則は可視行 singleton。複数の構造候補から独立な一致・不一致を全部計算する仕事は C。この周の I-72 公開断片は単項 declared の別タグまでで、R₀ に入れない。 |
| where の record/variant/nominal を作る引数 | 現行は元の位置の変数をそのまま渡す場合。複合の書かれた子要求と正しい型つき行の読みは C。 |
| where の関連型を指定する子の出力 | `LiteralVariableWhere403` の子出力列は空。出力先を指定する where 子とそれを使う順序付けは C。 |
| 宣言された共変単項 head の完了出力由来の下端 | C406 は `ScopedEvidence406`。下端への authored Origin が無いと固定 C402 の `SourceHead` に入らないことが証明済み。元型入力の名前を端点から推定せず、固定証拠と整合する表現が必要。 |
| 多引数/多階層の nominal head・反変/不変/row parameter | R₀ の正の native head は共変の単項 value/変数、根のみ走査。その他の宣言分散と row 残余は C。 |
| record/variant/合流・非点を持つ構造 head | 型付き RHS に record/join を持てても、入力 head の照合は別。隠し field、名付き/開いた tail、合流後の whole-payload 捕捉などは C。 |
| row-valued nominal 引数を含む関連型右辺の固定行 | B6 の木に保持できるが `fixedValueCode403` の ordinary 代表が無い。値側の同じモデルの代表と混同しない。 |
| 依存未完了のみの head と一般の非 K2 保留 | raw root K2 と根拠つき到達子 K2 は分離済み。R₀ は一般の pending 診断ルールを入れていない。足りない範囲を言語拒否にしない。 |

固定 C380 文、I-65 の全称・モデル・結論はこの一覧へ移動する作業の準備としても変更していない。C の数はこの表の構文分類の初期 8 行で、必要十分網羅とは言わない。