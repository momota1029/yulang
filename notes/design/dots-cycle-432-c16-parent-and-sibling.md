# C432: 元 Wrap の固定出力と合法な兄弟出力

§6.3 の output-only 境界に従い、元の where で b を受ける場合に **宣言済み不変 value 引数**の逐語的 unary `list 'b` を親の確定した RHS として読む。実親の B6 atlas の元 occurrence・declaration/output ordinal・body 記録がその型つき plan を返したことは前提として残す（辞書や適合モデルだけから作らない）。その plan を持つ実選択済み親の receipt は同じ適合モデルで `list(assignment child target)` を元の固定先に書くことを示した。

元親 frame の named output slot を読む合法な別 clause は、独立した入力 a を維持して同じ固定先を共有できる。実 `Wrap` 型の宣言ヘッダ・元 Container clause の順序・output ordinal と、合法な兄弟の元位置 [72,1] を Lean で確認。別の where の名前なし `Show b` は既存の output-only 条件に反し、`DeclarationChecked` にできない。実行順・安定化の theorem ではない。

これは宣言・B6 plan/固定先の橋の検証。C16 の正規 R16/check/check_sound と、Wrap→Container の同じ State における選択済み親子を一本で実行する public fixture はまだない。C 残り 7。