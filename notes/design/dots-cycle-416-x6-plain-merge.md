# C416 / X6 前半: 同じ tag の二つの plain binder

実際の単一 point 入力 `R :{tick int}` の元 variant と、元の payload slot の int 行を読んで、実際に宣言された単一候補 `R :{tick 'a,tick 'b}` を扱う。二つの異なる binder は、実際の同じ payload 名をそのまま読む。名前付き nominal や二本の branch の捕捉を使わない。

既存の `SourceHead` は正規化前の実構文を読むため、実 variant 根に保持された同名の自己 join 行を照合する。検査位置は正規化後の一つの variant 根だけ。別名の二つの arm を読むのではなく、同じ名前二回の冪等性をモデル側でも証明する。この保持行は checker の証明対象で、勝手に追加しない。新規 R8 は空 where・空出力の選択だけ追加、raw K2 と旧入口を維持。両 binder の元の名前、実 tag、候補序数を検査する。ground の競合候補と曖昧性は C09 なので扱わない。
