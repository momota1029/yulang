# C420: `C12` role 側の関連型 default

仕様 6.1 は該当名の明示本文がないときだけ role の既定本文を使う。10.7 は既定本文の変数を *role 引数の位置* から置換する。`char` は現在の Lean `Inference.Base` にはないため `type value = char` の primitive を置き換えない。独立の、同仕様で認められる第一階の位置 0 の既定値の実例を、一点の既知二 field record・可視一候補・where なし・出力一つで確かめる。head の binder は field と residual、既定値の位置 0 はそれらでなく元引数全体。`lookup` と `Supplies.default` で該当名の明示式がないこと、role に当該既定値があること、元 B6 の出現・宣言順・出力順・固定行を同一 State で照合する。C419 の根 raw K2 と以前の dispatch は保持する。
