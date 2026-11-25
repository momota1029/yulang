# C422 C14: record の根拠付き両端点と固定証拠の境界

仕様 §6.3（`spec/06-roles.md` 395–408 行）は、中心の record 行が未完の W しか根拠を持たなくても、元の上下端点に独立の根拠があれば Pick を選び、field と残りを二つの区間として捕捉する。原仕様例の `type out = 'a` は元の捕捉の実中心名を使う。未確認を拒否・保留に変えない。

1. 元の一要求、可視一宣言、明示の `{x:'a,..'rest}`、上・下の独立な `Origin` と実際に保持された両 endpoint の record 式を照合する。子の field/residual の名前の端点は元の式の operands、三つ目の名前は別の実論理表示／型付き入力の名前であり、下端や上端で埋めない。raw root K2 は普通の全式から判定する。候補選びに中心行は不要。
2. 読んだ端点に対し、任意の同じ適合割当てで、真の中心型の field projection および同じ label の mask/subtraction が各端点から挟まれることを、既存の carrier の射影単調性から確認する。記号名に意味を付けるために中心行を勝手に作らず、有限データだけを読む。一般の exact record deletion と mask は同一と仮定しない。
3. 接続先は凍結された `Event.head : SourceHead`。旧 `DeepHead.ordinary` の `Center.direct` は中心の等式を要求し、`Center.endpoints` は各 mode-sensitive binder の逆向き bound まで要求する。`DeepHead.declared` は nominal の head、`SourceHead.joined` は別の nominal/variant join。この二択が中心行のない真の非点捕捉を表現できないなら、exact inversion と、旧カーネルを変えずに証明できる射影までを報告し、C14 は閉じない。言語の質問と、既に決まった仕様の内部証明表現の不足を混同しない。
