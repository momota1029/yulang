# C422 C14: record の根拠付き両端点と固定証拠の境界

仕様 §6.3（`spec/06-roles.md` 395–408 行）は、中心の record 行が未完の W しか根拠を持たなくても、元の上下端点に独立の根拠があれば Pick を選び、field と残りを二つの区間として捕捉する。原仕様例の `type out = 'a` は元の捕捉の実中心名を使う。未確認を拒否・保留に変えない。

1. 元の一要求、可視一宣言、明示の `{x:'a,..'rest}`、上・下の独立な `Origin` と実際に保持された両 endpoint の record 式を照合する。子の field/residual の名前の端点は元の式の operands、三つ目の名前は別の実論理表示／型付き入力の名前であり、下端や上端で埋めない。raw root K2 は普通の全式から判定する。候補選びに中心行は不要。
2. 読んだ端点に対し、任意の同じ適合割当てで、真の中心型の field projection および同じ label の mask/subtraction が各端点から挟まれることを、既存の carrier の射影単調性から確認する。記号名に意味を付けるために中心行を勝手に作らず、有限データだけを読む。一般の exact record deletion と mask は同一と仮定しない。
3. 接続先は凍結された `Event.head : SourceHead`。旧 `DeepHead.ordinary` の `Center.direct` は中心の等式を要求し、`Center.endpoints` は各 mode-sensitive binder の逆向き bound まで要求する。`DeepHead.declared` は nominal の head、`SourceHead.joined` は別の nominal/variant join。この二択が中心行のない真の非点捕捉を表現できないなら、exact inversion と、旧カーネルを変えずに証明できる射影までを報告し、C14 は閉じない。言語の質問と、既に決まった仕様の内部証明表現の不足を混同しない。

## 実証できた証拠表現の差

- 元の `Pick` の引数は `(0,1,2)`、元の二つの書かれた record operands は field `3,4` と residual `5,6`。宣言は `{x:'a,..'rest}`、元の関連型指定、B6 の型付き局所 binder、元の結果先 `12` がある。中心 1 に record 行や origin はない。両端点の独立 root origin を外す、または locator をすり替えると新しい端点リーダーは通らない。
- 全称の逆向き検査: `original_fixed_record_source_head_forces_endpoint_equivalence422` は、中心に record 行がない限り、既存の **すべての** `SourceHead` から同じ適合モデルで両端点の意味の等しさを導く。候補の capture を別に選んでも逃れられない。`primitives_only_cannot_add_genuine_nonpoint_record_selection422` は、片方の適合モデルで端点が本当に異なれば **どの `SourcePrimitives` を渡しても** 選択を導出できない。現行 R13 の公開入口も、その健全性の定理からどの選択証人でも false。拒否／保留の証明ではない。
- 正対照: 観測された両端から同じ field/tail 名を読む「意味的な点」なら、記号上異なる root 名と中心行なしでも旧証拠を構成できる。真の非点例をそこへ置き換えていない。真の非点例の二つのモデルでは、同じ端点の型を保つ一方、実中心の field 型が `int` と `int | bool` に変わる。どの既存の論理名もこれら両方の真の field を常に表すことはできない。
- 旧 State・旧モデルを変えずにできること: `same_model_endpoints_support_both_projected_channels422` は各適合割当ての実中心で、required/optional 両方の field 区間および実中心の mask residual 区間を与える。両方の存在は強い literal 再構築とは別。general exact deletion の証明ではない。
- 別 State への相対延長: required/optional の投影が同値のときに限り、既存名と元結果先を変えずに新規名の literal record 行を別の普通 State に加えられる。二つの具体モデルでは field 三つ組 `(3,newCenter,4)`、元の結果先 `12` 不変。一方、同じ authored source・B6 binder を持つ第三の適合割当てに required/optional が異なる有限反例があり、別 State へのその延長すら全モデルには通用しない。条件を隠して元の State での健全性を主張しない。

次の証拠設計の候補は、端点の根拠を持つ head の意味に「同じモデルでの projection と mask を保つ」形を用意し、型付き output 側がその元 binder を読むことを示すことです。新しい名が既に State にあるとか、投影から常に literal record を組み直せるとは仮定しません。固定された宣言・入口を変更する作業は今周には含めていません。新しい Yulang 言語仕様の選択は必要ありません。
