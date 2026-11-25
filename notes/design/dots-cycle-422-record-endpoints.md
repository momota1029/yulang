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

## 次の接続点：literal ではなく実投影を B6 に渡す

- Target equation を支える head が直ちに必要とするのは各モデルでの実 projection と mask。第三のモデルでは record 再構築が不可能なのにこの証拠は成立する。別の適合割当てにこれらの値を新しい未使用座標で表現できるが、元の State には行を作らず、元の割当てのその座標に既に値が入るとも仮定しない。
- `readProjectedOutput422` は同じ宣言の lookup と本物の B6 atlas から元の `type out = 'a` の木を読む。`ProjectedOutput.actualRightValue` は元の出現・宣言番号・出力番号・固定先を保ち、同じモデルの実 field をその木の値側に使う。旧 B6 の一般 tree evaluator を再利用する。`int`、`int | bool`、`top` の各モデルで確認。擬似の型つき本体や model の座標を読んだことにはしない。
- 残る接続は、(i) C14 のこの元 source projection を受ける head 証拠、(ii) 元の B6 と固定先の保持関係（値を計算することとは別）、(iii) 固定している公開結果・根 K2・健全性を変えない検査器の接続。今周は、これらをすでにある旧 `SourceHead` に偽装しない。

### 既存の結論を変えずに続けるための区別

- C402 の `DictionaryEvidence.node` は、`Classifies` とは独立にも `Event.head : SourceHead` を引数に取る。したがって「新しい分類器で同じラベルを返す」だけでは元の非点例に対する旧辞書証拠は成立しない。旧 `HeadMeaning` の literal 同値そのものが第三の適合モデルで不成立。この点は実行子の不足とは別である。
- 将来の候補を段階で分けるなら、`Read p` → 同じ `m` の required/optional/残余 `ProjectedRecordChannels` → `ProjectedOutput.actualRightValue m` → **同じ固定先で保持された型の等式** → 元順の報告値。今回までで実装したのは両端点読取りから元の出現の RHS 値側まで。最後の二つを仮定した証明を完成とは数えない。
- 旧の `HeadMeaning` で中心行なしの構成ができるなら、実中心の全体型は下端と同値、field 端点・mask residual 端点もそれぞれ意味上等しくなる。これは “違う番号なら非点” という誤読とは別。新しい設計では同じ番号や同じ head の綴りからそうした同値を推論しない。
- 元の実中心が二つのモデルで意味上同じなら、原 B6 評価で返る field と残余の同値まで transport できる。field の意味はモデルの実中心から、語彙束縛と出力の座標は actual source/B6 atlas から取り、どちらも相手の証拠を代用しない。
- この範囲の `Read` では、原宣言の唯一の明示 associated equation と実要求の名前から lookup の `.explicit` が必ず一致する。`readProjectedOutput422` が値側を返す条件は、同じ元の B6 atlas 位置に型つき plan があることとちょうど同じ。実出力型の一致や中心 literal record をここで再検査して、端点からの選択を妨げない（scratch で strict 確認）。
