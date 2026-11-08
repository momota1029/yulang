# cast境界の追加監査（X18精密化）

旧Y2 `d4c8bc8fc8a49173180932cd25921a2c41057354`。cycle1 `y2-claims-casts-roles.md` と新spec06 §6.5を読み、no-preludeで既存releaseを使用。算術は `my add: int -> int -> int = builtin_op::int_add`、直接 `add 7 1` は8。user_idは `struct user_id {raw:int}`、castは `cast(x:user_id):int=x.raw`。各例全文・コマンド・stdout/stderr・exit・秒は `runtime-cycle-2-casts.md`（入力・出力全文。機械可読4JSONはローカル作業補助）へ保存。対象repo変更・公開・buildなし。

| ID | 出典 | 規則 | 例 | 実機結果 | 新spec | Lean | 分類 | 備考 |
|---|---|---|---|---|---|---|---|---|
| CAST-MORE-001 | 旧web/docs/ja/reference/casts.md:21–39 | direct expected-type境界でcast bodyが走る | direct-return/direct-arg/direct-add | check0/run0、7/7/8。cast bodyを42に変更したdirect-return-markerは42 | §6.5 既知期待型境界 | CommonNominalCoreCastRegistry.compile_exactは対応する核の部品。surface全体は未検証 | 一致 | markerにより単なるnewtype表示剥がしでなくbody結果を確認。 |
| CAST-MORE-002 | 旧casts.md:90–96 nominal中心。X18追加試験 | finite box後変換は新specで共変、既に得た値を別境界へ渡す必要がある | box-return、box-projection: `widen(x:box user_id):box int=x` | check0/run0。返却box内にuser_idが残り、projectionもuser_id | §6.5 有限boxは後から共変cast、新値を作る | CommonDeclaredCastEvaluationExamples.box_executesは明示planで二重boxのleafを変える例 | 違う | 注釈がintだから実値もintと解釈しない。旧dumpはboxの区間を持ち、完全なbox intへの変換成功とは言えない。 |
| CAST-MORE-003 | 同上 | 取り出した値に後から独立cast境界を追加した成功と、箱自体の変換を分ける | box-add: `add (widen (...)).value 1` | check0/run0=8。cast body42なら43 | §6.5 scalar境界 | 上記box plan定理のsource bridgeではない | 一致 | 8/43は後段scalar期待型を追加した入力での成功であり、挿入位置の内部traceは未取得。box返却時のpayload変換を証明しない。 |
| CAST-MORE-004 | 同上 | 利用側がbox intのfieldをint primitiveへ要求する | box-consumer-add: `consume(x:box int)=add x.value 1` にbox user_id literal | check0、run1 runtime unsupported-runtime-feature: non-int primitive argument。box int controlは8 | §6.5 finite boxを共変変換するなら8期待 | box_executesは抽象Value/明示planに対する定理 | 違う | この入力での型検査通過と実行失敗を確認。全言語の健全性欠如や原因箇所は断定しない。 |
| CAST-MORE-005 | 同上 | producerでbox user_idを確定してから利用側へ渡す | make():box user_id=box literal; consume(make()) | make単体check0/run0。box int consumerへの使用はcheck0/run1 compile unsatisfied-subtype box(user_id)<:box(int)。identity consumerも同じ | §6.5 finite boxは後変換可能 | box_executesはsource elaboration非対象 | 違う | literal直渡しのruntime failureと異なり、runのcompile段階で拒否。check0をrun成功としない。 |
| CAST-MORE-006 | 旧casts.md:21–39,90–96 | 明示scalar変換を別関数で実行して再構築する対照 | back(x:user_id):int=x; convert(x:box user_id):box int=box{value:back x.value}; consume(convert(...)) | check0/run0=8。ただ単にbox{value:x.value}で再構築するとcheck0/run1 non-int primitive argument | §6.5 expected-type境界 | source全体の対応未検証 | 一致 | 明示backのある局所回避策の観測。既存コードは変更せず。 |
| CAST-MORE-007 | 旧casts.md:90–96 structural conversion限定 | 構造recordをliteralから渡す場合と構築済みproducerから渡す場合を区別 | consume(x)=add x.value 1; consume{value:user_id...} / consume(make()) | literal check0/run0=8。make()={value:user_id...}経由はcheck0/run1 non-int primitive argument、marker42でも失敗 | §6.5 record成分castは新値を作る | Casts.accepts_exact/converts_exactはstructural boundaryの抽象モデル | 違う | literal側の成功を構築済みrecordの一般変換成功としない。両方とも実名nominal boxではなくstructural record。 |
| CAST-MORE-008 | 旧casts.md:15–17,90–96 | 異なるnominal型への明示outer ruleは別の試験 | user_id→target{value:int}明示cast、consume(x:target) | check0/run0 target({value:7}) | §6.5 明示規則 | CommonNominalCoreCastRegistry.compile_exactの対応部品 | 一致 | この成功を同じboxの引数だけを変える変換と同一視しない。 |
| CAST-MORE-009 | 旧casts.md:90–96 | box全体の明示cast追加の効果を確認 | cast(x:box user_id):box int=box{value:x.value.raw} | literal consumerはcheck0/run1 non-int primitive argument。固定producer経由はcheck0/run1 compile unsatisfied-subtype | §6.5 明示規則とfinite box変換 | そのsource compilerまでの接続は未検証 | 違う | これらの境界で明示outer rule追加では修復しなかった。cast body自体が呼ばれたかの内部traceなし。 |
| CAST-MORE-010 | 旧casts.md:90–96 | 構造tupleの既知戻り型cast | widen(x:(user_id,int)):(int,int)=x | check0、run1 compile unsatisfied-subtype `(user_id,int)->(user_id,int) <: (user_id,int)->(int,int)` | §6.5 tuple成分cast | CastExamples.tuple_components_are_covariant | 違う | この関数境界例でのみ確認。全tuple castが失敗するとは言わない。 |
| CAST-MORE-011 | 旧annotation builder対応範囲 | record戻り型注釈で同じ試験を表す | widen(x:{value:user_id}):{value:int}=x | check1/run1 unsupported type annotation syntax: record type annotation | §6.5 record変換 | 未照合 | 未確認 | 型注釈parser境界で止まるので変換挙動の反例としない。 |

## 試験の初期失敗を省略しない

最初の12ケース（36 CLI）は `struct user_id(int)` と `x.0` を使用した。この旧構文では `x.0` がdump上で `x 0.0` のように読まれ、`type shape user_id is not compatible with required shape function` となった。算術control以外の目的のcast検証に達していない。これらも `raw.json` に保存。修正後のrecord nominal版は `record-nominal-raw.json` に別保存し、初期失敗を隠していない。ケース名は同じでも入力が異なるためJSONファイル名も必ず区別する。

`box-direct-projection-consumer`（scalar consumer関数へbox literalのprojectionを直接渡す）もcheck0/run1 non-int primitive argument。この形と成功した `box-add` は異なる境界配置であり、同じ試験結果としてまとめない。

cast規則を削除した `box-consumer-no-cast` はcheck0/run1 `conflicting type candidates: user_id vs int`。規則ありの場合と診断が異なるが、この差だけで内部変換の正しさや原因を断言しない。

## Leanの限定された対応

`CommonDeclaredCastEvaluationExamples.box_executes` は全 `token : Nat` について、明示定義された二重box plan `box` とleaf関数 `increment` に対し、`executeChecked box increment 0 (boxValue token) = some (boxValue (token+1), 5)` を証明する。source宣言からこのplanを生成する正しさ定理ではないとファイル冒頭で明記されている。

既存 `Casts.lean` のnominal arguments opaqueという古いモデルの局所前提を、そのまま訂正後specの有限box不変という主張には用いない。`Casts.nominal_arguments_need_outer_rule` は `Compatibility.nominalInvariant` を仮定する部品。有限boxを共変とする新規定のsource compilerとの接続まで証明済みとはしない。

今回はソースreadと旧Y2実機の小例比較。Leanの追加build、runtime内部のtrace、一般の型安全性定理/反定理、cast計画生成の完全監査は実施していない。

## 標準prelude対照（cycle2後半）

`box-consumer-add` は標準prelude有りでも0.239秒で同じnon-int primitive argument、`box-fixed-producer` は158.763秒で同じcompile subtype拒否、`box-explicit-back` は0.212秒で8。実機全文は `runtime-cycle-2-effects-patterns.md` のstandard3節。no-preludeの未読込だけではこの差を説明できない。
