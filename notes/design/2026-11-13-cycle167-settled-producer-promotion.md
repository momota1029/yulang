# Cycle 167: 解決済み producer 出力の実際の Trusted 昇格

## 結論

`GeneralDictionaryCapturedSettledProducerTrust.producer_output_trusted` は追加仮定なしで、実際の `observed` に producer 出力を含む Trusted slice が存在することを証明する。slice は producer 出力、producer 入力、親入力の順に積まれ、int の有限 readback を保持する。親出力は使わない。

従って前の `consumer_input_not_ready` は「解決済み producer 出力を Trusted に昇格できなかっただけ」ではない。昇格できても、出力 target と元の捕捉 source2 の対応は現在の Trusted slice では得られない。この対応が親 Outputs に含まれることが、今回の固定状態の障害として切り分けられた。

spec 6.3 の兄弟間の型流入と I26 の source / settled-output 再開に対して、この routing の扱いは監督役が確認する実装範囲の論点。既存の provenance 設計文書も正当な説明をすべて Trusted として再構成できる一般の完全性を未証明としている。ここでは新しい言語判断、guard の変更、全将来状態の deadlock を主張しない。

## 公開定理の全件索引

名前空間は `Yulang.GeneralDictionaryCapturedSettledProducerTrust`。以下の7件はすべて固定 captured fixture についての具体的補助・正例であり、一般 V5 の定理ではない。`roles` は固定の `GeneralDeclarationExamples.roles`。

1. `parent_trusted`：追加仮定なし。実際の `observed` で親 input 一個・空 readbacks の Trusted 導出がある。既存の親入力 Trusted を二つの実際の Shared update に沿って移す。
2. `terminal_settled`：追加仮定なし。実際の `observed.current` で正確な stored producer `candidate` が PacketSettled。記録済みであり、children が空であることから導く。
3. `input_variables_empty`：追加仮定なし。candidate の inputSchema.variables は空。inputSchema 全体を任意に空と仮定したのではなく実際の宣言から計算する。
4. `endpoint_observation`：任意の slot : Fin 5、identity : Nat、test、observation、assignment m について、slot = 3 または 4、旧 snapshot の Head identity test observation、identity = base.source slot、親 packet の Inputs m を仮定すると observation.Holds m。正確な nominal descriptor の読み戻しであり外側 tag だけではない。
5. `input_readback`：追加仮定なし。実際の observed と親 input 一個から candidate の Readback が成立。すべての実際の read slot、head observation、slice model に量化し、read list を [3,4] と計算して前項を使う。
6. `int_recipe`：追加仮定なし。candidate の実際の namedSchema には出力 target の scalar int Recipe が存在し、具体的な `intTerm` を使う。
7. `producer_output_trusted`：追加仮定なし。facts、readbacks、support が存在し、`Trusted observed facts readbacks` かつ `Fact.outputs candidate support ∈ facts`。実際に記録された support alternative を取り、親入力→producer入力→producer出力の Trusted constructors で構成する。

公開定義 `certificate facts readbacks` は任意の同 fixture の facts と readbacks に対する OutputCertificate。namedSchema.variables が空のため input/binder/use 義務は空で、実際の定数 int の recipe を提供する。任意の出力を扱う証明ではない。`parentInput` は親入力 fact の略記、`intTerm` は引数を持たない scalar int node。

## 検証

新モジュールと `Audit/Cycle167CapturedSettledProducerTrust.lean` を `--trust=0` で検証し成功。全7公開定理と certificate の公理依存は propext / Classical.choice / Quot.sound のみ。既存ファイル・意味論・guard は変更しない。full build は行わない。
