# C412 / I-74 C04: X10 の候補内 record visit

§6.3 X10: `impl Check {box: {tick: 'a}} where Check {box: 'a}` / `Check {box: μ}`、`μ = {tick: μ}`。親の実 point に本来の outer record 観測があり、その `box` field の実 payload 名を元の raw row から得る。候補の head はその field に**構造のある** `{tick: 'a}` を書いているので、その箇所を実際に開く（単なる変数・違う field・open tail を見たのとは別）。そこで同じ無濾過 graph の raw cycle。親 root に raw 帰路なし。発生したのは候補 head の診断であり、where は実宣言にあるが成立した選択も生成した子需要もない。

- `ActualRecordField` に元の唯一の可視宣言・実 role・正しい declaration/descent・元の point と同じ field の raw 行を記録する。証人やモデルの成否は宣言規則の前提ではない。候補内の exact `Visit.field (.here .record)` から同じ site の `PatternK2`。新規 `other` rule のみを R3 に足した R4 に固定 `DictionarySound`。
- 実行証人は元 origin ordinal と元 root row ordinal、旧 parent escape、raw `checksHop/close` の cycle データ。判定対象の site は実 field から導き、子 `Problem` や where 需要を作らない。既存入口は同じ。
- 固定の exact Result は `rejected` tree、`rejected` verdict、書込み空。対して C03 は selected parent の実 where tree だった。子の循環を親根の K2 に置き換えない。R4 の元 trace と全 fitting model の ReportEvidence を保つ。

この確認点では独立局所規則、R4 の soundness、真の nested record Paterson（任意の置換後含む）、旧 report の移送を strict Lean + 独立 Audit で確認。新しい data branch と同じ X10 実例の照合は次。
