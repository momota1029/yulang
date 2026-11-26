# C438: C18 完了した別需要の native lane

対象は I‑79 の C18 のみ。正本は `integration/m1-final@0512c698732a0aeeb444f869f586bccc0a15866d`（C437 と Lean tree が一致）。C17 以前の既存定義はそのまま保存する。

- 宣言的判断: `Classifies18 R17 s q r` の旧分岐は旧 `Classifies R17` そのもの。新分岐は実際の有限の `CompletedInvocation406 s q []` と、その **同じ SupportForest** 上の producer に関する元 B6 出力の payload。producer の発生箇所は consumer と異なる。payload は出力番号を含む receipt と固定先に indexed、保持行番号と literal equality を持つ。新分岐は狭い leaf の独立規則、一般の範囲を広げない。
- モデル入りの証拠は別定義。元 B6 atlas/read の ordinal、plan 評価、同じ lower への retained equation、同一モデルでの値の同値、および独立の upper と選択後の元 center を示す。lower の authored syntax は要らない。root raw K2 は旧ルート、正例には全実根の raw 非循環を要求する。
- 新 wire は元 producer request と出所/保持行/upper/center locator、二つの検証付き raw root escape データだけ。元 header/book のリスト全体から唯一の該当候補を読む；出所は origin の字面と issuer、固定値は元 B6 atlas と実 retained row で検証。出力を持たない consumer の範囲だけをまず扱う。名前や宣言選択、proof、予想結果は wire に入れない。未対応は `false`、言語拒否は導出しない。既存 witness は何も変換せず旧 checker に渡し全入力で Bool 等式を証明。
- 狙う形: `∀ s q d, Classifies18 R17 s q (.selected d) → ∀ m, Fits s m → DictionaryEvidence18 s m q d`。check は結果の Tree／verdict／空 write を照合、check_sound は Classifies と全適合モデルの ReportEvidence を返す。producer の保持済み出力は consumer の新規 write に数えない。未検証の考案は closure と数えない。
