# Cycle 3 record-rest と親roleの受理対照

基点 `816ed8f1d` / Y2 `d4c8bc8fc`。実行全文はruntime-cycle-3-completeness、rest-controls、rest-no-cache、parent、parent-fixed。詳細根拠はcompleteness-cycle-3とrecord-rest-boundary-cycle-3。

| ID | 出典 | 規則 | 例 | 実機の結果 | 新 spec | Lean | 分類 | 備考 |
|---|---|---|---|---|---|---|---|---|
| C3-REC-01 | types.md49–56、patterns.md record spread | record restは入力全体 | `keep {x,..whole}=whole; keep {x:7,y:"kept"}` | check/poly/run0、両field残る | 3b.3 | CommonSourcePatternTyping.RawTyping.fieldはrestにも同じinputを渡す | 一致 | whole保持の局所規則と一致。 |
| C3-REC-02 | 同上 | rest返値の追加fieldの後続利用 | `(keep {x:7,y:"kept"}).y` | check0、run1 `{x:'open2} <: {y:'open0}` | 3b.3のwhole入力。採用されるschemeとのsource接続は別途必要 | RawTyping局所exactnessから全surface完全性を導かない | 未確認 | 値が保持されることと型境界を越えた追加field利用に差。一般化された型の選択まで仕様がこの例に一意に保証するかは未証明、単なる新Leanの欠陥とはしない。 |
| C3-REC-03 | infer lowering/pattern.rs565–581 | 直接lambdaと名前付き計算結果の境界 | `((\{x,..whole}->whole){x:7,y:"kept"}).y` 対 `my kept=(...);kept.y` | 前者run0:"kept"、後者run1。--no-cacheでも同じ | 4.7、3b.3 | source generalization/exportとの橋渡し未確認 | 未確認 | 多相化だけが唯一原因とはいえない。キャッシュだけの問題でもない。 |
| C3-REC-04 | 同上、specialize2 control.rs473–535 | rest fieldを要求に明示すれば通る | `keep {x,y,..whole}=whole; (keep...).y` | check/poly/run0:"kept"、head rest/only rest/default版の追加fieldは失敗 | 3b.3 | independent pattern入力の局所規則のみ | 一致 | 列挙済みfieldの受理対照。拒否群の根本原因は動的traceなし。 |
| C3-ROLE-01 | role-system/method-selection、X3–X4 | 実producerの関連型を使い複数の子whereを満たす親を実行 | `Produce seed.value=int; Parent(box a) where a:Left, a:Right; (box{value:seed.produce}).parent` | check/poly/mono/run0:(11,22)。where LR/RL両順、generic consume、結果注釈ありで同じ | 6.3、6.4、X3–X4 | finite role driver/local exactnessはこのsurface経路の実機検証とは別 | 一致 | 子を実bodyで使う具体受理候補。未知区間の普遍的安定/兄弟再生成を実測したという意味ではない。 |
| C3-ROLE-02 | 同上 | 必要な子roleを持たないreceiverでは親の利用不可 | `box{value:seed}` でParentを利用（seedにLeft/Rightなし） | check/mono/run1 no role implementation、poly0だが診断あり | 6.3 where前提を満たさない | role核の前提保持をsurface検証したわけではない | 一致 | 明示した子制約による拒否。最初にuseを関数名にした誤構文は別rawに残し規則の拒否に数えない。 |
