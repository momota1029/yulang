# Cycle 3: whole-record rest result の後続 projection 境界、追加局所監査

## 範囲

旧 Y2 `d4c8bc8fc` の既存 release binary と source を read-only で調べた。新 spec は `816ed8f1d`。source の変更、ビルド、Lean 検証はしていない。既存の主張を修正する調査ではなく、前の実測失敗を局所化する対照実験である。

実測は 2026-11-08T13:38:20Z〜13:39:04Z。12 ケース×check/dump/run と、7 ケース×同モードの --no-cache 対照、計57 invocation、合計 command 時間 0.310033 秒。exit 0 は42件、非0は15件、timeoutなし。dump の exit0 を診断なし/成功とは読まない。完全な source、コマンド、UTC、elapsed、stdout/stderr は `rest-controls-raw.md` と `rest-no-cache-raw.md`、機械可読版は各 JSON。

## 確定した実測

元の失敗:

```yulang
our keep {x, ..whole} = whole
(keep {x: 7, y: "kept"}).y
```

check は0、run は compile error `unsatisfied subtype constraint: {x: 'open2} <: {y: 'open0}`。前のログに保存済み。

今回の対照:

|変形|run 結果|読み取れること|
|---|---|---|
|head spread `{..whole, x}`|同じ失敗|tail spread の順序だけには限定されない|
|spread のみ `{..whole}`|`{} <: {y: 'open0}` で失敗|明示 field を除去しても、plain identity と等価な後続利用にならない|
|`{x,y,..whole}` と要求 field を列挙|`"kept"`|元から列挙した field の利用は通る|
|`({x} as whole)` を返す|`{x:'open1} <: {y:...}` で失敗|spread 構文だけの現象ではない。ただし generic 表示は `{x:'a}->{x:'a}` であり、この表示型から y が導けないこと自体は矛盾ではない|
|input を case `{x}` で調べ input を返す|上と同型の失敗|関数引数 pattern だけには限定されない|
|case `{x,..whole}` から whole を返す|元と同じ失敗|case 経由でも再現|
|case `{x,..rest}` から別名 input を返す|元と同じ失敗|rest 名の参照だけには限定されない|
|default `{x=7,..whole}` と `{y:"kept"}`|`{x?:'open2} <: {y:...}`|optional/default でも再現|
|`our get r = r.y` に keep の返り値を渡す|元と同じ失敗|`.y` の直接構文だけには限定されない|
|即時 lambda 適用を直接 projection|成功 `"kept"`|同じ record pattern の binding と値アクセス自体は実行できる|
|lambda を `our keep = ...` に名前付け|元と同じ失敗|名前付き exported binding 境界との相関|
|即時 lambda の結果を `my kept = ...` に束縛してから `.y`|`{x:int} <: {y:...}`|多相化だけを唯一原因と呼べない|

最後の重要な対照:

```yulang
((\{x, ..whole} -> whole) {x: 7, y: "kept"}).y
// run roots ["kept"]
```

```yulang
my kept = (\{x, ..whole} -> whole) {x: 7, y: "kept"}
kept.y
// compile error: {x: int} <: {y: 'open0}
```

--no-cache でも named lambda、computed binding、head-only/rest-only の失敗と、直接 lambda / 両 field 列挙の成功は同じ。古いキャッシュだけによる結果という説明はこの対照に合わない。

実験上の失敗も保持した。top-level `my {x,..whole} = ...` は `whole` 未解決となり、対照として使えない。また `width-only-identity-y` の top-level `my {x}=...` は dump に残らないため、この行で実際に幅制約が課されたと主張しない。そのケースは単純 identity 成功以上の証拠に数えない。

## 文書と source で確認した事実

1. 旧 `web/docs/ja/reference/types.md:49-56` は whole input の例と明示的説明を持ち、generic 表示も `('a & {width:'b}) -> 'a | {width:'b,..never}` と明記する。新 `spec/03b-patterns.md:90` も spread は残りではなく入力 record 全体、と指定する。generic 表示を今回新たに異常と認定してはいない。
2. 旧 `crates/infer/src/lowering/pattern.rs:565-581` の `lower_record_pattern_spread` は、binding を元の `record_value` に結び付け、その後に独立した fresh `tail` を返す。同 `472-489` は明示 field とこの tail から正の RecordTailSpread/HeadSpread を作り、value に lower 制約を追加し、明示 field の record を upper に課す。spread binder を明示 field を引いた残余に束縛しているコードではない。
3. 旧 `crates/specialize/src/types/materialize.rs:91-109` は正の spread の tail が Type::Record の場合だけ field を足し、それ以外は明示 field だけの Type::Record を構築する。従って表示上の `{x:'b,..never}` がこの処理へ入る場合、明示 field のみの record に具体化される構造が source 上にある。
4. 旧 `crates/specialize/src/solve/constraint_graph.rs:327-329` は Union の両成分に上限制約を課す。`'a | {x:...}` の record 側から `{y:...}` への失敗はこの構造と整合する。ただし本実測の例外がこの呼び出しを通ったことのトレース、materialize の実引数、簡約順序は採取していない。この2箇所を根本原因確定や修正箇所確定と呼ばない。
5. 旧 `crates/specialize/src/specialize2/task_solver/control.rs:473-535` の record binder は spread local に元の `ty` を保存する。旧 `crates/mono-runtime/src/runtime/bind.rs:191-205,274-289` も spread binder に元の record_value を保存する。runtime で余分な field を意図的に取り除く説明より、名前付き型境界・型具体化/制約に調査を寄せる材料になる。実際にどの runtime 系統で評価されたかは今回 instrument していない。

## 結論と未確認

旧 Y2 では whole-record の値をその場で使うことと、名前付き定義/計算結果の境界を越えて余分な field に射影することに差がある。全体 binding の runtime 意味そのものが壊れた、とするより狭い観測である。「同じ正の record lower が返り値に残り、名前付き scheme/型具体化後の利用で要求 field を満たせない」という局所仮説は source と実測に整合するが、根因の確定ではない。

新 Lean でこの surface 全経路が接続されているとは確認していない。`CommonSourcePatternTyping.RawTyping.field` の rest が同じ input を受ける局所規則と、旧 Y2 named-binding/inference/run の接続は別問題。新 spec の一般的完全性の反証とも、新 Lean の誤りとも宣言しない。次の独立作業は、旧Y2の generalization/export と materialize の実引数・制約発生点をトレースするか、新モデル側に具体的な source test を移植して検証すること。修正・仕様決定は本監査の範囲外。
