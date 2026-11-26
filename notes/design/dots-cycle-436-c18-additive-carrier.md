# C436 / I-79: C18 の追記だけの carrier

対象の正本は `integration/m1-final@a6c7ed28f3f9656cc23c15ccc49ec3caf98d360e`（Lean tree `6b1fa752…`）、I-79 は inbox blob `63620853…`。spec §6.3、`spec/06-roles.md` blob `2732b1d7…` 182–226 行: 片付いた別需要の出力は head の根拠となり、未完了の式も raw K2 から除かない。実装の枝だけを増やす。以下は source を照合した**設計**であり、Lean の型検査結果ではない。

## 変更しない境界

`GeneralDeclarativeI65I72FixedGoal402.lean@8ebefffe…` の `classification_has_exact_lane_rule426` (134–141) は全 `lane` の分類が旧 named または旧 projected のいずれかであると示す。C435 で確認したとおり、実際の C18 正例はどちらでもない。従ってそこに第三の `PrimitiveLane426` を単純追加する案は、単に case が減るのではなく、既存の定理を偽にする。旧 `SourceHead` へ payload を押し込む案も named の `Event.head` を要求する既存の producer inversion を壊す。旧ファイルや定理を弱めない。

新しい上位モジュールの namespace に `Classifies R18` / `DictionaryEvidence` / `DictionarySound` を置く（ここでの `Classifies` 等は新モジュールの名前で、I72 の旧定義は同名で不変）。`R18` は `PendingAssociated434.R17` と一つの独立した completed-native source rule の和。旧 lane に対しては縮約が既存の named/projected の枝へ戻る。和から旧分類を逆抽出する補題は「`.previous` witness を実際に選んだ場合」にのみ置く。新定理の文は同じく `∀ s q d, Classifies R18 s q (.selected d) → ∀ m, Fits s m → DictionaryEvidence s m q d`。同じ `State/Request/Model/Fits/Result/Dictionary` を用いる。C406 の汎用 `ScopedEvidence406` を canonical と称して使わない。もし既存の型定数そのものに第三の構成子を入れる指示が別途必要になれば、I-79 の停止条件に従い上の旧分類定理を指し、**編集しない**。

## import の向き

```text
B6MixedLexical401 (7db6d0b9…) and common syntax/model
       ↓
CompletedLowerPayload436 (new, no FixedGoal402, no SourceTrace)
       ↓
CompletedLowerSource436 (new, may import high 402, 404/405/406, R17)
       ↓
CompletedLowerEntry436 (new, may import proof-producing readback)
```

下位 `Payload436` は `NamedMixedReceipt401 core`（実際に occurrence、declarationOrdinal、outputOrdinal、original、slots、typed RHS を持つ）、consumer lower L、同じ ordinary equations 上の明示した row ordinal、およびその `getElem?` 等式を索引とする。「この receipt が誰かに選ばれた」は一切入れない。`TypedCovariantPoint404`、`fixedValueCode403` をここへ import するとその定義ファイルがすでに `FixedGoal402` へ戻る。そのため型つきの構成子／kind／mode／point の検査との接合を**上位**に置く。下位に value expression の列を足して nominal の型つき項に読み替える方法は採らない。下位で `actualEquation` を使い `LowerMeaning` を定義してよいが、その値と raw Expr の関係は上位で証明する。

上位 `CompletedHead436` は、同じ State の **具体的な** `SourceTrace PriorSource406 s producer t (some e)`、同じ診断木への `Summarizes t (.selected d)`、producer の有限な元の出力番号 `i`、および `(e.outputs i).receipt` に索引付けした同じ下位 payload を持つ（producer は consumer の**同じ要求ではない**ことを元の occurrence で確認）。`OutputNeed` を `needOfSelected404 e d i` でその場で作り、`SupportForest.cons trace summary rfl .nil` と `atOriginal 0 rfl` を使う。ユーザーの報告やお仕着せの receipt、実行版 release/authority は構成子の前提にしない。新しい head/evidence の形はこの一つ。最初の実際の coverage は旧 C405 の有限 producer と新しい singleton unary leaf（consumer の出力・where が空）に制限できる。旧例を排除せず、別 producer の完成は許可済みの有限 derivation による。

## 同じモデルでの厳密な結合

1. 元の `e.outputs i` は B6 atlas の同じ request、宣言番号、出力番号、本体、型付き項の証拠を持つ（`NamedMixedOutput401`）。`need.expected` はこれと定義的に等しい（または `ExactOutputSupport.sameTypedOutput` で輸送）。
2. 新規の row ordinal `j` について `s.core.current.ordinary.equations[j]? = some ⟨L,code⟩`。これは単なる等式の denotation ではなく文字どおりの保持行。型が違う、target が alias 上だけ一致する、producer occurrence/ordinal が違う場合は不一致。既存 `readOriginalOutput432` (blob `a109ef2c…`) はこの exact address を最初から返す。これなら高位の意味補題は一般の `KeepsFixedOutputs404 R17` を仮造しない。
3. 上位で `actual_typed_point_yields_literal_declared_code404` (blob `a0a0035b…`) により、同じ receipt の既存 typed point が `fixedValueCode403 … = some code` を持つことを確認。`fixed_value_code_same_model403` (blob `7f5292aa…`) を**実際の** receipt.rhs に適用すると、`actualEquation m = some (L,v)`（`v = value (environment m.assignment) .actual code`）。次に `List.mem_of_getElem?` で行所属、`fit.1.1.2 _ retained` で `Equivalent (m.assignment L).1 v`。これは `retained_typed_rows_satisfy_fixed_targets403` の一点版だが、別の選択された辞書・別の出力の存在量化に依存しない。
4. consumer の上端は authored route から普通に読み、source lower の m.nativeSyntax を読まない。両者の declared unary kind / variance と payload 比較を `literal_input_declares_mode_and_compares406`、唯一の候補の訪問 ordinal と raw 安全性を `completed_root_never_inspects_variable_payload406`、postselection の実際の中心だけを `original_payload_names_the_exact_native_capture406` で接続する。選択に実中心の既知の行を要求する言語規則は追加しない。中心の元の捕捉を別途再現できる部分だけ、この checker は対応する。
5. `DictionaryEvidence` の新枝は、選んだ exact head とその報告の同一性、上記 lower の実際の値と同じモデルの upper/interval/center、consumer の同じモデルでの元 body・fixed targets（試験片では全称が空）、旧 producer の実際の選択済み辞書の意味を一つの枝に保持する。後者は `authored_native_dictionary_reuses_given_trace405` (blob `887067e2…`) に、同じ trace と `Summarizes` を渡せる。別モデルに持ち替えない。producer は根拠であって consumer where 子や再発行の writes ではない。空の where と空の writes も実元データで確認する。

## 受け入れ前の独立したチェック

旧 witness の全入力 Bool 恒等は `check p r (.previous old) = PendingAssociated434.check p r old`、定義から `rfl`（有限の比較試験だけで代用しない）。新 witness は独立に読み直せる source coordinates と検査可能な raw-escape wire のみ。旧 `check_sound` の場合は既存の証明をそのまま呼び、根が raw K2 の場合は R17 の実際の拒否へ戻す。新しい場合は同じ exact replay、`ClassifiedAs`、全 fitting model の `ReportEvidence`。R18 の addition も report equality も Lean 未検証のため、今回の公開時点で C18 を閉じたとは数えない。
