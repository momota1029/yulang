この周に閉じた C の行: C20（`NestedInvariant440.dictionary_sound_R20`、`NestedInvariant440.check`、`NestedInvariant440.check_sound`）

# cycle 440 — 入れ子 nominal head の invariant 文脈

実開始: 2026-11-26 11:30:16 UTC。通常の 50 分ゲート後に終了報告を作成・公開。経過の定値と canonical release は同じ commit の heartbeat を参照。使用量の枠: 不明。

## 元の依頼と得られた範囲

I‑74 の一行のみ、I‑78 / I‑79。元の C423 C20、spec §6.5 L431–435。開始時 `integration/m1-final@1d2084ac7278aa7b9eb29eea86caaf740a7bc567` の Lean `3fa551ff461d24ab106f9dca1f55cdefd742b49e` は前周 C439 exact 採用。旧 C19 は再実装していない。

実在する可視候補一つ、元の `Outer(Inner 'a)` の宣言と二つの authored 原点、名前付き raw 位置、where および固定出力なしの葉を、モデルなしで `nestedLocal` が選ぶ。外側は unary invariant、内側は unary value の実宣言 invariant / covariant / contravariant。内側は継承した invariant 区間として判定し、元の下端・中心名・上端を保つ。端点比較は中心値を使わない。当該 scope は同じ outer head の interval syntax を元の上下端に持つ場合に限る。

1. `actual_nested_selected_trace440` は元の候補 tape から同じ状態の literal named trace、元の preoutput capture、空の child/output を出す。`nested_only_dictionary_sound440` は既存 `I72.DictionarySound` と `DictionaryEvidence.node` を用いる。 `dictionary_sound_R20` は、全ての元 state/request/dictionary と fit モデルに対し、新旧各規則から同じ固定辞書証拠（既存 R19 と同じ evidence carrier）を返す。
2. `check` の追加分岐 `.nested` の wire は原点・raw 行の元の索引と二つの有限 raw escape データだけ。答え・scope/type proof を埋め込まない。`all_previous_R19_Bool_unchanged440` は任意の元 Problem/Result/旧 witness に対し旧 Bool と同じ。raw root K2 が優先し、実際に調べる内側 site と変数で捕捉するだけの循環の位置を区別する。
3. 固定外形 `check_sound` は、任意の Problem/Result/Witness で Bool true なら元の同じ state/request の分類と、全てのその適合モデルで元の報告の意味を与える。元の root と内側の authored syntax、同じ捕捉の端点の意味と実際の中心の範囲を保持する。既存 theorem / carrier / checker の定義の書換なし。

[実入口の詳細](../design/dots-cycle-440-c20-verified-entry.md)。正例の各 source は invariant list/list、list/covariant box、list/contravariant constructor。各実入口で正に検査し、同じ実中心名が異なる値をもつ二つの適合モデルを構成した。外側の invariant を legacy flag でなく再帰 list body から算出する実入口でも三種が true。別 raw 中心名の候補を許す場合、[同じ適合モデル内では両中心値同値](../design/dots-cycle-440-c20-wire-coherence.md)（異なる名を等置しない）。元の候補・K2・誤った mode/原点/行/報告も実入口で対照。

## 比較、限界、次の範囲

- [二つの元の異なる区間の実コンパイラ比較](../design/dots-cycle-440-c20-exact-crossings.md): 任意の端点名で出力は順序付き 16 atoms（親の 4 比較の各々で内側の両区間と交差 2 つ）。同じ full model で scalar Int と Float を端点に与えれば両立しない。literal Float source が直接同じ `TyTerm` に収まるとの主張ではない。
- [有限なら任意長の共有 unary 接頭辞](../design/dots-cycle-440-c20-arbitrary-inherited-prefix.md): used-value mode のたび inherited invariant が残り、余分な k 層の実出力は 4^(k+2)（重複込み）、必要十分な同じモデルでの比較は 4 種のまま。実コンパイラ 3 追加層で 1024 行を確認。これは比較 backend の定理で、dictionary checker を任意深さ化していない。
- [二つの source 端点に対する固定捕捉の境界](../design/dots-cycle-440-c20-distinct-origin-boundary.md): 区間が重なるだけでは、両者の端点を一つの現行 `DeepRead` binder に同値として保持できない具体例を確認。対象を unchecked 言語拒否にはしない。
- X14 の literal source interval merger/solver、X17 の関数 source 簡約、全ての幅・深さ・候補や任意 where/output、Rust と証人生成・停止性・完全性は未検証または範囲外。新しい仕様判断をしていない。質問ノートなし。C21・C22 には着手していない。

## 検証と公開

- 科学 pin `edaebd19d22cd90ee6b7ae7cfce675ae4b2eb578`、Lean tree `5d57993d91ace99c523aaca4b6d8804d4b1498aa`。公開用 7 production / 8 independent Audit を immutable Git bytes から再取得・照合して `lean --trust=0 -DwarningAsError=true`（公式 Lean 4.35.0）で各々 exit 0。Production は `-o` を依存順に、各 Audit は別 clean dir + production-only oleans で検査。Audit 45 件は標準公理のみ（1 件は公理なし）。4,089 既存 focused dependency source provenance は正本と完全一致。全体 build、`tools/verify-lean.sh`、Rust 検証は dot では実行していない。
- Audit の import: `Yulang.*` 以外 0 件。[完全な axiom 出力、Git blob 表、実入口の対照の再現](../design/dots-cycle-440-c20-verification.md)（検証ノート blob `f24253a5a36b54ed5a23786f9756bb63ac1f58ec`）。
- 既存の Lean/notes の行は削除・置換なし。固定 `Audit.lean`/`README.md` は ID のみ確認。barrel の元の 375,527 bytes の後ろに 7 imports を追記。公開差分: **26 paths**（7 production、8 Audit、barrel、8 今周 design/検証ノート、canonical report と heartbeat）。期待先頭に対する nonforce のみ、`work/dots-main`。書き込み後に両方の末尾 canonical files と Lean SHA を再取得照合。専属 worker を解放。

最終照合時の正本 `integration/m1-final@1d2084ac7278aa7b9eb29eea86caaf740a7bc567`（Lean `3fa551ff461d24ab106f9dca1f55cdefd742b49e`）に C440 の exact 15 blobs はまだ揃っていない。C20 の scoped 完了は `work/dots-main` 上。正式取込・監督役の全体検証は別。

**C の残り: 2 行（C21・C22）。** [coverage 一覧](../design/dots-cycle-440-c-coverage.md)
