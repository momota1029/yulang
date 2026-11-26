この周に閉じた C の行: なし（C18 は未完了）

# Yulang cycle 436: 完了した別需要から native head を支える枝の設計

I-79（inbox blob `63620853fb52ce1319c2bd85d2b42b2cca7b2e72`）に従い、C18 のための独立した分類・head・辞書証拠の形を、追記だけで足す設計を進めた。基準は正本 `integration/m1-final@a6c7ed28f3f9656cc23c15ccc49ec3caf98d360e`、Lean tree `6b1fa7520125ad7a50797c9d0cf4c6083a3f66a6`。C17 は正本に採用済み。他の統合ブランチには書いていない。

## 今回確かめたこと

1. [追記だけの carrier](../design/dots-cycle-436-c18-additive-carrier.md) と [分類・辞書・報告の同一索引](../design/dots-cycle-436-c18-entry-contract.md)。旧 `classification_has_exact_lane_rule426` は旧二枝を全称で尽くす定理なので、旧型に第三枝を足して既存の定理をそのまま残す案とは両立しない。既存二枝の型・意味・定理は変更せず、旧 R17 と新 C18 leaf を上位の和にする。低い payload は旧 B6 語彙だけを import し、同じ State の有限な selected SourceTrace は上位で照合する。I‑65 と同じ量化・前提・結論の外形、および `previous` の全入力 Bool 同一性を残す設計。
2. [native header の障害と差し替える一つの証明欄](../design/dots-cycle-436-c18-native-header.md)。旧 `RoleDefault420.checkHeader` の `explicitCheck` は primitive か invariant を要求する。実際の declared Box は **同じ snapshot で両方の flag がない**ことが必須で、この旧ヘッダでは通らない。新 helper は `Header349.checkedRegistry` の署名・ID・lexical/where descent の検査を保持し、`DeclarationChecked.constructorScoped` だけを native `ModeCoverage357` / `ModeDeclaration357.scoped_decl` から組む。既存ヘッダの動作は変えない。
3. [証人から元の producer を作る手順](../design/dots-cycle-436-c18-proof-producing-reader.md) と [元の B6 plan と保持先の同じモデル上の値](../design/dots-cycle-436-c18-same-atlas-value.md)。同じ有限 producer Event の元 request、宣言番号、出力番号、body で atlas を読み、実 raw row locator と完全一致する時だけ、保持先 L の値がその元の B6 出力に等しいと示す。L の authored native syntax を捏造しない。宣言番号は high 側 event.frame.ordinal にあり、低い `NamedMixedReceipt401` にあるわけではない（後者のノートで明記・訂正）。
4. [旧候補診断との重なり](../design/dots-cycle-436-c18-inherited-priority.md)、[意味が同じ別行の対照](../design/dots-cycle-436-c18-exact-fixture.md)、[検証順序](../design/dots-cycle-436-c18-focused-verification.md)。試験片は元入力一つ・可視の unary 選択一つ・consumer の出力/where なし。旧 R17 pending は元の子の出力一つを要求するため、この片とは重ならない。さらに [結果の競合がないこと](../design/dots-cycle-436-c18-result-confluence.md) を旧 trace の三構成子と新 singleton の同じ結果から紙上で導いた。保持行 #0 `40=Box(30)` と別行 #1 `40=Box(32)` は同じモデルで同値でも、元 B6 本体から出るのは #0。#2 `30=40` だけを加えると consumer の raw K2 となる。該当する exact escape と raw witness の数値式を限定データで照合した（Lean/Rust の実行ではない）。producer を consumer の子・再発行 write に数えない。

## 検証と次の手順

- cloud computer が offline。Lean 4.35.0 の focused build、`--trust=0`、独立 Audit、実 public checker の正負試験は**未実施**。I-79 の新 Lean を公開していない。新規設計文書 9 本、報告と heartbeat のみ。期待 head を検査した non-force 更新と、公開後の Git 内容・変更パス・Lean tree／凍結ファイルの blob ID を照合している。フル検証、Rust、NoFalseRejection、停止性、C19 は対象外。使用量の枠は不明。
- 復帰後の順序は (1) lower payload と native header の strict Lean、(2) 元の typed producer と raw-first consumer のデータ reader、(3) 実 `dictionary_sound_R18`、public check 新枝と旧 Bool の全入力同一、同じ外形の `check_sound`、(4) exact Git と独立 Audit。三条件は今回いずれも新 Lean で通っていないので、C18 を閉じたとは数えない。

**C の残り: 5 行（C18–C22）。** 実開始 07:32:47.506 UTC。50 分の通常ゲート後に報告し、sole writer を解放。
