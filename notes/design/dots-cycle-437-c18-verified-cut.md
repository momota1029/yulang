# C437 / I-79: 検証済みの lower・producer・scoped consumer

入力は正本 `integration/m1-final@fdab22303a5b928c1af2f87458da7a55dd12b04c` の Lean tree `6b1fa7520125ad7a50797c9d0cf4c6083a3f66a6`。技術成果の work pin は `ed7e39f81d521b556dd37962b3b4baa5cb9b2351`、Lean tree `07eaa114f990a25365054ea6bd17ddc2b4ad46c2`。この周で C18 は閉じない。

## 実際に検証した層

- **native metadata。** 実際の source body から `Box` を covariant と再生し、legacy explicit header は false、native header true。同じ snapshot に invariant flag を足した対照と、宣言 ID の重複も false。新しい helper は構成子スコープの根拠だけを native coverage から作り、旧署名・識別・lexical・descent の確認を捨てない。
- **保持行と元 B6 の意味。** `Payload` は typed receipt、固定先、文字どおりの行の ordinal/code を保持する。上位の `lower_retention_uses_original_B6_value437` は任意の同一適合モデルで、原 request/宣言/出力/body の typed plan が評価する値と固定先の値の意味的同値を結ぶ。lower の `nativeSyntax` を用いない。実試験では原 occurrence [101] と宣言 ordinal 0 を読む。別 occurrence／宣言番号、および同じ target・同じモデル値を持つが本文が `Box(32)` の別行は、元の `Box(30)` の代わりにならない。
- **別需要 Seed の実際の完了。** 実原 role/declaration を一候補の tape で選び、元 B6 frame と同じ `Event` を作って、`SourceTrace.selected` を得た。 `readOneOutput` は思いついた辞書を照合するのではなく、独立に取得した Seed basis と元 typed output から行を実際に検査して `SupportForest` を組む。row #0 で [101]／decl=0／output=0／target=40／row=0、同値だが別字面の #1 と不存在 #2 で失敗。実適合モデルで Seed の辞書と lower の値を同時に得た。
- **同一状態の scoped Observe。** Seed の exact support が L40 を支え、上端は独立原記録 U42・issuer [303]。L に authored route がないことも実データから証明。選択後に元記録 C41・issuer [202] を読み、payload span (30,32,34) を保つ。実適合モデルでは `nativeSyntax 40 = none` で、Seed の辞書・固定先の値・Observe の scoped 意味が同時に成り立つ。中心 reader は正しい #1、真の上端 #2、**中心と同じ物理名・構文でも異なる issuer [999] の #3**、不存在 #4 を区別する。
- **raw K2（意味を仮定しない対照）。** 元 raw graph は Observe の root40 safe。row #2 に `30=40` 一個だけ足した raw graph では実 `Cycle350` witness が通って root K2。Seed root10 は両 raw graph で safe。改変 raw graph に適合モデルがあるとは述べず、旧 public dispatch の再証明としても数えない。

## 検証

公式 Lean 4.35.0 の `--trust=0 -DwarningAsError=true`。新 production 5 本を個別 `.olean` にビルドし、独立 Audit 7 本を空の作業場所で production-only module path を使って別々に確認（全 exit 0）。公開後、同じ Audit の Git 内容を再取得し、独立な `lean --stdin --trust=0 -DwarningAsError=true` を同じ production-only import 群で一つずつ再実行（全 exit 0）。C437 の比較に必要な既存94本（58 + 33 + 3）も immutable Git の各 blob と照合し、個別 strict compile。古い cache については scoped source graph の 3,789 本が正本 Git bytes と一致し、`.olean` の存在と時刻を確認したが、全件を新規 build したわけではない。全体 build、Rust、NoFalseRejection、停止性は未実行・対象外。

Audit の import: `Yulang.*` 以外 0 件。36 行の公理出力はすべて `propext` / `Classical.choice` / `Quot.sound` の範囲だけ。frozen 2 ファイルは Git metadata の blob ID のみ確認、どちらも不変。旧 `Yulang.lean` は完全な旧 bytes を prefix とし、今回の 5 imports のみ末尾に追記。既存 production/Audit 本体・spec・integration branch は変更しなかった。

| production | 検証 bytes blob |
|---|---|
| `lean/Yulang/GeneralDeclarativeI65I74CompletedLowerCenter437.lean` | `a41f1c9ef4d5b9ccc3a21f80b5d13c60cbfe611a` |
| `lean/Yulang/GeneralDeclarativeI65I74CompletedLowerNativeHeader437.lean` | `bd33069284de0bede70e0e159cc491b543013529` |
| `lean/Yulang/GeneralDeclarativeI65I74CompletedLowerPayload437.lean` | `12c970f8dab79c7a089ded26b5771f4040b356e1` |
| `lean/Yulang/GeneralDeclarativeI65I74CompletedLowerRetained437.lean` | `89578ca0282859455cf83341589c71ee5d07005e` |
| `lean/Yulang/GeneralDeclarativeI65I74CompletedLowerSeed437.lean` | `1031f22ea6a046b6a2d2ae04e31210a37c0d2a8a` |

| standalone Audit | 検証 bytes blob | 公理出力 |
|---|---|---:|
| `lean/Audit/Cycle437I74CompletedLowerCenterReader.lean` | `a4f99a7035c8d27c2e8c112ff970f1d7a9aa91ce` | 4 |
| `lean/Audit/Cycle437I74CompletedLowerConsumer.lean` | `a834fcec9376335dc542b6419560890efcc0b1aa` | 8 |
| `lean/Audit/Cycle437I74CompletedLowerExactFixture.lean` | `de7069a9afac496e8327b0e2a4e0631f194c80a0` | 4 |
| `lean/Audit/Cycle437I74CompletedLowerNativeHeader.lean` | `29df5511b06b2d95b04711860a84390032a21928` | 6 |
| `lean/Audit/Cycle437I74CompletedLowerRetained.lean` | `21d5951b09bbc070aaeedf5a592a0d2c952f0662` | 3 |
| `lean/Audit/Cycle437I74CompletedLowerSeedReader.lean` | `9f8854068b4968120c000d8da3ae53e29a7203e1` | 5 |
| `lean/Audit/Cycle437I74CompletedLowerSelectedSeed.lean` | `b80b1f583886c7d3f9c47341378499a0d0b7bd0a` | 6 |
