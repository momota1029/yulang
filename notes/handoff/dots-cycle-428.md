この周に閉じた C の行: なし。

# C428: 実際の where の子を元の選択証明に接続

開始: 2026-11-25 23:30:00.006 UTC。I-74/I-75、対象は C15 のみ。

## 検証できたこと

- 元の where の句番号・字句上の捕捉・保持済み compound 行を、既存の `SourceTrace.selected` の **同じ** `WhereForest` における実際の選択 Event に接続した。元の Request/occurrence を宣言 ID や同じ値から推測しない。選択の局所規則はモデルや望む結論を入力に取らず、同じ State の全適合モデルに辞書証拠を与える。初期 pin `f8434cdff8533ca1a9a7c803151bed613ada7195`。
- 本当に異なる局所規則を一つの木で使用した。元の親 [71] は、原構文の構造 where 子 [71,0]（元の配置 4、宣言 219）と、別の原構文の変数 where 子 [71,1]（同じ実捕捉 3、宣言 88）をこの順で出す。後者だけが元の宣言済み再帰 nominal 90 を読む既存の Named409/R13。前者を旧 named 子に見せかけると通らない。同じ実適合モデルがあり、どの適合モデルでも辞書 218[219,88]。この実例に support 依存・要求出力・書き込みはない。pin `1e0bd973f56d11140fac50eba8421201c47b8691`。
- 既存の検査器が実際に返した後者の証明をそのまま使い、その Event が親の第 2 子に残ることを確認した。一般の既存 support についてもルール包含で元の producer occurrence、出力 ordinal、型つき receipt、固定先を保持する。これは C15 に新しい出力例を増やすことではない。pin `f36d32a35c3acbeb7c2f267fd21c040861c7eba7 / 10be463dcb8cf34a60c8d628e36a9e6088268828`。
- 検査済みの元の親 frame から両子を順序通りに読む、独立した実行可能な body reader を検証。証人は保持済み行などの位置だけで、子 Request、捕捉、結果は渡さない。行・宣言・nominal 根拠を取り違えると通らない。C426 統合後の **現行 R14 公開入口** で、実際に復元した旧 named 子 [71,1] を検査して通過を確認した。C15 の親を受理する公開分岐はまだない。pin `133b25c6b4058b35e95e6658fd50b7f7de217ede`。
- C429 に向け、C427 の実 same-role ordinary rival は既存の declared-app 専用候補テープでは表現できないことを厳密確認。実 singleton の親および構造子は既存テープの必要条件を満たし、閉じた変数付き record 子の実 raw Visit は根だけ。いずれも言語上の拒否・受理範囲の拡張ではない。`b398f7750454a904d7c2770d5ae0004c2086f603 / 894085840b595bf14c7ee4cf4e4e7d2cc7249e99`。
- singleton の候補テープから元の宣言・登録順・字句捕捉を復元する既存証明を実行。compound の配置は独立に与えられた元の根拠であり、公開アロケータから導出したものではない。pin `639014c7bb663dc10a1182a59d6ae4bff0c98aa1`。

## 統合と検証

統合は途中で `34ece1698e5b8369f08e8d22e028a78d900e1594` に進み、C426 canonical R14 の exact Lean tree `efac6836b560e3180f253b5fc37b92ebbfafe9bd` と実ソースを確認した。`integration/types` は `1b9361bb6dfca0642ee7d7e149e2e224bff535c0`。今回は R15、公開 root checker、固定 `check_sound` は変更していない。C427/C428 は未統合。

公開 Lean tree `56cbf88db87b0f7aceacbf7661e1bf0baa41ec30`。追加 7 モジュールの exact import を C425 と C426 の両環境でまとめて検査。新規監査 9 ファイルを依存順（他の Audit の事前ビルドあり）で実行、Lean 4.35.0 `--trust=0 -DwarningAsError=true`、標準公理のみ。公理表示は C425 58 件・C426 60 件（再監査を含む）、既存 R14 は別途 10 件。 既存の R14 射影例の元監査も exact 再実行 PASS。既存 Lean ファイルは import barrel の末尾追記のみ、凍結ファイルは blob ID のみ確認。Rust、全体ビルド、網羅性、停止性、NoFalseRejection は対象外。

## I-76: 独立監査の制約

最終読戻しで inbox `6dea808d4bab26c49ecc5a403048a80e430ea8d6` の I-76 を確認。Audit は `Yulang.*` のみを import でき、事前ビルドした別 Audit に依存する実行は統合条件を満たさない。C427 の Forest、Readback、Visits の 3 件に加え、C428 の新規 9 件中 7 件に該当。該当依存は以下のとおり（ソース検査）。この周はこれらを単独で通るとは数えず、既存ファイルは変更していない。

- `Cycle428I74StructuralWhereBodyReplay.lean` → `«Cycle428I74StructuralWhereMixedSibling»`
- `Cycle428I74StructuralWhereIntegratedLegacy.lean` → `«Cycle428I74StructuralWhereBodyReplay»`
- `Cycle428I74StructuralWhereLegacyTrace.lean` → `«Cycle428I74StructuralWhereMixedSibling»`
- `Cycle428I74StructuralWhereRootFrame.lean` → `«Cycle428I74StructuralWhereMixedSibling»`
- `Cycle428I74StructuralWhereSingletonTape.lean` → `«Cycle428I74StructuralWhereMixedSibling»`
- `Cycle428I74StructuralWhereTapeBoundary.lean` → `«Cycle427I74StructuralWhereSameRole»`
- `Cycle428I74StructuralWhereTrace.lean` → `«Cycle427I74StructuralWhereForest»`

## 次

I-76 が次周に明示した作業は、まず C427 の 3 監査を修復し、共有部分を `Yulang.*` に置いて各 Audit を単独で strict 実行すること。C428 の 7 件も別途同じ制約に沿う必要があり、変更範囲はその時点の指示に従う。以下の R15 準備は監査修復後のために保存したもので、次周の優先順位ではない。

[採用済み R14 からの手順](../design/dots-cycle-428-c15-next.md) と [singleton の検証](../design/dots-cycle-428-c15-singleton-readiness.md)。C15 の実構造 where について、独立局所規則と `DictionarySound`、公開の data-only 分岐、固定形の `check_sound` の三つが同時に通ったときだけ閉じる。distinct-role singleton を same-role X10 と報告しない。同じ role が必要な場合は実 ordinary rival の狭い規則を用い、固定テープの欠落を拒否としない。

**C の残り: 8 行（C15–C22）。**
