# `Core.infer` が覆う構文と、全構文への距離 (2026-11-07)

状態: **棚卸し。決定は無い。** ユーザーの要望: 「すべての構文に対応してほしい」。
署名: Claude (Sonnet 5.5)。根拠は `integration/m1-common` の先頭 `42d023f78` の Lean ソース（`lean/Yulang/CoreExpr.lean`、`CoreInference.lean`、`CorePresenceGenerationCore.lean`）。
証明の中身は読んでいない。宣言（構文の定義と型付け規則）と、ビルド・Audit の通過だけを確かめた。

## 現状

公開入口 `Core.infer` が型付けの根拠にするのは、`Core.Typing (PresenceGeneration.CoreRules.model Common.model)`。
入力の構文は `Core.Expr`（構成子 31 個）で、この判断が規則を持つのは 14 個。それ以外は `rejected` になる（`unsupported` ではない）。
`rejected ⇔ presence モデルで型付け不能` であり、言語全体で型付け不能という意味ではない。

### 規則がある構文（14）

| 分類 | 構成子 |
| --- | --- |
| 変数・リテラル | `var`、`lit`（基底型のマーカー） |
| 関数 | `lam`、`app` |
| 束縛 | `letE`（値の let は多相、計算の let は単相の 2 規則） |
| 条件 | `branch` |
| 組 | `pair`、`fst`、`snd` |
| record | `emptyRecord`、`record`、`recordDefault`、`field` |
| variant | `variant` |

これらは、旧い `Inference.Expr`（14 個）の `embed` と同じ集合。つまり、**旧い核の範囲を `Common` の上へ移したところ**。

### 規則が無い構文（約 17）と、別のモデルでの扱い

別のモデルでは、それぞれ独立に型付けされている（`lean/README.md` の各節）。**今の `Core.infer` には接続されていない**。

| 構成子 | 意味 | 別のモデルの所在（README の節、またはモジュール） |
| --- | --- | --- |
| `literal`、`data` | 数値・文字列などの literal、data の値 | `CoreLiteral`、`CoreData`（「Literal の中身と比較」） |
| `caseE` | `case` の照合 | `CoreCase`、`CoreScopedPatterns`（「Case の照合・順序・presence」） |
| `request`、`boundary` | effect の呼び出し、effect の境界 | `CoreEffects`、`CoreEffectTyping`（「M2: effect 判断の統合」） |
| `handler`、`multiHandler`、`partialHandler` | `catch` の handler | `CoreEffects`（「複数 operation の shallow handler」「決定41」） |
| `method` | method の呼び出し | `CoreQualified`（role と method table） |
| `nominal`、`construction` | nominal 型の構築 | 「Nominal構築・保留cast・listの観測」 |
| `cast` | 暗黙変換 | 同上 |
| `nil`、`cons` | list | 同上 |
| `strictApp` | 評価順を指定した適用 | （要確認） |
| `leaf` | （要確認） | （要確認） |
| `free`、`atom` | 自由変数、原子 | （要確認） |

`（要確認）` は、私がソースで用途を読み切れていないもの。

### 言語の構文との対応（粗い）

| Yulang の構文 | 対応する Core | 今の `Core.infer` |
| --- | --- | --- |
| 関数、application、`let`、`if` | `lam`、`app`、`letE`、`branch` | 覆う |
| tuple、record、`..` の spread、field | `pair`、`record`、`recordDefault`、`field` | 覆う |
| polymorphic variant | `variant` | 覆う（`case` で拾う側は外） |
| `case`、pattern | `caseE` | **外** |
| `act`、operation、`catch`、`sub`/`return`、`for`/`last` | `request`、`boundary`、`handler` ほか | **外** |
| `role`、`impl`、method 呼び出し、`where` | `method` と qualified | **外** |
| `struct`、`enum`、nominal な構築、`cast` | `nominal`、`construction`、`cast` | **外** |
| 数値・文字列・list の literal | `literal`、`data`、`nil`、`cons` | **外** |
| `$x`、`&x`（局所の参照） | effect（`var` effect） | **外** |

つまり、**effect、`case`、role、nominal 型、literal の全てが、まだ公開入口の外**にある。

## 全構文へ届くまでの距離

1. 別のモデルで証明された規則を、**同じ carrier（`Common`）の上の一つの型付け判断**へ載せる。
   presence のモデルを `Common` に載せるだけで M1 の大半が掛かったので、効果・case・role・nominal を載せるのは、段階を踏む大きな仕事になる。
2. 各段階で「閉じた」と言える条件を、先に決める。たとえば、`Typing [] e c ↔ ∃ S ∈ Core.infer e, ∃ p, S.instantiate p ≤ c` を、追加した構文を含む `Core.Expr` の全体に対して示す。
3. `unsupported` と `rejected` の区別を、最終的な公開入口でどう扱うか（ユーザーの判断）。全構文を覆えば `unsupported` は不要になる。

## 順序の候補（案。決めるのはユーザー）

- **高速な算法を先に設計するか**（`2026-11-07-fast-propagation-idea.md`）。全構文を載せてから算法を変えると、証明の作り直しになりうる。
- **載せる順番**。依存の少ない順に、literal と data → `case` → effect と handler → role と method → nominal と cast、が自然に見えるが、未検証。
- 各段階の担当は、算法と証明を ChatGPT Pro、Rust への写しと差分試験を Codex、統合と検査を Claude、という分担を想定している（決定ではない）。

## 確認が要る点

- `strictApp`、`leaf`、`free`、`atom` の用途と、どのモデルが扱うか。
- `Typing` の判断が言語の「全構文」に対してどこまで必要か（実装は後から導くので、核が覆う範囲が実装の範囲を決める）。
