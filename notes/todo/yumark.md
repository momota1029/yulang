# Yumark TODO

状態（2026-07-18）: **static core / thin path complete, remaining work specified**。
Yumark 全体が fully complete という意味ではなく、静的構文の production 経路は閉じ、
未対応の構文・diagnostics provenance・専用 preview を残件として切り分けた状態である。

## Done / partial / open

| 状態 | 領域 | 現在地 |
| --- | --- | --- |
| Done | value / type model | algebra-passing model を採用した。設計決定は `bac9cee0`、production migration は `a152595a`。 |
| Done | static syntax lowering | static vocabulary 全体を lowering する production 経路がある（`edc2de3b` / `a152595a` / `dc13b5d6`）。 |
| Done | runtime / render | `lib/std/text/yumark.yu` に HTML / Markdown algebra があり、warm evaluator（`af15ae11`）と per-unit evaluation（`7bd4640b`）まで接続済み。 |
| Done | LS display | resident worker（`9d1da924`）、hover draft（`0c341b33`）、live lazy hover（`5a7abcdd`）が接続済み。structural blank-line / line-doc-continuation semantics も `3e1d4947` / `fa076484` / `9f61e04e` で反映済み。 |
| Partial | spans / diagnostics provenance | source span を運ぶ独立した Yumark AST / value node はない。algebra operation 自体も span 情報を持たないため、Yumark rendering を通した diagnostics / provenance は限定的。 |
| Partial | display surface | LS hover は動くが、Yumark 文書専用の playground preview surface は未実装。 |
| Open | command / injection | `YmCommand` / `YmInlineExpr`（injection / interpolation）は明示的に unsupported。injection の public shape と effect-row parity は未決定。 |
| Open | playground preview | Yumark 文書専用 preview を playground に用意する作業は未着手。優先順位はここでは決めない。 |
| Open | lazy-hover policy | Slice 9、すなわち lazy hover を default / primary policy にするかは、技術的 blocker ではなく意図的に未決定の product decision。 |

## 現行の参照先

- value-model の設計経緯: `../design/2026-07-08-yumark-value-model-tagless-final.md`
- algebra-passing への収束と migration 境界: `../design/2026-07-17-yumark-converged-design.md`
- 旧 model の generalization / memory 調査記録: `../bugs/2026-07-17-yumark-generalization-memory-exhaustion.md`
- structural source boundary: `../design/2026-07-18-yumark-structural-boundaries.md`
- lazy-hover policy: `language-server.md`

## 境界

- 未対応項目を string fallback や名前ベースの特別扱いで埋めない。
- injection / interpolation の public shape や effect-row parity は、別の product / design decision なしに確定扱いしない。
- playground preview 専用の構造を core IR に混ぜない。
