# deriving（構造的総称）TODO

出典: notes/design/2026-07-02-parting-assessment.md §4（Claude Fable 5、ユーザ承認済み）。
関連: spec/2026-07-02-io-resource-api.md（Wire）、project_show_vs_debug、Yumark。

## 問題

struct / enum 定義から show / debug / eq / ord / wire の instance を
機械導出する仕組みがない。このままでは:

- ユーザは struct 一つにつき instance を 4〜5 個手書きする。
- io 仕様の Wire codec（host boundary の必須契約）を誰も書かず、死文化する。
- Yumark のデータ埋め込みが同じ壁に当たる。

## 方針: マクロではなく、専用の derive 機構

汎用メタプログラミングは導入しない（衛生性の再発リスクと引き換えに
する価値がない）。derive は**コンパイラが知っている固定の導出器の集合**とし、
lowering がフィールド構造から instance を合成する。

取り付け先は既にある: companion module の `with:` ブロック。

```yu
struct point { x: int, y: int } with:
    derive show, eq, wire
```

- `derive` は with: ブロック内の宣言として parse する（綴りは仮）。
- 導出された instance は通常の role impl と同じ経路で登録される
  （.rules: builtin を推論内で特別扱いしない。derive は lowering 段で
  普通の定義に展開し終える）。
- 手書き instance が同居する場合は手書きが勝つ（override）。

## 導出器の初期集合と規則

| 導出器 | 規則 |
|---|---|
| `show` | 全フィールドが show を持つとき、`point { x: 1, y: 2 }` 風の表示。持たない型が混ざればコンパイルエラー（黙って debug に落とさない） |
| `debug` | 全型に対して常に導出可能（show との二系統を維持） |
| `eq` | フィールドごとの eq の積 |
| `ord` | フィールド宣言順の辞書式。**宣言順が意味を持つことを docs に明記** |
| `wire` | manifest の型レイアウト（v2 F2/F4）と同一の encode/decode。record/replay と server 境界の両方がこれを使う |

enum（error 宣言含む）は constructor tag + payload の直積として同じ規則で導出する。

## 再帰・多相・制約

- 型パラメータ付き struct の derive は、パラメータへの role 制約として
  伝播する（`show` の derive → `'a: Show => point<'a>: Show`）。
  role システムの既存機構に乗せ、derive 専用の制約表現を作らない。
- 再帰型は通常の再帰 instance として展開する（無限展開しない設計は
  role 解決側の既存責務）。

## First slice

1. `derive debug` のみ（常に導出可能で、失敗系がない）。
2. `derive eq` / `show`（フィールド制約の伝播が入る）。
3. `derive wire`（io 実装と足並みを揃える。manifest レイアウトの再利用を確認）。
4. enum / error への拡張。

## 完了条件

- std の主要 struct から手書き show/debug が消せる（diff がマイナスになる）。
- derive された wire で record/replay の fixture が動く。
- 手書き override の fixture。
- derive 不能（show を持たないフィールド）が構造化診断になる。

## やってはいけないこと

- 汎用マクロ・コンパイル時実行の導入。
- derive を型推論内の特別扱いで実装すること（lowering で展開を終える）。
- show 導出不能のとき黙って debug 表示に落とすこと（二系統の区別を守る）。
