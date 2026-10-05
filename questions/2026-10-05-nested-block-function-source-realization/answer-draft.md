# ブロックから返す関数と捕捉 — 回答案 a1

Question ID/revision: `nested-block-function-source-realization/q1`
Draft ID/revision: `nested-block-function-source-realization-answer/a1`
Predecessor/history: none
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revisions: question q1 records current branch `757c90564` and legacy Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Task/thread locator: unavailable; this answering conversation has no exposed thread identifier
Governing sources: question q1; `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` の brace semantic interpretation boundary; `notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md` Authoritative §§19–21, 41; `notes/design/2026-10-05-inferred-function-call-views.md` §§1–5; `function-call-view-formation/q1` の承認済み回答 a2

## ユーザーの発言

> 1で合ってると思いますね．

## 解釈と決定案

選択肢1を採用する。対象は次の候補である。

```text
my apply f = { my step x = f x; step }
```

1. この候補では、ブロック内のローカル束縛を順に扱い、最後の式の値をブロックの結果とする。したがって `apply` は関数値 `step` を返す。末尾の `step` 自体は関数呼び出しではない。
2. `step` 本体の `f` は外側の `apply` の仮引数を、`x` は内側の `step` の仮引数を指す。返された関数は、その外側の `f` の捕捉を保持し、後の呼び出しでも同じ捕捉を使う。
3. この意味を、承認済みのカリー化された Function の形をソースで実現する候補として採用する。型付き呼び出しと証拠輸送の前提を明示した条件付きのソースから core への導出を進める。旧 Yulang2 の資料は互換性の根拠として扱い、Yulang3 の狭い設計追補を作成して独立レビューを受け、承認済み範囲を記録する。
4. 本回答はこの候補の意味を選ぶ。現在の本番実装による受理や、すべての brace の解釈、再帰するローカル定義群、effect の実行規則、一般的なクロージャ寿命、呼び出し契約の登録規則は確定しない。既存の役割・callback・注釈・保護・共有証拠の決定を保持し、推論アルゴリズムや本番実装は、残る設計・証明・レビューの gate を満たしてから扱う。

上記はユーザーの選択を質問 q1 の範囲に対応付けた回答者の解釈であり、全文の承認対象に含む。

## 承認と公開

全文 a1 を表示し、明示的な承認後に `approved-answer.md` を保存する。選択肢への賛同を、この全文への承認として自動で扱わない。

回答ファイルは未ステージ・未コミットのまま残す。回答者は Git を変更せず、質問者が一致する質問・回答案・承認済み回答を検証して統合する。最終公開後の訂正は新しい関連質問と再承認を要する。
