# Research Consultation

Yulang の型推論・effect system を研究相談へ持っていくための資料作成 track。

入口:

- `notes/research/consultation/README.md`
- `notes/research/consultation/email-draft.md`
- `notes/research/consultation/technical-brief.md`
- `research/effect-mini-language/directed_stack_weight_letrec_complete_ja.tex`

## Current Packet

2026-06-23 に、相談先の先生への初回相談を想定した下書きを作った。
初回相談は 2026-06-24 に送付済みであり、この packet は送付時点の historical record として残す。

含めたもの:

- 初回メール案
- 4〜6 ページ技術資料の草案
- compiler output を取るための小さい `.yu` 例
- 送付前 guardrail

初回送付の準備は完了済み。現在 open なのは、必要になった場合の follow-up correspondence だけである。

## Initial-send preparation（historical; completed 2026-06-24）

以下は送付前に使った準備チェックリストであり、active TODO ではない。

1. 相談先の現在の所属・連絡先・研究テーマを一次情報で確認する。
2. 送付前に `technical-brief.md` の compiler output を最終 commit で再実行し、commit hash を更新する。
3. 「注釈なし」という表現を送付前に再点検する。
   - surface annotation が無いことと、内部で effect-only skeleton を生成することを混同しない。
   - handler combinator の例は、どの量化変数に関して多相かを明示する。
   - annotation は effect だけでなく、関数の形と effect の可視性・流出を制約するものとして述べる。
4. 1ページの "what is new" を作る。
   - principal weighted scheme
   - directed stack evidence
   - hygienic effect subtraction
   - public scheme projection
   - 初期版は `docs/effect-inference-brief.md` に置いた。
5. 初回相談の killer example は二つに絞る。
   - higher-order `apply`
   - `sub` handler combinator with `int` / `str` / residual `note`
   - `twice`、parser `choice`、`ref.update` は付録 canary として扱う。
   - 公開例の入口は `examples/effect-hygiene/README.md` に置いた。
6. PDF 化するなら、本文は短い資料、`directed_stack_weight_letrec_complete_ja.pdf` は詳細付録として扱う。

## Open

- 初回相談への follow-up correspondence が発生した場合の資料更新と返信。

## Do Not

- 送付資料で `pop(n) = pop(1)` と書かない。
- same-boundary alias-cycle subsumption を型等式として説明しない。
- public scheme と hidden weighted scheme を同じものとして説明しない。
- 現在の実装で確認していない「完全注釈なし handler」の例を headline にしない。
