# Research Consultation

Yulang の型推論・effect system を研究相談へ持っていくための資料作成 track。

入口:

- `notes/research/consultation/README.md`
- `notes/research/consultation/email-draft.md`
- `notes/research/consultation/technical-brief.md`
- `research/effect-mini-language/directed_stack_weight_letrec_complete_ja.tex`

## Current Packet

2026-06-23 に、相談先の先生への初回相談を想定した下書きを作った。

含めたもの:

- 初回メール案
- 4〜6 ページ技術資料の草案
- compiler output を取るための小さい `.yu` 例
- 送付前 guardrail

現時点ではまだ送付用ではない。

## Next

1. 相談先の現在の所属・連絡先・研究テーマを一次情報で確認する。
2. `technical-brief.md` の実例を、読者が最初に理解しやすい順に並べ替える。
   - `apply` は最初の例としてよい。
   - `twice` は広い型の例として面白いが、初見には重い。
   - `ref.update` は handler hygiene の canary として後半に置く。
3. 「注釈なし」という表現を送付前に再点検する。
   - surface annotation が無いことと、内部で effect-only skeleton を生成することを混同しない。
   - handler combinator の例は、どの量化変数に関して多相かを明示する。
4. 1ページの "what is new" を作る。
   - principal weighted scheme
   - directed stack evidence
   - hygienic effect subtraction
   - public scheme projection
5. 5個の killer example を選ぶ。
   - higher-order inference
   - `sub` / early return
   - nondet `once` / `list`
   - parser `choice`
   - `ref.update`
6. PDF 化するなら、本文は短い資料、`directed_stack_weight_letrec_complete_ja.pdf` は詳細付録として扱う。

## Do Not

- 送付資料で `pop(n) = pop(1)` と書かない。
- same-boundary alias-cycle subsumption を型等式として説明しない。
- public scheme と hidden weighted scheme を同じものとして説明しない。
- 現在の実装で確認していない「完全注釈なし handler」の例を headline にしない。
