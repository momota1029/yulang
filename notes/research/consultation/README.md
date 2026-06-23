# Research Consultation Packet

このディレクトリは、Yulang の型推論と effect-only annotation について研究相談するための下書き置き場である。

目的は、初回連絡でいきなり長い形式化を読ませるのではなく、4〜6 ページ程度の短い技術資料と、相談目的が明確なメールを用意すること。

## Files

- `email-draft.md`
  - 初回連絡メールの下書き。
  - 所属、連絡先、公開 URL は未記入の placeholder のままにしている。
- `technical-brief.md`
  - 短い技術資料の本文草案。
  - `research/effect-mini-language/directed_stack_weight_letrec_complete_ja.tex` と
    `docs/infer-solver-invariants.md` の用語へ寄せている。
- `examples/high_order_inference.yu`
  - 注釈なし高階関数の公開型を取るための小さい入力。
- `examples/local_sub_handler.yu`
  - effect-only skeleton を持つ handler combinator の公開型を取るための小さい入力。

## Guardrails

- 「注釈なし」は宣伝文句として使わず、技術資料では「具体的な値型・effect family 集合を省略し、内部で effect-only skeleton / wildcard slot を生成する」と説明する。
- 「多相 handler」は曖昧なので、返り値型 `a` と residual effect row `b` に関する多相性として述べる。
- public scheme と hidden weighted scheme を混同しない。外向けには public scheme、研究相談では hidden weighted scheme と public projection の関係を質問する。
- `ref.update` は便利なデモだが、標準ライブラリの特殊 hack ではなく handler hygiene の canary として説明する。
- `pop(n) = pop(1)` のような等式は書かない。replay 停止性は exact label、residual hash-cons、same-boundary alias-cycle subsumption の実装規則として説明する。

## Before Sending

- 相談先の先生の現在の所属、メールアドレス、専門分野の説明を一次情報で確認する。
- 添付資料内の「実装済み」「証明済み」は、現在の `research/` と `docs/` の範囲に合わせて弱める。
- `technical-brief.md` の compiler output は送付直前に再実行し、commit hash を併記する。
- 形式化全文を添付する場合は `directed_stack_weight_letrec_complete_ja.pdf` を「詳細付録」として扱い、初回本文では読む必要がないと明記する。
