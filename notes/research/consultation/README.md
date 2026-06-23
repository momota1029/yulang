# Research Consultation Packet

このディレクトリは、Yulang の型推論と hygienic effect subtraction について研究相談するための下書き置き場である。

目的は、初回連絡でいきなり長い形式化を読ませるのではなく、4〜6 ページ程度の短い技術資料と、相談目的が明確なメールを用意すること。

## Files

- `email-draft.md`
  - 初回連絡メールの下書き。
  - 所属、連絡先、公開 URL は未記入の placeholder のままにしている。
- `technical-brief.md`
  - 短い技術資料の本文草案。
  - 本文は `flip/all_paths` による AE/H の最小例、nested handler、`sub` による hygiene、
    explicit capture contract、`compose` から生じる weighted scheme の順に説明する。
  - `twice`、standard-library canaries、`ref.update` は付録へ回している。
- `../../../docs/effect-inference-brief.md`
  - 旧 1 ページ版。
  - 現在の `technical-brief.md` の流れには未対応なので、研究相談で送る場合は
    `flip/all_paths`、handler hygiene、explicit capture contract、`compose` の順に作り直す。
- `examples/high_order_inference.yu`
  - 注釈なし高階関数の公開型を取るための小さい入力。
- `examples/local_sub_handler.yu`
  - effect-only skeleton を持つ handler combinator の公開型を取るための小さい入力。
  - `int` / `str` / residual `note` の三ケースを同じ handler で確認する。
- `examples/nested_handler_contracts.yu`
  - `flip` と `amount` の handler を重ね、contract が対象 effect だけを処理して residual row を残すことを示す。

## Guardrails

- 「注釈なし」は宣伝文句として使わず、技術資料では「具体的な値型・effect family 集合を省略し、内部で effect-only skeleton / wildcard slot を生成する」と説明する。
- 「多相 handler」は曖昧なので、返り値型 `a` と residual effect row `b` に関する多相性として述べる。
- annotation は effect だけでなく、関数の形と effect の可視性・流出を局所的に制約するものとして述べる。
- 初回メールでは、通常の式・高階関数での effect introduction / propagation は infer され、
  handler boundary での effect elimination だけが explicit contract として check される、という非対称性に絞る。
- 上の contract は「通常の関数にも局所化注釈を付ける」という話ではなく、
  handler が effect subtraction を許可される境界を示すものとして説明する。
- public scheme と hidden weighted scheme を混同しない。外向けには public scheme、研究相談では hidden weighted scheme と public projection の関係を質問する。
- 初回メールでは「主型性を達成した」という断定を避け、`principal-style な公開型` と
  `hidden weighted scheme と public projection の関係` として相談する。
- 共有リンクや相談文脈から実名・所属が抽出できても、このディレクトリには入れない。
  送信時にローカル copy でだけ placeholder を埋める。
- `ref.update` は便利なデモだが、標準ライブラリの特殊 hack ではなく handler hygiene の canary として説明する。
- `pop(n) = pop(1)` のような等式は書かない。replay 停止性は exact label、residual hash-cons、same-boundary alias-cycle subsumption の実装規則として説明する。

## Before Sending

- 相談先の先生の現在の所属、メールアドレス、専門分野の説明を一次情報で確認する。
- 添付資料内の「実装済み」「証明済み」は、現在の `research/` と `docs/` の範囲に合わせて弱める。
- `technical-brief.md` の compiler output は送付直前に再実行し、commit hash を併記する。
- 形式化全文を添付する場合は `directed_stack_weight_letrec_complete_ja.pdf` を「詳細付録」として扱い、初回本文では読む必要がないと明記する。
