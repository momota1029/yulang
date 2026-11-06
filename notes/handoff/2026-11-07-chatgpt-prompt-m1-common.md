# ChatGPT Pro への依頼: M1 の最後 — 統一 carrier `Common` と `Core.infer` の公開 (2026-11-07)

`integration/types` に、Pro の M1 継続(`integration/m1-solver`)と Sol の M2(`integration/m2-effects`)を合流済み(411 モジュール、Audit 通過)。
Pro 自身が書いた残契約のメモ(`notes/design/2026-11-07-m1-remaining-contracts.md`)が、そのまま設計になっている。
この依頼は、それを実装して証明する 1 回分。ユーザーへの新しい問いは、設計の段階では無い。

```text
yulang の integration/types ブランチ(https://github.com/momota1029/yulang)を pull して、M1 の最後を進めてください。
途中で私に確認を取らずに、できるところまで自走し、こまめに push してください。

## ブランチ
integration/types から新しいブランチ integration/m1-common を切って、そこへ push する。
integration/types と yulang3 には push しない(別のエージェントが別のブランチで作業することがあります)。
作業の途中で origin/yulang3 に仕様の更新が入ることがあるので、時々 merge して、ビルドと Audit が通ることを確かめる。

## 読むもの
1. notes/design/2026-11-07-m1-remaining-contracts.md(あなた自身が書いた残契約。この依頼の設計)
2. notes/handoff/2026-11-07-m1-solver-results.md の 8 節(閉じていない部分)
3. lean/README.md の「Core (M0)」「M1」「M2」の節
4. notes/handoff/2026-11-05-lean-proof-handoff.md(決定 1〜47)
5. spec/04-types.md の 4.3(record の残りへの要求の回し方)、4.7b(要求で定義した順序)、spec/07-display.md の 7.4b(標準形)
6. notes/questions/2026-11-07-demand-model-contracts.md(Q1・Q5 は回答済み。Q4 は原則に従う仮の前提)

## 作業(順番どおり)
残契約のメモの 1〜6 節を順に実装して証明する。

1. 共通 carrier: `Common.Ty` / `Common.Demand` / `Common.Environment` / `Common.AcceptAt` を、solver・Typing・
   「定理が成り立つ」という法則に依存しない独立な構文・再帰的解釈として実装する。`common_subtype_exact`、
   `contextual_embedding_exact`、`common_arrow_iff`(引数/結果が var・mask・regular graph でも除外しない)。
2. exactEmpty・required・whole recordDefault の像を、同じ carrier で。
3. 自由 mask family と、同深さ tail の接続。現在の二 family(positive data-demand 解と contextual constructor 解)を
   同じ carrier で結ぶ。
4. 行 solver との simultaneous 接続。
5. 生成 formula、束縛、source lowering。record 構築・recordDefault を含む断片で、
   existential 制約を残さない全自由 parameter family に接続する。
6. 最終公開 theorem:
   `Typing [] e c ↔ ∃ S ∈ Core.infer e, ∃ parameters, S の具体化 ≤ c`(任意の閉式・任意の結果)。
   `.rejected` ↔ 型付け不能。この断片で `.unsupported` は出ない。support checker・推論成功・solver 解・fuel を
   公開前提にしない。旧入口との関係は決定 46 の形(旧 instance ⇒ 新 instance。新 instance からは、
   同じ結果行の、要求で等しい旧 instance が回収できる)。
7. 完全な interface 標準形: 決定 47 の標準形(同じ構成子の union を成分ごとにまとめる。型変数が先、
   具体型は辞書順。`int | str` と `str | int` は同じ表現)。`normalize_not_complete` の反例を直す。
   「等しい interface ⇔ 同じ canonical encoding」。

## 決定の読み方(念のため)
- record の残りへの要求の回し方(spec 4.3): 先頭 field の要求を取り除いて残りに回す。`{x:'a, ..'b} <: {x:'a}` で
  `'b` に要求されるのは `{}`(`{x: any}` ではない)。
- 型の union `|` は正の位置にだけ現れ、要求は union を含まない。variant の `|` は型の union ではなく、
  `:{ str 'a, ..'r }` の別表記(tag の行)で、負の位置にも現れる。
- `int | str` と `any` は区別する(要求の語彙に、型変数・mask・role 制約を含める)。

## 進め方
- 小さな単位で commit と push を繰り返す。
- 仕様(spec/)が黙っていて決められない所は、止まらずに notes/questions/ に問いとして積む。
  **ユーザーに見える Yulang のコードで違いが書ける問いだけ**にすること。Lean の内部モデルの都合は、
  自分で決めて、決めた理由と代案を設計メモに書く。問いは 1 問ずつ・Yulang のコードの例つき・選択肢つき・
  あなたの推奨を先頭。専門用語は、使う前に説明する。
- sorry、追加の公理、native_decide を使わない。lake build と lake env lean --trust=0 Audit.lean を通す。
- 既存の定理の主張を弱めない。README の「示さないこと」の列を、証明した範囲と一致させる。
- 行き詰まる所は、欠けている補題を正確に書いて、別の項目へ進む。

## 返信に含めてほしいこと
1. 追加した定理の名前と、日本語で読める主張(量化子と前提を省略しない)
2. 閉じていない所と、欠けている補題
3. ビルドと Audit の結果の末尾
4. notes/questions/ に積んだ新しい問いの一覧
```
