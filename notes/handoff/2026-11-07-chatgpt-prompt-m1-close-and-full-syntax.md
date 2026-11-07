# ChatGPT Pro への依頼: M1 の残りを閉じ、`Core.infer` を全構文へ広げる (2026-11-07)

ChatGPT は回数制のため、**この 1 回の依頼で、できる限り先へ進める**ことを前提に書く。途中で私(ユーザー)に確認を取らず、止まらずに自走し、こまめに push してほしい。
M1 の前回分(7.2・7.3 と、7.4 の公開入口・拒否完全性・旧 instance の保存)は、ユーザー側でビルドと Audit を再実行して確認済み
(`lake build --wfail` 554 jobs、`Audit.lean` 47,115 declarations、どちらも終了コード 0)。`yulang3` へ取り込み済み。
残りは二つ: **(A) M1 を閉じる**(7.4 の反映と 7.5)、**(B) `Core.infer` を全構文へ広げる**。ユーザーの要望は「すべての構文に対応してほしい」。

```text
yulang の integration/m1-common ブランチ(https://github.com/momota1029/yulang)を pull して、続きを進めてください。
途中で私に確認を取らずに、できるところまで自走し、こまめに push してください。前のスレッドは途中で落ちたので、
小さな単位(定理一つ、補題一つ)ごとに commit と push を繰り返してください。

## ブランチ
integration/m1-common をそのまま続ける。新しいブランチは切らない。integration/types と yulang3 には push しない。
**最初に origin/yulang3 を merge すること**(yulang3 にだけある資料と、仕様の更新があります)。その直後に、次の二つが通ることを確かめる。
  cd lean && lake build --wfail && lake env lean --trust=0 Audit.lean
通らなければ、まずそれを直す。以降も、yulang3 に更新が入ることがあるので、時々 merge して、同じ確認をする。

## 読むもの(この順)
1. notes/ideas/2026-11-07-core-infer-coverage.md  ← (B) の設計。`Core.infer` が覆う構文 14/31 と、外にある構文の一覧
2. notes/handoff/2026-11-07-m1-common-saturation-results.md  ← 前回の結果。特に 7 節(閉じていない補題)
3. notes/handoff/2026-11-07-m1-symbolic-results.md
4. lean/README.md の「M1」「M2」「Case の照合・順序・presence」「Literal」「Nominal構築・保留cast・listの観測」
   「複数 operation の shallow handler」「決定41」「junction」「for・last・next・redo」の各節(別のモデルでの証明の所在)
5. notes/handoff/2026-11-05-lean-proof-handoff.md(決定 1〜47)
6. spec/03-expressions.md、spec/03b-patterns.md、spec/03c-control.md、spec/04-types.md、spec/05-effects.md、
   spec/06-roles.md、spec/10-inference-core.md(各構文の意味。確定の印がついた規則を使う)
7. notes/ideas/2026-11-07-fast-propagation-idea.md(参考。下の「速さ」を読む)

## 作業 A: M1 を閉じる(優先度は高いが、B と独立。詰まったら B へ進む)
前回の結果 7.4・7.5 節の statement を、量化子と前提を変えずに閉じる。
- A1. `legacy_instances_reflected`(新しい公開入口 `Core.infer (embed e)` に対して):
  任意の旧 supported source e・任意の旧結果 c について、
  (Core.infer (Core.Required.embed e)).Instance (Common.embedComp c)
    → ∃ old, (SourcePrincipalInference.infer e).Instance Common.rowAlgebra old
              ∧ Common.embedOld c.value ≈ Common.embedOld old.value ∧ c.row = old.row。
  不足は「共有・負位置・構成子の方程式を同時に保つ witness の存在証明」。結果 7.4 節の絞り込んだ形に従う。
  target を任意の新 exact/default 型へ拡大しない。旧 solver の成功を前提に置く代案や、独立 envelope の方程式保存での代用はしない。
- A2. `public_interface_canonical_exact`(7.5): 任意の有限 public interface I/J について、
  既存の公開 instance 意味での等価性 ⇔ 同じ計算可能な canonical encoding。同数 parameter の全単射による α 同値で等価性を定義し直さない。
  全体を一度に閉じられないときは、結果 8 節のように、**閉じた部分言語**を広げる形で進め、各段階の部分言語を明記する。

## 作業 B: `Core.infer` を全構文へ広げる(ユーザーの要望: すべての構文に対応してほしい)
今の `Core.infer` は、`Core.Expr` の 31 個の構成子のうち 14 個(var、lit、lam、app、letE、branch、pair、fst、snd、emptyRecord、record、recordDefault、field、variant)だけを覆う。
残りは別のモデルで個別に証明されているが、`Common` の上の一つの判断には載っていない。これらを同じ carrier の上へ載せる。
載せる順番(依存の少ない順。理由を設計メモに書いて、必要なら入れ替えてよい):
  B1. literal と data(`literal`、`data`、`nil`、`cons`):  CoreLiteral、CoreData
  B2. case と pattern(`caseE`):  CoreCase、CoreScopedPatterns
  B3. effect と handler(`request`、`boundary`、`handler`、`multiHandler`、`partialHandler`):  CoreEffects、CoreEffectTyping
  B4. role と method(`method`):  CoreQualified
  B5. nominal・cast・construction(`nominal`、`cast`、`construction`):  README の「Nominal構築・保留cast・listの観測」
  B6. 残り(`strictApp`、`leaf`、`free`、`atom`): 用途を確かめ、どのモデルが扱うかを設計メモに書く。
各段階 Bk の完了条件(量化子と前提を省略しない):
  (1) 追加した構成子を含む `Core.Expr` の全体について、
      Core.Typing (拡張したモデル) [] e c ↔ ∃ S ∈ Core.infer e, ∃ p, S.instantiate p ≤ c。
      support、成功、closed cache、fuel、残余条件を前提にしない。任意の S ∈ Core.infer e と任意の p が、同じ Typing を与える。
  (2) Core.infer e = .rejected ↔ ¬∃ c, Typing …。
  (3) Core.infer e ≠ .unsupported(追加した構成子が覆われた範囲で)。
  (4) 前の段階までの定理(presence の部分を含む)は弱めない。旧 presence だけの入口は別名(例: `PresenceOnly.infer`)で残し、定理を消さない。
  (5) lake build --wfail と Audit.lean が通る。新しい主要 theorem は Audit に登録する。
**ある段階が閉じない場合**: 欠けている補題を正確に書き、**次の独立した段階へ進む**。段階 Bk を飛ばしてよいのは、Bk の欠けた補題が Bk+1 に依存しない場合だけ。
全構文が覆われた時点で、`unsupported` は不要になる。その扱い(分岐の削除か、空の型として残すか)は、設計メモに理由つきで書く。
`Core.infer` の公開名と、`rejected` の意味(presence モデルの外の構文を rejected にしていた現状)は、各段階で、利用者が読み違えない書き方にする。

## 速さについて(参考。実装はしない)
ユーザーは、Simple-sub より速い伝播の算法を考えている(bound の集合を union-find 風にまとめる。effect 変数にも同じ上下限の解法を使う)。
今は構文の統合を優先するが、B の solver の構造が、その算法を後から入れる妨げにならないよう、設計メモに一節を割く。
- 変数を潰す(`α ≤ β` を `α = β` にする)ことと、bound の集合を共有することの違い(前者は輪のときだけ正確)。
- 算法を Lean の関数として書き、いまの参照実装の洗練(refinement)であることを証明する、という道筋が、B の各段階の定理とどう噛み合うか。
これは設計メモだけ。証明や実装は、依頼しない。

## 決定の読み方(念のため)
- record の残りへの要求の回し方(spec 4.3): 先頭 field の要求を取り除いて残りに回す。`{x:'a, ..'b} <: {x:'a}` で `'b` に要求されるのは `{}`。
- 型の union `|` は正の位置にだけ現れ、要求は union を含まない。variant の `|` は型の union ではなく、`:{ str 'a, ..'r }` の別表記(tag の行)で、負の位置にも現れる。
- `int | str` と `any` は区別する。
- `{..rest}`(spread だけの波括弧)は record(spec 3.1、確定 2026-11-07)。
- 対象なしの `case:` と `catch:` は、一引数の関数(`\x -> case x:`、`\a -> catch a:`)。`x | catch:` の左辺の effect が handler に届くかは未決(spec 3 の E7)。B3 で、これに関わる判断が必要になったら、止まらずに notes/questions/ へ問いとして積む。
- role の member は receiver が無くてもよく、必ず引数を取る(spec 6.1、確定 2026-11-07)。その整合条件(K1)は未決。B4 で関わるときは同じ扱い。

## 進め方
- 小さな単位で commit と push を繰り返す。
- 仕様(spec/)が黙っていて決められない所は、止まらずに notes/questions/ に問いとして積む。
  **ユーザーに見える Yulang のコードで違いが書ける問いだけ**にすること。Lean の内部モデルの都合は、自分で決めて、決めた理由と代案を設計メモに書く。
  問いは 1 問ずつ・Yulang のコードの例つき・選択肢つき・あなたの推奨を先頭。専門用語は使う前に説明する。
- sorry、追加の公理、native_decide を使わない。lake build --wfail と lake env lean --trust=0 Audit.lean を通す。
- 既存の定理の主張を弱めない。README の「示さないこと」の列を、証明した範囲と一致させる。
- 行き詰まる所は、欠けている補題を正確に書いて、別の項目へ進む。
- 回数制なので、**この 1 回で終わらせようとして、証明の質を落とさない**。閉じていないものは、閉じていないと書く。巻き込む順序を選べるなら、閉じる確率の高いものから。

## 返信に含めてほしいこと
1. 追加した定理の名前と、日本語で読める主張(量化子と前提を省略しない)
2. 閉じていない所と、欠けている補題(前回の 7 節の形式で)
3. 各段階 B1〜B6 の到達状況(完了 / 部分 / 未着手)と、次に着手すべき段階
4. ビルドと Audit の結果の末尾
5. notes/questions/ に積んだ新しい問いの一覧
6. 速さの設計メモの場所
```
