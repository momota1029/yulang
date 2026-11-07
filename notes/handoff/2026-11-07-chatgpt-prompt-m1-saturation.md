# ChatGPT Pro への依頼: M1 の残り — symbolic 飽和・全 instance の求解・公開入口 (2026-11-07)

`integration/m1-common` で、共通 carrier、有限な outer inspector、実 source の変数辺の消去、α 正規化までが通った
(`lake build --wfail` と `Audit.lean` が通過。公開 commit `316e899b6`、記録は `7d4c0b58a`)。
残りは、Pro 自身が復旧記録の 7 節に名前をつけた 5 つの補題。**新しい仕様の問いは 0 件**と報告されていて、
内部表現の選択はすべて Pro の側で決める。この依頼は、その 5 つを順に閉じる 1 回分。

```text
yulang の integration/m1-common ブランチ(https://github.com/momota1029/yulang)を pull して、M1 の残りを進めてください。
途中で私に確認を取らずに、できるところまで自走し、こまめに push してください。

## ブランチ
integration/m1-common をそのまま続ける。新しいブランチは切らない。
integration/types と yulang3 には push しない。
origin/yulang3 に仕様の更新が入ることがあるので、時々 merge して、ビルドと Audit が通ることを確かめる。

## 読むもの
1. notes/handoff/2026-11-07-m1-common-recovery-results.md(特に 7 節「閉じていない補題」。この依頼の設計)
2. notes/design/2026-11-07-m1-common-model.md の 9〜12 節(採用しなかった案と理由)
3. notes/design/2026-11-07-m1-remaining-contracts.md
4. lean/README.md の M1 の節
5. notes/handoff/2026-11-05-lean-proof-handoff.md(決定 1〜47)
6. spec/04-types.md の 4.3 と 4.7b、spec/07-display.md の 7.4b

## 作業(順番どおり)
復旧記録の 7 節の補題を、番号どおりに閉じる。各補題の statement は、7 節に書かれた量化子と前提のまま変えない。

1. 7.1 `saturate_common_rigid_exact`: 実生成 packed clause の共有 graph G と rigid 比較列 E について、
   有限の symbolic branch 列 `saturate G E` を計算し、「G の constructor 方程式の下で E が成立する ⇔ 計算した
   branch のどれかが追加する child / row / mask / presence 制約が成立する」を示す。
   未知 slot の field/optional profile、presence、外側 mask は、同じ共有 ID のまま表現する。
   具体化した Common.Ty に既存の inspector を呼ぶだけの形にしない(推論時に固定した有限 scheme にならない)。
2. 7.2 `saturation_closed` と全 parameter soundness: projection、whole default の分解、lower/upper の伝播が
   追加する状態を、構成した有限 universe に収める。すべての実生成 graph で worklist が停止し、終了時に
   全 rigid 比較が分解済みであることを示す。その閉性から、求解済み branch の**すべての**行・型 parameter 代入で
   残比較が成立することを証明する。成功、closed cache、fuel を公開 principal theorem の前提に置いて代用しない。
3. 7.3 `solve_all_instances_exact`: 任意の実生成 atom 列 a、任意の独立行割当て rows、任意の compiled node 割当て values
   について、`(compile a).Models rows values ↔ ∃ S ∈ solveAll (compile a), ∃ rowParameters, ∃ valueParameters,
   S.instantiateRows rowParameters = rows ∧ ∀ i, S.instantiateValues rowParameters valueParameters i ≈ values i`。
   さらに、返された任意の S と**任意の** parameters が元の Models を与える。
   parameters に ResidualHolds、Models、support、fuel、solver 成功などの条件を残さない。
4. 7.4 公開入口と決定 46: 3 を実生成 clause の有限和へ接続し、
   `Typing [] e c ↔ ∃ S ∈ Core.infer e, ∃ parameters, S.instantiate parameters ≤ c`(任意の対象閉式 e・任意の結果 c)、
   `.rejected ↔ 型付け不能`、対象断片での `.unsupported` 不出現を、残余のない定理として閉じる。
   旧入口との関係は決定 46 の形(旧 supported source の旧 instance ⇒ 新 solved instance。新 instance からは
   同じ結果行の、要求で等しい旧 instance が回収できる)。反映を任意の新 exact/default 型へ無条件に拡大しない。
   統合 `Core.infer` を、Formula.Holds などの別名として導入しない。
5. 7.5 完全な interface 標準形: 任意の有限 public interface I/J について、
   「仕様上の等価性 ⇔ 同じ canonical encoding」。必要なのは、現在の文法外の構成子と行式、一般の再parameter化、
   変数の正負位置・共起・弱さ、regular graph、nominal/role 義務、実 inference / export / display への接続。
   同じ n の型パラメータ全単射による α 同値だけで、全 interface の等価性を定義し直さない。

## 決定の読み方(念のため)
- record の残りへの要求の回し方(spec 4.3): 先頭 field の要求を取り除いて残りに回す。`{x:'a, ..'b} <: {x:'a}` で
  `'b` に要求されるのは `{}`(`{x: any}` ではない)。
- 型の union `|` は正の位置にだけ現れ、要求は union を含まない。variant の `|` は型の union ではなく、
  `:{ str 'a, ..'r }` の別表記(tag の行)で、負の位置にも現れる。
- `int | str` と `any` は区別する(要求の語彙に、型変数・mask・role 制約を含める)。
- `{..rest}`(spread だけの波括弧)は record。spec 3.1 に確定として入った(2026-11-07)。

## 進め方
- 小さな単位で commit と push を繰り返す。
- 仕様(spec/)が黙っていて決められない所は、止まらずに notes/questions/ に問いとして積む。
  **ユーザーに見える Yulang のコードで違いが書ける問いだけ**にすること。Lean の内部モデルの都合は、
  自分で決めて、決めた理由と代案を設計メモに書く。問いは 1 問ずつ・Yulang のコードの例つき・選択肢つき・
  あなたの推奨を先頭。専門用語は、使う前に説明する。
- sorry、追加の公理、native_decide を使わない。lake build --wfail と lake env lean --trust=0 Audit.lean を通す。
- 既存の定理の主張を弱めない。README の「示さないこと」の列を、証明した範囲と一致させる。
- 行き詰まる所は、欠けている補題を正確に書いて、別の項目へ進む。ただし 2 は 1 に、3 は 2 に依存するので、
  1 が閉じないときは、閉じない理由と、その時点で 2 以降のどれが独立に進められるかを書く。
- 前回の復旧で、作業が途中で切れた。小さな単位で push する理由はそこにある。

## 返信に含めてほしいこと
1. 追加した定理の名前と、日本語で読める主張(量化子と前提を省略しない)
2. 閉じていない所と、欠けている補題(7 節の形式で)
3. ビルドと Audit の結果の末尾
4. notes/questions/ に積んだ新しい問いの一覧
```
