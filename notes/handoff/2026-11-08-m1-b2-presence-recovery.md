# B2 復旧: 元 pattern の presence 検査と有限 Core case family

状態: **部分。B2 全体の E1 ではない。** 元の意味論・公開入口・既存 Lean モジュールは変更しない。
復旧依頼の初回全体検証は親作業で実施済み。本作業は新規三モジュールを追加する。

## 規則と、解消する欠落

`spec/03b-patterns.md` 3b.3 は、必須 field に default を書くことを拒否し、default は省略可能な
field にだけ許している。`CasePresenceValidation` はこの三状態の metadata 検査を持っていたが、
元の Core case 有限生成・返却 family に接続されていなかった。
意味的な `OptionalPayload` は必須 field にも成り立つため、元の subtype 制約だけではこの規則を検査できない。

新しい接続は、**元 pattern の各位置における、解決済み入力 record の有限宣言表**を入力とする。
この宣言表を一般の source typing からすべて導く仕事は残る。
同名の field でも別の pattern 位置なら別の site として保持し、record 宣言の lookup は first-field-wins とする。

## 主な定理と全称範囲

- `CommonPatternSourcePresence.sites_exact`: 任意の float/default-code 型、任意の元 pattern、
  任意の有限 syntax path と field 名について、有限 collector の membership iff 元 pattern の
  その位置を直接読むと、ちょうどその field の default node がある。
  payload と record 全体に当たる rest、両方の or branch を保存する。実行成功は仮定しない。
- `CommonPatternDeclaredPresence.check_exact`: 任意の有限入力宣言表と元 pattern について、
  実有限 check の成功 iff すべての元 default node の宣言 presence が optional である。
  欠けた宣言・欠けた field は unknown のままにする。required と unknown は optional に変えない。
- 同 module の `required_report_exact` / `unresolved_report_exact`: 任意の表・pattern・元位置・field 名に対し、
  診断表の membership iff その元 default が存在し、解決結果がそれぞれ required / unknown である。
  `first_field_wins` は任意の path/name/presence と任意の隠れた field 列・後続宣言列について、
  最初の可視 field の presence がそのまま得られることを示す。
- `CommonCasePresenceGeneration.generate_exact`: 任意の有限 record coverage specification、
  元 Core subject、有限な元 arm とその各位置の入力宣言の列、任意の独立な三つの computation 根の割当てについて、
  実生成が formula を返し、その formula が成立すること iff source presence の合法性と
  同じ元 subject/arm の独立した Core typing・coverage・environment・source gate の premises。
  既存 generator の式・slot・記述順を変更しない。
- 同 module の `instances_exact`: 同じ任意の入力と任意の独立な三根の割当てについて、上記 premises iff
  実返却 scheme と**無制約の parameter**があり、全元型根を要求同値、全元行根を文字通りの等式で回収できる。
- 同 module の `all_parameter_returns`: 任意の上記入力、実返却 scheme 列、列中の任意の scheme、
  その任意の無制約 parameter、任意の runtime error 行解釈について、元 default の合法性と、
  **同じ実 evaluator**の成功終了 trace、同じ出力型、同じ cap 以下の観測行を構成する。
  成功 default・選択済み arm・外部 EvaluationSound を仮定しない。対象の source は既存の有限な純粋 data fragment。
- 同 module の `required_blocks`: 任意の上記入力、実 arm 列中の任意の arm、その元 default の任意の位置について、
  その入力宣言が required なら、実 formula 生成と実 solve preparation は両方とも `none` になる。
  ordinary subtype の整合性や実行成功で拒否を迂回できない。

## 保留と拒否の表示

`generate` / `solve` の `none` は presence preparation が未完了であることを表す。
`reports` は元 arm の順で、必須 field の違反と unknown の位置を別々に保存する。
unknown だけの場合を「型制約が充足不能」とは報告しない。
presence が確定して許可された後に通常の型制約が不整合なら、`solve` は `some []` を返す。
新しい成功条件を返却 parameter に付ける方式ではない。

## 残る E1 義務

1. 有限な各位置の入力 record 宣言表を、一般 source 宣言・注釈・推論から導くこと。
   特に default payload の union と fallback による入れ子入力の presence、open tail、polymorphic source は未接続。
   新しい表を受け取る theorem は、この lowering を仮定不要にしたものではない。
2. **作業中の追補（ユーザー決定 `9ee79a0d8` / `1ace30e8e`）**:
   optional な入力を default なしで照合することは合法であり、field が無ければ miss して次の arm へ進む。
   この問いは解消した。既存の Common 全 arm 判断は required 入力を要求するため、
   `CommonOptionalField` 系を用いた新しい全体判断・実生成への接続が必要である。
   本 packet の default 付き field の検査には影響しない。
   到達不能 arm の静的 effect 行だけが未回答のまま残る。
3. 関数・再帰・effect・nominal/list/float/merged-row を含む source producer / adequacy と、
   全 pattern judgment・一般 coverage・実 source generator の iff を閉じること。
4. 同じ公開三契約への統合。B6 は着手しない。

新しい意味論の問いは追加していない。optional の問いは上記のユーザー決定を尊重し、
未回答の静的 effect 行を局所的に決めていない。

## 検証

各 packet を `lake build --wfail Yulang.<module>` で検査した。最後の対象 build は 300 jobs で成功。
新主要 theorem 全てを直接 `lake env lean --trust=0` で再コンパイル・公理監査し、
使用公理は `{propext, Classical.choice, Quot.sound}` の部分集合である。
`sorry`・追加公理・`native_decide` はない。
集約 import / Audit / README への追記と統合後の全体 gate は親作業が行う。
