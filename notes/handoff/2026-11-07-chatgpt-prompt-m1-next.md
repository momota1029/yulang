# ChatGPT Pro への依頼: 全構文への拡張の続きと、要求駆動 solver (2026-11-07 夕)

ChatGPT は回数制のため、**この 1 回の依頼で、できる限り先へ進める**ことを前提に書く。途中で私(ユーザー)に確認を取らず、止まらずに自走し、こまめに push してほしい。
前回分は、ユーザー側でビルドと Audit を再実行して確認済み(先頭 `2eb0af63a`: `lake build --wfail` 572 jobs、`Audit.lean` 47,937 declarations、どちらも終了コード 0)。
`yulang3` へ取り込み済み。前回の報告は、「閉じた部分」と「閉じていない補題」を正確に分けて書いてあり、信頼できる書き方だった。
今回の目標は二つ: **(B) `Core.infer` が覆う構文を広げ、残りの M1 の補題を閉じる**、**(C) 要求駆動(遅延)solver の設計と、最小の洗練定理**。

```text
yulang の integration/m1-common ブランチ(https://github.com/momota1029/yulang)を pull して、続きを進めてください。
途中で私に確認を取らずに、できるところまで自走し、こまめに push してください。小さな単位(定理一つ、補題一つ)ごとに commit と push を繰り返してください。

## ブランチ
integration/m1-common をそのまま続ける。新しいブランチは切らない。integration/types と yulang3 には push しない。
**最初に origin/yulang3 を merge すること**(今日の決定を書いた資料が yulang3 にあります)。その直後に、次の二つが通ることを確かめる。
  cd lean && lake build --wfail && lake env lean --trust=0 Audit.lean
通らなければ、まずそれを直す。以降も、時々 merge して、同じ確認をする。

## 読むもの(この順)
1. notes/handoff/2026-11-07-core-common-coverage-results.md  ← 前回のあなたの結果。特に 7 節(閉じていない補題)。今回の目標はその statement そのもの
2. notes/design/2026-11-07-common-effect-role-nominal-contracts.md、notes/design/2026-11-07-core-common-coverage.md
3. notes/ideas/2026-11-07-fast-propagation-idea.md の末尾 3 節(ユーザーの着想と決定。作業 C の根拠)
4. notes/design/2026-11-07-common-inference-refinement.md(あなた自身の速さのメモ。作業 C が拡張する)
5. notes/ideas/2026-11-07-error-tolerance-status.md(壊れた入力と部分推論の課題。作業 C の「要求の根」と関わる)
6. lean/README.md の M1・M2 の節と、各構文の節(Case、Literal、Nominal、handler、junction)
7. spec/04-types.md、spec/05-effects.md、spec/06-roles.md(今日の更新あり: 06 の 6.1 に receiver の無い role member、05 の 5.5 に effect 注釈の一つの規則)、spec/03-expressions.md(`catch:`、`{..rest}`)

## 作業 B: 前回の 7 節の補題を閉じる
前回の 7 節の statement を、量化子と前提を変えずに閉じる。順番は、依存と閉じる見込みで決めてよい(入れ替えたら、理由を設計メモに書く)。私の想定する順:
  B5 の基礎(nominal invariance、ground cast): B1 の list/nominal data と nil/cons が依存する。独立に進められると前回の報告にある。
  B2 の構造 pattern の環境橋(`common_pattern_environment_exact`): B3〜B5 全体を待たずに進められると前回の報告にある。
  B1(list / nominal data / float の共通生成)
  A1(`legacy_generated_shared_witnesses`: 全旧 supported source)
  A2(`public_interface_canonical_exact`: 全 finite public interface)
  B3(effect: signed row、有限宣言、全称 handler)
  B4(role: 有限 registry、dictionary、qualified)
各補題の完了条件は前回と同じ:
  (1) 追加した構成子を含む `Core.Expr` について、`Core.Typing M [] e c ↔ ∃ S ∈ Core.infer e, ∃ p, S.instantiate p ≤ c`(support、成功、closed cache、fuel、残余条件を前提にしない)。
      任意の `S ∈ Core.infer e` と任意の `p` が、同じ Typing を与える。
  (2) `Core.infer e = .rejected ↔` その共通判断で結果が存在しない。
  (3) 前の定理(`Core.PresenceOnly` 以下を含む)は弱めない。
  (4) lake build --wfail と Audit.lean が通る。新しい主要 theorem は Audit に登録する。
閉じない補題は、欠けている補題を正確に書いて、次の独立した項目へ進む。

## 作業 C: 要求駆動(遅延)solver の設計と、最小の洗練定理
ユーザーの着想: 上界・下界の伝播の計算を**遅延**する。計算できる所だけ計算する。実行しない部分の型エラーは、遅れて出てもよい。
ユーザーの決定(2026-11-07): **実行する経路の検査は、実行の前に済ませる。** 型が決まらないと method などの実装が決まらないので、そこは伝播を **eager** にする。
言い換え(私の整理。誤りがあれば直してよい):
  - eager にする所は、実装の選択が型に依存する所。method の解決、role の辞書の選択、`cast` の挿入、handler と衛生性、junction、`xs[i]` の error effect。これらの node が solver への「要求の根」。根が問う変数の bound だけを、辺をさかのぼって計算する。
  - 遅延する所は、根が問わない所。実行しない関数、不整合を報告するための全体の検査。後から埋めて、「今回は起きない型警告」として報告する。
  - 粒度は関数(相互再帰なら SCC)。
  - 公開定理の形は変えない。変わるのは計算の順序だけ(制約を scheme に残す qualified な読みではない。私の先の読みは取り違えだった)。
やってほしいこと(B の合間か、B が一区切りついたところで):
  C1. 現在の `Core.infer` が覆う 17 構成子の範囲に限り、「要求の根」と「要求駆動の bound 計算」を Lean の関数として定義する。
  C2. 最小の洗練定理: 任意の根 node について、要求駆動の結果が、eager な参照実装(`solveAll`)の結果と**その node で**一致する(要求同値)。`rejected` の判定は、全体の検査が最終的に済んだ時点で eager と一致する。
  C3. これで「どこまでが eager で必要か」が分かるので、設計メモ(`common-inference-refinement.md` の続き)に、根の一覧と、各根が問う変数の範囲を書く。
速度は主張しない(測定は別)。実装(Rust)は頼まない。C が B の定理の形を壊す場合は、止まって、壊れる箇所を notes/questions/ に書く。

## 決定の読み方(念のため)
- record の残りへの要求の回し方(spec 4.3)、`|` は型の union(正の位置のみ)と variant の行(負の位置にも出る)で別物、`int | str` と `any` は区別する。
- `{..rest}` は record。`case:` と `catch:` は一引数の関数(`\x -> case x:`、`\a -> catch a:`)。`x | catch:` の左辺の effect が届くか(E7)は未決。関わるときは、止まらずに notes/questions/ へ問いとして積む。
- role の member は receiver が無くてもよく、必ず引数を取る(spec 6.1)。その整合条件(K1)は未決。B4 で関わるときは同じ扱い。
- effect の注釈は一つの規則で読める(spec 5.5): 高階関数は自由に書けて、明示的に見える effect は検査される。B3 の「見える effect」の定義の根拠にしてよい。

## 進め方
- 仕様(spec/)が黙っていて決められない所は、止まらずに notes/questions/ に問いとして積む。
  **ユーザーに見える Yulang のコードで違いが書ける問いだけ**にすること。Lean の内部モデルの都合は、自分で決めて、理由と代案を設計メモに書く。
  問いは 1 問ずつ・Yulang のコードの例つき・選択肢つき・あなたの推奨を先頭。専門用語は使う前に説明する。
- sorry、追加の公理、native_decide を使わない。既存の定理の主張を弱めない。README の「示さないこと」の列を、証明した範囲と一致させる。
- 行き詰まる所は、欠けている補題を正確に書いて、別の項目へ進む。
- 回数制なので、**この 1 回で終わらせようとして、証明の質を落とさない**。閉じていないものは、閉じていないと書く。閉じる確率の高いものから。

## 返信に含めてほしいこと
1. 追加した定理の名前と、日本語で読める主張(量化子と前提を省略しない)
2. 閉じていない所と、欠けている補題(前回の 7 節の形式で)
3. B の各補題の到達状況(完了 / 部分 / 未着手)と、次に着手すべきもの
4. 作業 C の到達状況(定義 / 定理 / 設計メモのみ)と、要求の根の一覧
5. ビルドと Audit の結果の末尾
6. notes/questions/ に積んだ新しい問いの一覧
```
