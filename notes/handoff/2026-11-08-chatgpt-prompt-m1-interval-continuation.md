# ChatGPT Pro への依頼: 区間モデルで M1 の残りを一括で進める (2026-11-08)

ChatGPT は回数制のため、**この 1 回の依頼で、できる限り先へ進める**ことを前提に書く。途中で私(ユーザー)に確認を取らず、止まらずに自走し、こまめに push してほしい。
前回の Pro の依頼(`2026-11-07-chatgpt-prompt-m1-next.md` ほか)の後、Codex のワーカー(Astra・Sol)が約 1 日、M1 の各目標を並行で進めた。
ユーザーの判断で、**その状態のまま(死んだところまで)ここで打ち切り、続きを Pro に渡す**。ワーカーの結果は、ビルドと Audit を再実行して確認した統合ブランチに入っている。

## 貼る用のブロック

```text
yulang の integration/m1-final ブランチ(https://github.com/momota1029/yulang)を pull して、続きを進めてください。
最初に notes/handoff/2026-11-08-chatgpt-prompt-m1-interval-continuation.md を読み、そこに書いてあるとおりに進めてください。
途中で私に確認を取らずに、できるところまで自走し、こまめに push してください(小さな単位、定理一つ・補題一つごとに commit と push)。
新しいブランチは切らず、integration/m1-final をそのまま続けてください。yulang3 と integration/types には push しないでください。
最初に、cd lean && lake build --wfail && lake env lean --trust=0 Audit.lean が通ることを確かめてください。
最初の作業は「作業 0: モデルの忠実性の監査」です。notes/reference/ の旧世代の文書(不変区間規則)を、最初に読んでください。
```

## 一番大事なこと(これまでの誤りと、正しいモデル)

Codex のワーカーは、**role の解決と nominal の不変性を、「型を点として扱う」モデル**(`Common.Equivalent` と「∃ 代入」)で、大量に証明した。ビルドも Audit も通るが、**モデルが実際の規則と違った**。
正しいモデルは、次のとおり(`spec/06-roles.md` 6.3〜6.5 に、ユーザーの決定として書いてある)。

- 不変な引数は、中心を持たない区間 `(lower, upper)`。表示は `bool | int | 'a & float & complex`(真ん中が型変数)。
- 同じ実引数を 2 つの区間で満たすときは、**下界どうしを lower 側へ、上界どうしを upper 側へ足す**。`'a <: box 'b` と `'a <: box 'c` から `box ('b | 'c, 'c & 'b)`。共起分析で多くは `'b = 'c`。区間は `lower <: upper` を要求する。
- **role の goal は区間の制約になり、下界の head が分かるまで解決を遅らせる**(6.4)。候補の選択は探索ではなく伝播で起こる。record の尾 `..'a` は、引き算を遅らせた結果として決まる。
- 型変数の向きは**型宣言のときに決める**。無限に入れ子になるもの(`list` など)だけが不変で、`box` は共変。理由は型変換のコスト。
- 旧世代の文書が正本として `notes/reference/` にある(`2026-06-02-role-system-yulang2.md`、`2026-06-06-invariant-type-sandwich-yulang2.md`)。**最初に読む**。

この誤りは「spec が『Lean 側で扱う』と書いた規則の中身を、旧世代の文書から拾わなかった」ことから起きた。**同じ誤りを繰り返さないために、下の作業 0 を最初にやる。**

## ブランチ

`integration/m1-final`(統合済み)。最初に、これを pull する。新しいブランチは切らない。`yulang3` と `integration/types` には push しない。
最初に次が通ることを確かめる。通らなければ、まずそれを直す。
  cd lean && lake build --wfail && lake env lean --trust=0 Audit.lean

## 読むもの(この順)

1. `notes/reference/2026-06-02-role-system-yulang2.md`、`notes/reference/2026-06-06-invariant-type-sandwich-yulang2.md`(正しい区間モデル)
2. `spec/06-roles.md` 6.3〜6.5 と末尾の「要確認」(ユーザーの決定がここに積んである)、`spec/04-types.md` 4.3・4.6(record の尾、struct field の rank 2)
3. `notes/handoff/2026-11-07-m1-completion-contract.md`(E1/E2、ワーカーの契約、「∃ 代入」の規則、モデルの忠実性の監査)
4. 設計メモ: `notes/design/2026-11-08-b4r8-interval-model.md`(B4 の区間モデルでの再定義)、`notes/design/2026-11-08-b5-interval-invariance.md`(B5)
5. 各目標の進捗: `notes/handoff/2026-11-07-m1-{b2,b3,b5,b4r}-progress.md`(各 700〜1400 行。末尾の「正確な残り」を読む)、`2026-11-08-m1-b5-interval-results.md`
6. B4 の E2 の記録: `2026-11-07-m1-b4*-results.md`(4 つの E2。点モデルの上の結果なので、区間モデルで何が生き残るかを判定する)
7. `notes/questions/`(未回答の問い。下の「ユーザーに残っている問い」)

## 終わり方の変更: 「証明できません」で終わらない(ユーザーの指摘, 2026-11-08)

前回までのワーカーは、E2(成り立たないことの証明 + 修正案)を正式な終わりとして、反例を見つけて止まることが多かった。ユーザーの不満は「証明できませんと言うだけで、**証明できるような定義を設計してくれない**」こと。今回から次の規則にする。

- **E2 は終わりではない。** 反例が出たら、それは設計の材料。反例を排除し、かつ実際の solver の規則(区間、遅延、正準な残り)に合う**定義を設計して、その定義の上で証明する(E1)ところまで進む**。
- 設計した定義が spec に書かれていない選択を含むなら、`notes/questions/` に、Yulang のコードの例つきで、**定義の候補を 2〜3 個**(推奨を先頭)出す。その間も、決めずに進められる部分(どの候補でも成り立つ補題、候補ごとの場合分け)を証明し続ける。
- 「元の statement は偽」と言う場合も、必ず「こう定義し直せば、こう証明できる」を添える。添えられないときは、**何が足りないか**(どの規則が分からず、それがどの定義に効くか)を書く。
- 終わりに数えるのは、(a) 元の statement の E1、(b) **設計し直した statement の E1(修正の根拠つき)**、のどちらか。反例だけの報告は、途中経過として扱う。

## 作業 0: モデルの忠実性の監査(最初に、短く)

各 Lean モデルの定義が、`spec/` と `notes/reference/` の旧文書に合っているかを、機能ごとに照らして表にする(`notes/handoff/2026-11-08-m1-model-fidelity-audit.md`)。
行は「Lean の定義 / 照らした spec・旧文書の箇所 / 一致・不一致・不明 / 影響する定理」。特に、**role の照合、nominal の不変性(宣言ごとの向き)、record の尾、effect family の引数、struct field の rank 2**。
不一致は、該当する作業(下)の目標を区間モデルに合わせて再定義する根拠にする。statement の変更は、`notes/questions/` に案を書き、ユーザーの承認が要る(承認前は、元の statement を弱めた定理を「完了」と呼ばない)。

## 作業 B4: role の解決を、区間と遅延で

目標: `notes/design/2026-11-08-b4r8-interval-model.md` の言い直し。role の goal は引数の区間への制約。下界の head が分かるまで保留。分かったら、候補が一つなら選択、複数なら曖昧、なければ拒否。選択後の `where` の子は、新しい区間制約として生まれる。辞書は有限。
- 区間の部品(`CommonRoleIntervals`、`CommonRoleIntervalGeneration`、`CommonRoleIntervalCongruence`、`CommonRoleDeferredBounds`)がある。再利用する。
- 点モデルの 4 つの E2(再帰型、重複 field のサイズ、record の尾、合流 payload)と、約 200 の補題のうち、区間モデルで生き残るものを表にする。
- ユーザーの決定(`spec/06-roles.md` 6.3):`where` は head より小さい(隠れた field と同じ tag の重ね書きは縮約後に数える、型変数の捕捉後に合流して小さくなくなる impl は宣言で拒否)、record の尾は引き算を遅らせる、plain の型変数が合流後の payload を丸ごと捕捉、構造的再帰型は解決で拒否(名前付きは対象外)。区間モデルで不要になるものは、そう明記する。
- 停止性: 遅延だけでは、子の head が毎回分かっている鎖は止まらない。Paterson 的な下降が区間モデルで要るかを示す。
- 目標は E1 か E2。**statement の変更は承認が要る**。

## 作業 B5(と B1): nominal の宣言ごとの向き

`box` は共変、`list` など無限に入れ子になるものは不変の区間。向きは型宣言で決まる。
- 既存の `nominal_regular_invariant_exact` など、「nominal はすべて不変」という形の補題は、宣言ごとの向きを持つ形に直す。
- 保留された境界(list literal の `'_a` など)は、不変な引数にだけ付く(`spec/06-roles.md` 6.5 末尾に「要確認」)。
- 進捗: `2026-11-07-m1-b5-progress.md`(nil の葉、row の求解、type flow など)。

## 作業 B2(case・pattern)と B3(effect・handler)

どちらも、約 45 / 約 80 個の checkpoint まで進んでいる。進捗メモの末尾の「正確な残り」を起点に続ける。区間モデルに触れる箇所(effect family の引数、record の尾、nominal の引数)は、作業 0 の表で確かめてから進める。
- B2 の未回答の問い 2 つ(`notes/questions/2026-11-07-b2-optional-field-case-pattern.md`、`…-b2-unreachable-case-effect-row.md`)は、ユーザーが決める。決めずに、局所の補題として進める。
- B3: spec 4.6 の struct field の rank 2(`ref` の `run: ('a -> ['f] 'a) -> ['e, 'f] ()`)は、作成時は `'f` を rigid、使用時は具体化。operation-local の全称 handler と同じ形なので、既存の `CommonEffectKindedFormula` などで足りるかを確かめる。

## 作業 A2(参考)

A2 は E2 で終わっている(`no_computable_canonical_encoding`)。`notes/questions/2026-11-07-a2-canonical-computability.md` の修正案は、ユーザーに聞く問いとして残っている。ここでは触らない。

## ユーザーに残っている問い(進めるうえで決めずに、局所の補題で進める)

- E7(`x | catch:`)。(K1 と K2 の残りは決まった。K1 は宣言で何も拒否しない。)
- 「無限に入れ子」の正確な定義(再帰的に定義された型が自分を通して際限なく深くなる所、と読んでいる)。
- 「plain 変数以外は合流後の payload を分割しない」の理由の見直し(`box` は共変なので、`list('a), list('b)` のような不変な例で聞き直す予定)。
- 拒否と曖昧性の優先順位(`2026-11-07-b4r2-rejection-priority.md`)。
- B2 の 2 つ(optional field、到達不能な arm の静的 effect 行)。
- A2 の契約の修正案。

## 進め方

- sorry、追加の公理、`native_decide` を使わない。既存の定理の主張を弱めない。`lake build --wfail` と `Audit.lean` を通す。新しい主要 theorem は Audit に登録する。README の「示さないこと」の列を、証明した範囲と一致させる。
- **「∃ 代入」や「任意の代入」を含む statement を置くときは、実際の solver がその代入をどう決めるかが spec に書かれているかを、先に確かめる**。書かれていなければ、E2 を出す前に `notes/questions/` に 1 問(Yulang のコードの例つき、選択肢つき、推奨を先頭)を積む。
- 小さな単位(定理一つ、補題一つ)ごとに commit と push。行き詰まる所は、欠けている補題を正確に書いて、別の項目へ進む。
- 回数制なので、**この 1 回で終わらせようとして、証明の質を落とさない**。閉じていないものは、閉じていないと書く。B6(公開入口への統合)は、作業 0 の不一致が片付くまで始めない。

## 返信に含めてほしいこと

1. 作業 0 の表(不一致の一覧と、影響する定理)
2. 追加した定理の名前と、日本語で読める主張(量化子と前提を省略しない)
3. 各目標(B2・B3・B4・B5/B1)の到達状況(完了 / 部分 / 未着手)と、E1/E2 までの残りの補題
4. ビルドと Audit の結果の末尾
5. `notes/questions/` に積んだ新しい問いの一覧
