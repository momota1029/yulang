# 引き継ぎ: Lean 型推論核の証明と仕様確定 (2026-11-05)

ブランチ `yulang3`。別マシンで続きをやるための文書。

## 今どこにいるか
- `lean/` は `lake build` と `lake env lean --trust=0 Audit.lean` が通る。`sorry`・追加公理・`native_decide` はない。
  README の証明対象表が、何を証明して何を証明していないかの正本。
- 前日までの証明(型推論の主性、符号付き行の高階衛生性、shallow handler の上界など)は、
  commit `d5bef9645`〜`663fee827` で入っていた。止まっていた理由は、言語仕様が決まらない箇所があったこと。
- 今日は仕様の未決を1問ずつ決めて、決まった所から Lean に落とした。

## 今日決めたこと(すべて spec に書いて commit 済み)
1. **T3 の検査時点**(`spec/traps.md` T3、`spec/10-inference-core.md` 末尾)。共変位置の effect 注釈は、
   注釈を検査した時点で見えている具体 effect だけを縛る。見えていない行変数が後で具体化されるのは、
   一般化された型の具体化(代入)であって、注釈の再検査ではない。注釈時点で既に分かっている effect は、その時点でエラー。
2. **共変と反変の注釈が同じ変数に付く問題は生じない**。共変位置の注釈は行変数を束縛せず、検査するだけ。
3. **operation-local 多相の escape はエラー**(`spec/05-effects.md`)。handler 内で `'b` は抽象型。
   handler の結果の型や外側の環境に現れてはならない。存在型は導入しない。
4. **variant の tag は一意で、payload は tag ごとに union へ合流する**(`spec/04-types.md` 4.5)。
   payload の一部だけを処理することはできない。網羅性は「tag の集合が閉じているか」で決まる。値に stack weight は要らない。
5. **impl の where は head より構造的に小さい**(`spec/06-roles.md` 6.3)。Paterson 型: 条件の型サイズ合計が head より真に小さく、
   各変数の出現回数が head 以下。違反する impl は宣言時に拒否。解決の深さ上限は置かない。
6. **impl の `type name = ...` の右辺は、他 role の associated type を参照できない**(6.3)。
   具体的な型・型構築子・head の型変数だけ。必要が出てから構文を足す。

7. **未解決の role 制約は自動で型に付く**(6.3)。`my twice(x) = x.add x` は `'a -> 'a where 'a: Add`。一般化のとき、環境由来でない型変数の制約を型に持ち上げる。
8. **一般化できない束縛に残った制約は、同じファイル(module)の終わりまで待つ**(6.3)。決まらなければそこでエラー。未定の型変数は、ファイルの境界を越えて公開されない。
9. **関連型は「新しい型変数 + 制約の等式」で表す**(6.3)。`first : 'c -> 'v where 'c: Index(int, value = 'v)`。型の中に射影を書かず、型の等価判定は第一階のまま。記法は旧版 dump 表示に合わせた暫定。
10. **関連型の変数 `'v` は普通の型変数で、等式は先に束縛しない**(6.3)。制約が先に積まれ、`impl` が選ばれた時に `'v = value` が足され、合わなければその時点でエラー。
11. **operation 署名の role 制約は、署名の下の `where` で書く**(6.3, 05-effects)。handler 側では `'b` は抽象で、その role の method だけが使える。

### 7〜11 を ChatGPT に証明してほしい主張(Lean 未実装)
- 7,8: 推論器の制約言語に role 制約を足したとき、`principal_exact` 相当(生成制約の解 ⇔ 宣言的な型判断)が保たれること。
  持ち上げ(一般化)で環境由来の変数を量化しないこと。ファイル終端で決まらない変数が公開型に残らないこと。
- 9,10: `Roles.resolve` が `resolved` を返したとき、等式 `'v = value` を足すと制約が整合するか矛盾するかの二択になり、積まれた制約の順序に依らないこと
  (制約の追加が可換・冪等であること)。`RolesAssoc.assoc_independent_of_constraints` が土台になる。
- 11: `PolySignature` に role 制約を足し、handler 側では `'b` を rigid に保ったまま、制約が与える証拠だけを使えること。
  証拠を持たない `'b` の method 呼び出しは拒否されること(負例)。

12. **SCC の中は単相で連立して解き、全部注釈した binding だけ多相再帰を許す**(`spec/04-types.md` 4.7)。
13. **「全部注釈」= 全引数と戻り値の型がすべて書かれていること**。effect 行は数えない。注釈の型変数だけが再帰呼び出しで量化され、effect 行は再帰の最中は共有。他の member からの呼び出しにも注釈のスキームを使う(暫定)。

### 12,13 を ChatGPT に証明してほしい主張(Lean 未実装)
- 有限の相互再帰束縛の集合に対して、生成制約の解 ⇔ 宣言的な型判断(`principal_exact` の SCC 版)。SCC 内は単相、完了後に一般化。
- 全注釈の束縛では、注釈のスキームを仮定した判断が、注釈を使わない単相判断より真に多くの式を受理すること(`depth` が通り、注釈なしでは通らない例)。
- computed-value cycle(`my a = make b; my b = make a`)が拒否されること(負例)。値制限で一般化できない束縛を SCC に入れても、環境由来の変数を量化しないこと。

14. **値の参照順序の判定は保守的**(`spec/02-declarations.md`)。評価される位置に関数が現れたら(呼んでも渡しても)呼ばれたとみなし、その本体の参照を推移的に依存として数える。lambda で包めば評価位置から外れる。値の cycle はこの規則の特別な場合として拒否される。

### 14 を ChatGPT に証明してほしい主張(Lean 未実装)
- 評価依存の関係を構文から計算する関数を定義し、(a) 値制限を受ける binding が自分自身に推移的に依存するなら拒否、(b) 下にある computed binding への依存は拒否、(c) lambda で包むと依存が消える、を示す。
- 拒否の判定は決定可能で、受理されたプログラムでは、評価順に従って参照先が必ず先に評価済みであること(「副作用の順番が変わらない」)。

## Lean に入ったもの(commit 順)
| commit | 内容 |
| --- | --- |
| `55f990a15` | 決定1・2。`Annotations.lean` の docstring を確定に合わせた |
| `827ec9f6a` | 決定3。`PolySignature`、`poly_request_constraints_exact`、`poly_handler_constraints_exact`。呼出側は存在量化、handler 側は全称量化 |
| `c037e46cb` | 決定4。`VariantsMerged.lean`。合流、残余との可換、tag 単位の全部処理、網羅性との同値 |
| `856be37bc` | 決定5。`Roles.lean`。停止する `resolve`、健全性、完全性、曖昧さ |
| `06379b6a4` | 決定6。`RolesAssoc.lean`。関連型は既存の `resolve` を再利用でき、停止性の議論は増えない |

## 割り引いて読む所(過大評価しないこと)
- `local_result_no_escape` は、型が局所変数を持たない形で書かれていることから出るだけで、証明は `simp` 一発。設計の帰結であって深い定理ではない。
- operation-local の負例は1つの具体モデルでの確認。任意のモデルで「payload を返す腕は必ず拒否」とは言っていない。
- `VariantsMerged` の合流は入力順の右結合で定義した。順列不変性は証明していない。
- `Roles.resolve` は「impl 集合が整形式」を入力として要求するだけ。source の宣言を検査して拒否する部分は未接続。
- `Roles` の曖昧さは head 照合の段階で判定し、where の成否は見ない。goal の変数は rigid。複数引数の head のサイズは型サイズの合計。
  これらは spec が黙っていた所を、Codex と私で選んだもの。

## まだ決まっていない・未着手
- 仕様の未決(優先度は低い): `cast` の仮採用部分(6.5)、相互再帰で一部だけ注釈した binding の扱い(困る例が出てから)、
  表示(章7)の暫定記法(`@`、`Index(int, value = 'v)`)、型の SCC と評価依存の SCC を同じ単位で扱うか(今は別と書いた)。
- 網羅性と source pattern の組合せ。guard は網羅に数えない(3b.4)、payload 内は見ない(決定4)ので、仕様としては閉じている。
  残るのは source の pattern を核へ翻訳する部分(実装寄り)。
- 証明側(ChatGPT 担当): 決定 7〜14 の各主張(上の「証明してほしい主張」)、solver、preservation/progress、source から核への elaboration。
- `traps.md` T-variant の ①最小解に落ちるか ④`'r` が `:str` を含まないことの保ち方 は solver の仕事として残る。

## 作業の進め方(ユーザーの流儀)
- 1問ずつ、例つきで聞く。ファイルを読ませない。Lean の細部はユーザーに聞かない(私が決める)。
- 決まったら先に spec に書き、Lean は Codex(`gpt-6.1-sol`, high, `terminal: false`)に渡して、戻ってから自分で `lake build` と Audit を回し直す。
- Codex の報告は鵜呑みにしない。README の「示さないこと」の列が正しいか、`git diff` で必ず見る。

## 証明の担当について(2026-11-05 追記)
- 証明の本命は ChatGPT 側が GitHub 経由で持ち込む。この文書の Lean(`Roles.lean`・`RolesAssoc.lean`・`VariantsMerged.lean`・`PolySignature` まわり)は
  **参考実装**として残してある。衝突したら ChatGPT 側を優先してよい。
- Claude 側の役割は、仕様の決定を `spec/` に書くことと、持ち込まれた証明が仕様に忠実か(特に README の「示さないこと」の列)のレビュー。
