# 引き継ぎ: Lean 型推論核の証明と仕様確定 (2026-11-05)

ブランチ `yulang3`。別マシンで続きをやるための文書。

> 証明再開後の追補: この文書の「Lean 未実装」は引き継ぎ時点の記録。決定7〜18に対応する拡張核に加え、21〜26の純粋cast・多相castの有限endpoint探索・実際のclosure読み取りと初期化済みstore・一般化直前の観測・nominal構築境界・ref照合を追加した。章6.2の匿名impl変数も形式化した。最新の証明範囲と残る義務は [`lean/README.md`](../../lean/README.md) と [`spec/10-inference-core.md` 10.8–10.9](../../spec/10-inference-core.md#109-追加確定事項の形式化) を参照する。これらはsource全体のelaboration、全体solver、preservation/progressの完了を意味しない。

早見表(書くとどうなるかの順): `notes/cheatsheet/2026-11-06-yulang-cheatsheet.md`

## 読む順番(目次)
1. 「今どこにいるか」と「割り引いて読む所」: 状況と注意点
2. 「今日決めたこと」1〜26: 決定の一覧。各項目の末尾に spec の場所がある
3. 「証明してほしい主張」の節(7〜11 / 12,13 / 14 / 15〜17): ChatGPT に渡す材料。量化子と負例つき
4. 「Lean に入ったもの」: 参考実装(本命は ChatGPT 側)
5. 「まだ決まっていない・未着手」: 残り

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
- 全注釈の束縛では、注釈のスキームを仮定した判断が、注釈を使わない単相判断より真に多くの式を受理することを証明すること。ただし、旧 `depth` の単相拒否は決定36で成立しなくなった。同じ本体は現在 `any -> int` で単相受理される（`RecursiveExamples.unannotated_depth_typable`）。top追加以前の拒否を現在の体系の定理として残さず、別のwitnessによる厳密な分離は未完の義務として保持する。
- computed-value cycle(`my a = make b; my b = make a`)が拒否されること(負例)。値制限で一般化できない束縛を SCC に入れても、環境由来の変数を量化しないこと。

14. **値の参照順序の判定は保守的**(`spec/02-declarations.md`)。評価される位置に関数が現れたら(呼んでも渡しても)呼ばれたとみなし、その本体の参照を推移的に依存として数える。lambda で包めば評価位置から外れる。値の cycle はこの規則の特別な場合として拒否される。

### 14 を ChatGPT に証明してほしい主張(Lean 未実装)
- 評価依存の関係を構文から計算する関数を定義し、(a) 値制限を受ける binding が自分自身に推移的に依存するなら拒否、(b) 下にある computed binding への依存は拒否、(c) lambda で包むと依存が消える、を示す。
- 拒否の判定は決定可能で、受理されたプログラムでは、評価順に従って参照先が必ず先に評価済みであること(「副作用の順番が変わらない」)。

15. **union の receiver への method 呼び出し**(`spec/06-roles.md` 6.4)。method を持つメンバーが1つだけならその型に決まり、receiver は普通の cast 境界としてその型へ寄る。2つ以上持てば曖昧エラーで、注釈を入れさせる(並び順では選ばない)。

### 15 を ChatGPT に証明してほしい主張(Lean 未実装)
- 解決の結果がメンバーの並び順に依らないこと(union の順序の入れ替えで結果が変わらない)。
- メンバーのうち method を持つものがちょうど1つなら解決し、2つ以上なら曖昧、0なら失敗、の三分(`Roles.resolve` の曖昧さの判定と同型)。

16. **union の値の各メンバーは別々に cast する。cast の無いメンバーが1つでもあれば型エラー**(`spec/06-roles.md` 6.5)。実行時に失敗させない。
17. **cast は方向を持つ位置に沿って通る**(関数の引数反変・戻り値共変、tuple の成分・record のフィールド・variant の payload は共変)。**nominal な型の型引数(list・ref・box など)は不変で cast も通らない**(区間 (lower, upper) で持つ)。list literal の要素型は `int | ?a` のように後で決まる部分を持ち、`?a` が決まったとき要素は**構築位置に遡って**cast される(保留された境界)。

### 15〜17 を ChatGPT に証明してほしい主張(Lean 未実装)
- cast を部分型とは別の「境界での変換関係」として定義し、関数に対して引数反変・戻り値共変に持ち上がること。
- nominal 型の型引数に対して持ち上がらないこと(不変)。型が決まった `list user_id` が `list int` として受理されない負例。tuple・record・payload には共変に持ち上がること。
- cast 関係の推移閉包が有限な cast 集合の上で決定可能であること(経路が複数あってもどれを選んでも型は同じ)。

18. **cast は型が合わないときにだけ探す**(6.5)。規則があっても、合っていれば適用しない。
19. **弱多相の型変数の表示は `'_a`**(`spec/07-display.md` 7.2b)。多相 `'a`、保護の解除 `'e?` とは別の記号。
20. **7.3 の `'e`・`'e[io]`・`'e?` は、境界ごとの符号付き重みの見せ方**として定義した。「型変数に属性を付ける」枠組みは使わない。`Directed.lean` の証明と同じ言葉になった。
    入れ子で複数の境界の保護が重なるときは、解除を `'e??` のように `?` を重ねて書く(暫定。問題が出たら変える)。

21. **`cast` の本体は純粋でなければならない**(6.5)。effect を起こす cast は宣言時にエラー。ChatGPT 側の `Casts` が「effectを持つcastの実行意味」を対象外にしていた所を、仕様で閉じた。
    証明してほしい主張: 純粋な cast の境界挿入は、式の effect 行を変えない(関数への持ち上げ後も呼び出しの行は同じ)。

22. **型引数を持つ cast は、target が source より大きくならなければ書ける**(6.5)。条件は、(1) target の型サイズ ≤ source のサイズ、(2) 各変数の出現回数が target ≤ source。違反は宣言時に拒否。
    証明してほしい主張: この条件を満たす cast 集合なら、任意の ground な型から到達できる型の集合が有限で、連鎖の探索が停止すること(`Roles.size_decreases` の非厳密版)。`CastGraph` が前提にしていた「多相castの到達instance集合が有限であること」を、この条件から導く。
    等しい大きさを許すので、循環は起きうる(探索は訪問済み集合で止まる)。

23. **評価順序の規則の主語は、computed な束縛どうしの順序**(`spec/02-declarations.md`)。`k` が `late` を読みうるなら `late` を先に評価。名前で決まらない呼び出しは、モジュール内の関数本体から参照される computed な束縛をすべて読みうるとみなす(関数の同一性を追わない)。ChatGPT 側の `EvaluationOrder` が対象外にしていた「局所 closure/alias・格納された関数のフロー」を、この規則で閉じる。
    証明してほしい主張: 名前で決まらない呼び出しを含む式について、この近似が実際の読みの上界になっていること(健全性)。受理されたプログラムでは、読まれる computed な束縛は必ず評価済み。

24. **共変の注釈を検査する時点は、その binding(SCC 全体)の推論が終わった一般化の直前**(`spec/05-effects.md` 5.5b)。ソース順や本体内の順序に依らない。呼び出し側で後から入るものは見ない。入れ子の `my` は自分の終わりで検査する。
    ChatGPT 側の `AnnotationSnapshots`(観測履歴を保存する層)が前提にしていた「何がその時点で既知かを決める solver」の観測時点を、仕様で固定した。
    証明してほしい主張: (a) 観測時点が一般化の直前であれば、受理は本体内の制約生成の順序に依らない(順序不変)。(b) 相互再帰の SCC 内で member の並びを入れ替えても受理は変わらない。(c) 呼び出し側の具体化は、検査済みの snapshot を変えない(`AnnotationSnapshots` で証明済みの性質)。

25. **保留された cast 境界は list に限らない**(6.5)。不変の型引数を持つ nominal 型の構築(struct literal、enum constructor)すべてが、型引数に当たる値に保留された境界を持つ。tuple・record・payload は共変で保留不要。
    ChatGPT 側の `LiteralCasts` は list に限っていたので、対象を「不変の型引数を持つ nominal 型の構築」に広げる義務が増えた。証明してほしい主張: 構築位置の保留境界が、`'_a` が決まったとき(または EOF)に、list の場合と同じ性質(位置ごとの検査、EOF では変換なしで要素型の合流)を満たすこと。

26. **`ref` の receiver は `ref` だけを探す**(6.4)。中身 `'a` には降りない(値に適用したいなら `$n.method`)。`ref` は普通の nominal 型で、委譲規則はない。`ref _ int` のように一部だけ決めた形に特化した method を定義できる。
    ChatGPT 側の `Methods` が対象外にしていた「参照型の処理」は、特別な処理が無いと決まったので不要になった。

27. **再帰で保護が積み増される型は拒否も上限もせず、無限の型を許す**(`spec/10-inference-core.md` 10.3.2)。意味は有限制約の最小解。ChatGPT の `RecursiveRows`(10.10)が見つけた `{raw k} ≤ r`, `protect(b,∅,r) ≤ r`(重み 0,1,2,… を強制)を、仕様として正しい型と決めた。
    **ユーザーは「無限の型を許してもうまく行く。むしろそれを証明してほしい」と言っている。** 証明してほしい主張: (1) 最小解への所属が有限制約について決定できること(`RecursiveRows` の「解への所属の決定手続き」)。(2) 最小解を有限の記号で表せること(等差的に増える重みの集合 = 半線形集合になるはず。表現とその閉包性)。(3) 非 capture と保護・解除の相殺(`Directed` の定理)が無限の解でも保たれること。(4) 型の等価・包含(`≤`)が、この記号表現の上で決定できること。
    表示(無限の重みを `'e` 系の記法でどう見せるか)は未決。

28. **再帰する行は `as` で閉じて表示する**(`spec/07-display.md` 7.3b)。`[k, 'e] as 'e`。重みの数字は出さない。複数変数の相互再帰の書き方は実例待ち。
    ChatGPT が 10.13 で閉じたもの: 無限行の衛生性、一つのサイクルの最小解の有限表示(ray/segment)と所属・包含・等価の決定、生成制約の解から無限行の実行上界まで。
    **閉じていない(研究的な問い)**: 一般の相互再帰(複数サイクルが絡む)の所属決定・有限表示。「禁止点つき整数平行移動 graph の到達定理」に還元される(禁止点なしなら Presburger = Haase–Halfon 2014)。決定不能とは主張されていない。松田先生への相談候補。

29. **receiver の型が最後まで分からない `x.method` は、role の method を先にする**(`spec/06-roles.md` 6.4)。同名の method を持つ role がスコープに複数あれば曖昧エラー、なければ record の field。型が分かっているときの順(field が先)とは逆。決定 7(`x.add x` が `where 'a: Add`)と整合させるための判断。
    証明してほしい主張: `QualifiedInference` の method 要求の生成が、(a) 未知 receiver では role 候補があれば role の制約、なければ field の構造制約になること、(b) 同名 method を持つ role が複数なら曖昧、(c) 同じ SCC の中で receiver の型が分かった場合は、型が分かっているときの順(field → role)で解くこと。(d) **SCC の解決後は解釈が固定**され、呼び出し側の具体化(`'a := box` など)で field に再解釈されないこと(`Size box` の impl が無ければエラー)。ChatGPT の `Methods` が「member ごとの method lookup の優先順位」を対象外にしていた所の一部。

30. **`impl` の候補は、具体化した場所(呼び出し側)で見えるものから選ぶ**(`spec/06-roles.md` 6.2)。入れ子の where も根の呼び出し側の可視範囲で解く。証拠(辞書)は関数へ渡される。
    証明してほしい主張: `Roles.resolve` に「可視な impl 集合」を引数として渡す形(すでに入力リストが可視な impl 集合を表す設計)で、(a) 可視集合が単調に増えると、resolved だった goal は resolved か ambiguous になること(単調性。ambiguous への遷移を除いて結果は変わらない)、(b) 同じ関数を別の可視集合で具体化しても、各具体化の証拠が独立に決まること。`ModuleRoles` の EOF 検査が、その file の可視集合を使うこと。

31. **coherence・孤児規則は課さない**(6.2)。別ファイルの同じ `impl` は共存でき、一箇所に両方見えたときだけ曖昧。辞書は具体化した側のものが渡る。孤児規則は必要が出てから足す(既存コードは壊れない)。

32. **ファイル終端の検査には、そのファイルで見える `impl` の集合を使う**(6.3 の決定 8 と 6.2 の決定 30 の接続)。他のファイルにだけある `impl` は含めない。この集合を使うのは、**型が決まった** role 制約の検査(一意／曖昧／見つからない)だけ。
    **終端まで型変数が決まらなければ、見える impl が一つでもそれに決めない(2026-11-05 訂正、決定 33)。** エラーにして注釈で決めさせる。当初の私の文「一つに決まるならそれに決まり」は広すぎた。
    `ModuleRoles` の EOF 検査が、その file の可視集合を入力に取ること(すでにその設計のはず)を、定理として明示してほしい。
33. **終端での唯一 impl による型変数の補完はしない**(6.3)。`impl` の追加で既存コードが壊れることを避ける。
    ChatGPT の `EOFRoleInference`(可視 ground head から弱型を補完する層)は、この決定により対象外になる。残す場合は「注釈で決まった型に対する検査」だけに使う。補完機能そのものは、将来「未定型を unique impl に決める」オプションを仕様に入れたくなったときのための参考実装として残してよい。

34. **値の型の注釈は公開型を決める**(`spec/04-types.md` 4.2、2026-11-06)。推論結果 ≤ 注釈を検査し、公開型は注釈の型。effect の行は例外で、検査のみ(行変数を束縛しない。決定 1・2・24)。
    証明してほしい主張: (a) 注釈つき binding の公開 scheme は、注釈を上界にした推論結果の scheme に、注釈の型を代入したものと一致すること。(b) 注釈が推論結果より狭ければ、公開型は注釈で、推論結果より多くの呼び出しを許さないこと(情報が減る方向のみ)。(c) 行は注釈を無視して推論され、検査(決定 24)だけが注釈を参照すること。

35. **表示の標準形**(`spec/07-display.md` 7.4b、2026-11-06)。意味が等しい型は同じ文字列。変数名は出現順、union/intersection のメンバーは変数が先・具体型は辞書順、簡約は意味を保つものに限る。
    証明してほしい主張(任意): 標準形を選ぶ関数 `canon` が、意味的な等価を保ち(`canon t ≈ t`)、等価な型で同じ結果を返す(`t ≈ u → canon t = canon u`)こと。`SemilinearRowQuotient` の等価判定を、この標準形の等号判定に接続する。

36. **`any` は最大の型(top)で、注釈にも書ける**(`spec/04-types.md` 4.1、2026-11-06)。TypeScript の `unknown` と同じ(値は何にも使えない)。表示の `⊤` は `any` に統一。推論で負の位置に残った未知型は `any`。
37. **主型推論の完成(ChatGPT への指示、2026-11-06)。** `ValueBounds`・`ValueBoundElimination` の続きとして、次を証明してほしい。
    (1) 負の位置の未知型を、上界の共通部分で決める(上界が無ければ `any`)。正の位置の「下界の和(無ければ `never`)」の双対。これで `ValueBoundElimination` の「負の出現は未対応」が埋まる。反例 `α -> int`(`negative_minimization_loses_instance`)が、双対側で解消すること。
    (2) Simple-sub の共起分析(同じ型と必ず共起する変数の併合、sandwich 併合、正にだけ/負にだけ現れる変数の除去)が、意味(全インスタンスの集合)を保つこと。
    (3) 再帰する型を `as` で閉じる(`spec/07-display.md` 7.3b)ことと、主型推論の接続。
    (4) 得られた型スキームが、制約スキームの全インスタンスと同値であること(主性)。`identity_principal_exact` の一般化。
    (5) 公開型の標準形(決定 35、7.4b)に、(2) の簡約を接続すること。任意。
    ユーザーの言葉: 「推論が計算可能か」の証明を、主型の算法の完成まで求めている。

38. **record の型は、意味が等しければ同じ型**(`spec/04-types.md` 4.3、2026-11-06)。tail でも同じ。`never` は union の単位元(空の union)で、`{}` と `{} | never` は同じ型。ChatGPT が 10.25 で見つけた境界(`{x: 1}` の全インスタンスを一つの proper spine で表せない)への答え: **案A(意味的な同一視)**。
    ChatGPT への指示: `RecordTailBoundary` が示した、構文的な `IsRecord` 条件を持つ参照モデルを、record の tail を束の法則の下で同一視するモデルに作り直す。checker・cut elimination・`StructuralDecisions`・compiler の接続を、そのモデルで再証明する。`Typing.record` の既存のインスタンスを落とさない(10.25 の末尾の方針どおり)。その上で、`SourceConstraintSupport.RecordFree` の制限を外し、record 構築を含む core の式まで、`recordFree_instances_exact` 相当を閉じる。
    注意: 4.1 には「`never` は全ての型の部分型(bottom 型)で、注釈にも書ける」とある。「厳密には型ではない」というユーザーの言い方との表現の差は、実害はないが、4.1 の文言を後で揃えるかもしれない。

39. **record の「残り」は、要求側が rigid なときに共変**(`spec/04-types.md` 4.3、2026-11-06)。要求側(右辺・反変の位置)の残り `S` は field が決まった rigid な spine に限られ、未知 tail の展開(union・`never`・型変数)は供給側(左辺)だけに現れる。`S` が rigid なら、`R ≤ S ⇒ {l:A, ..R} ≤ {l:A, ..S}`。一般の `S` に対する新しい規則は足さない。10.27.5 の確認点への回答。
    ChatGPT への指示: (1) この rigid-`S` 版の共変性を、SemanticRecords の関係に足す。これで `record(l,A,never) ≤ {}` も `never ≤ {}` から導ける。(2) 最終 record 関係の checker と cut elimination を再証明する。(3) `SemanticRecordVarianceBoundary` の反例(`S = ↑{y} ∪ ↑{z}`)は、`S` が rigid でないので、この規則の反例にならないことを明記する。(4) 隠れた field(first-field-wins)は検査で比べない。比べないことによる完全性の欠落があれば、その形を境界として示す。(5) `RecordFree` の制限を外し、record 構築を含む全 core の自由 parameter scheme・全 instance 主型性・拒否完全性を閉じる。

40. **隠れた field は、型の上でも無かったことになる**(`spec/04-types.md` 4.3、2026-11-06)。first-field-wins で隠れた同名 field は値にも残らないので、`{x:int, x:str, ..R}` と `{x:int, ..R}` は同じ型。rigid な tail でも、推論された未知 tail(union など)でも同じ。10.28.3 の確認事項(「nonrigid な推論 tail に隠れた同名 field にも型等価としての消去を適用するか」)への回答。
    ChatGPT への指示: (1) モデルの合同関係に、隠れた同名 field の消去 `record(l,A,record(l,B,R)) ≡ record(l,A,R)` を足す。tail が rigid でない場合も含む。(2) 10.28.3 の `opaque_comparison_iff` と `source_has_incomparable_instances` が、この等式の下で「二つの instance が等価」に変わることを示す(旧関係の定理は歴史として保持し、書き換えて消さない)。(3) checker・cut elimination・商の等号判定を、この等式を含む関係で再証明する。(4) `RecordFree` の制限を外し、opaque な tail を含む全 core 式まで、自由 parameter scheme・全 instance 主型性・拒否完全性を閉じる。

41. **引けない effect の arm を handler に書くとエラー**(`spec/05-effects.md` 5.5、`spec/traps.md` T2、2026-11-06)。許可のマスクに含まれない effect の arm は静的に報告する。引ける arm は普通に動く。
    証明してほしい主張: (a) 許可のマスクに effect key が含まれないとき、その key を扱う arm は決して実行されないこと(`Directed` の「重みが 0 でなければ捕まらない」と、マスクが重みを +1 する定義から)。(b) 逆に、マスクに含まれ、かつ重みが 0 の出現は、対応する arm に必ず捕まること。(c) 静的な検査(マスクに key が無ければエラー)が、(a) と正確に対応すること。

42. **隠れる field の式も評価される**(`spec/04-types.md` 4.3、2026-11-06)。record の構築は、書いた順に各 field の式(と spread)を評価してから、同名 field のうち先に書いたものを残す。ChatGPT の `SourceDataRuntime.eval` が黙って採っていた挙動を、仕様として確定した。
    ChatGPT への指示: (1) 評価器の record 構築が「書いた順に全式を評価する」ことを、定理として明示する(評価順の独立な特徴付け)。(2) 将来 effect を含む式を評価器に入れるとき、隠れる field の式の effect も起きることを前提にする。

43. **式は書いた順(左→右、上→下)に評価される**(`spec/03-expressions.md`、2026-11-06)。tuple の成分・関数の引数・record の field(と spread)・`let` の右辺→本体。値を使わない式も評価される。`SourceDataRuntime.eval` が黙って採っていた順序の、一般規則としての確定。
44. **spread が前にある record の型は、省略可能な field の仕組みで付ける**(`spec/04-types.md` 4.3、2026-11-06)。`{..base, x: 3}` の `x: 3` は既定値。`base` が未知なら `base` に `x?: 'a` を要求し、結果の `x` を `'a | int`。pattern の既定値(3b.3)の型 `{width?: 'a} -> 'a | int` と同じ道具。
    ChatGPT への指示: (1) 核の AST に、spread が前にある record を表す形を足す(今の `record label head tail` は、先頭の field が勝つ形だけ)。(2) その形の型付けを、省略可能な field(`x?`)と union の仕組みで定義し、主型推論と評価器(`SourceDataRuntime`)の両方に接続する。(3) 評価順は決定 43 のとおり(spread が前なら `base` の式が先)。(4) `{..base, x: 3}` の評価結果が、`base` が `x` を持つなら `base.x`、持たなければ `3` になることを、型付けの結果(`'a | int`)と対応づけて証明する。

45. **list の spread の対象は任意の `Fold`**(`spec/03-expressions.md` 3.1、2026-11-06)。`[0, ..(1..10), 11]`。走査順に新しい list へ入れる。`for` と同じ role 解決・辞書・effect。無限の Fold なら終わらない。ChatGPT の推奨(A: list だけ)と違う答え。
    ChatGPT への指示: list spread の型判断に `Fold 'item` の制約を足し、結果の要素型を spread の要素型と literal の要素型の union にする。辞書選択、spread の effect 行、`Fold` の走査から list 構築への翻訳、評価順(書いた順)を接続する。有限性は仮定せず、進行と停止を区別する。operand が既に有限の list 値と解決された核(今の実装)は、その特別な場合として保つ。

46. **作る側の型の順序は、要求で定義する**(`spec/04-types.md` 4.7b、2026-11-07)。`S ≤ T :⇔ ∀ 要求 D, T ≤ D ⇒ S ≤ D`。`|` は正の位置にだけ、要求(負の位置)は union を含まない。構成子の union への分配は、この定義から出る(`(int, int | str) = (int, int) | (int, str)`)。集合論的な部分型を別に持ち込まない。
    旧入口との要件は緩める: 旧 instance は新 instance に入る(保存)。新 instance は旧 instance と要求で等しい(反映は同値を除く)。「全 instance が一致」は要求しない。
47. **標準形は、同じ構成子の union を成分ごとにまとめた形**(`spec/07-display.md` 7.4b、2026-11-07)。`(int, int | str)` が標準形で、展開した形は標準形にしない。
    Pro / Sol への指示: M1 の問い Q1(`notes/questions/2026-11-06-m1-model-contracts.md`)の答えがこれ。(1) `ProducerLe`(要求で定義した順序)を Lean で定義し、要求の文法は union を含まない形に限る。(2) 旧い構造的部分型の保存、分配の等式を定理として示す。(3) `Core.PresenceLegacyObstructions.no_semantic_legacy_instance_exact` は「全 instance の一致」を要求した場合の障害物として保持し、新しい要件(保存と、要求での同値を除く反映)の定理を別に立てる。(4) 7.4b の標準形(まとめる)を選ぶ関数と、その等価保存。
    注意(2026-11-07): variant の型の `|` は型の union ではなく、`:{ str 'a, ..'r }` の別表記(tag の行)。引数の位置(負)にも現れる。決定 46 の「要求は union を含まない」は型の union についてで、variant の行には当てはまらない(`spec/04-types.md` 4.7b)。

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
