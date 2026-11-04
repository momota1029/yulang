# 章10 型推論の核

状態: **構成案・形式化対象を明記**（2026-11-04）。この章は現行の章2〜7を計算体系へ移すための仕様である。新しい注釈構文を追加せず、旧実装の挙動を言語仕様に昇格させない。Lean の対応物は [`../lean/`](../lean/) に置く。

## 10.1 権威と対象

今回の構成では、次の順で根拠を扱う。

1. `yulang3` の確定済みの利用者向け仕様。特に[型](04-types.md)、[effect](05-effects.md)、[表示](07-display.md)、[罠台帳](traps.md)。
2. 2026-11-04 の依頼: `yulang2-oracle` の衛生性を尊重しつつ、破綻した実装をそのまま採用せず、`'e?` と `[io, 'e]` 等は `yulang3` に合わせて再構成する。
3. `yulang2-oracle` の設計意図。参照する commit は `a58eefc31e22141574b6f20c6a5748151c6d79f1`。

旧版の主な参照箇所は `web/docs/ja/reference/type-theory.md`、`spec/2026-05-31-effect-variable-subtractable.md`、`docs/effect-inference-brief.md`、`notes/design/handler-row-subtraction.md`。これらは相互に改訂時期が異なる。古い shift/peel 案、後の directed stack weight、旧 hover 表示を一つの証明済み体系として混ぜない。

核の入力は、名前を解決し、糖衣を除いた式と、その時点で可視な宣言・型注釈である。出力は**値の型、effect 行、残余制約**である。残余制約を黙って捨てて公開型を作ってはならない。

出典: `AGENTS.md`、章4.7–4.8、章5.4–5.5、章7.1–7.4。

## 10.2 型の関係と関数の引数

型の制約は原則として `A ≤ B` であり、すべてを等式単一化に置き換えない。`never ≤ A`、record の幅部分型付け、分岐の union が必要になる。関数の入力は反変、出力は共変で扱う。nominal な型の同一性を構造的な record の同一性と混ぜない。

関数の入力にも computation の行がある。内部記法を

```text
Comp(A, ρ)
Fun(Comp(A, ρin), Comp(B, ρout))
```

と書く。これは利用者向け構文ではない。`'a [flip, 'e] -> ['e] list 'a` の入力側の行を表すために必要になる。

`catch action` に渡される `action` は、callee の handler が処理できる computation である。引数を必ず先に実行し尽くす通常の CBV application だけでは、章5.2 の `all_paths` を表せない。核では computation を引数として渡す規則を明示し、source から suspension/force 等へ移す際は別途その接続を証明する。

分岐は両腕の型を union として保持し、その場で cast を挿入しない。期待型が到来する境界で初めて cast の義務を生成する。`if c: 1 else: "text"` を `int = str` の失敗にしてはならない。

出典: 章3.3、章4.1・4.3・4.8、章5.2、章6.5。

## 10.3 衛生的な effect 行

### 10.3.1 family と出現を分ける

effect の出現は、**family とその型引数を含む key**、およびどの呼出境界から保護されているかを持つ。表示上の family 名だけを比較して capture を決めない。内部の境界識別子は公開型の一部ではない。

同じ `io` に対して、局所で明示された出現と、callback 由来の保護された出現は同時に存在できる。行を family 名の集合に潰してから handler で減算すると、後者を誤って消してしまう。

`ref_update int` と `ref_update str` も別の key である。未解決の型引数を照合するときは、その不変性に対応する型制約を残す。型引数を捨てて同じ family として処理しない。

実行時の dispatch には operation 自体の識別子も必要である。`OperationKey` は family・operation・型引数を保持する。同じ family に二つの operation があって、一方だけを処理しても、もう一方は残る。family 行の entry を丸ごと消すには、operation の被覆が十分であることを示すか、未処理の operation に対応する family を残す。source の不完全な handler をどう診断するかは、この内部表現だけでは決めない。

### 10.3.2 保護・許可・解除

境界 `b` と、そこで引いてよい key の集合 `P` に対して、`protect(b, P, ρ)` は `P` にない出現へ保護を付ける。許可は effect の存在を要求しない。

`release(b, ρ)` は対応する境界の保護を一回だけ外す。別の境界の保護は残す。再帰等で同じ静的境界を反復しても、重なった保護を Boolean 一個へ潰してはならない。往復の等式を主張するときは、境界の新鮮性など実際に必要な前提を明記する。

handler が引いてよいのは、対象 key が一致し、かつ現在の保護がない出現だけである。外側の保護は、内側で `[_]` と書いたからといって消えない。

| 表記 | 核で保つ区別 |
| --- | --- |
| `[io, 'e]` | 明示的な `io` と、保護された tail の出現 `'e` の和。tail 自身に同じ `io` が含まれてもよい |
| `'e[io]` | tail のこの出現で `io` だけを引いてよい。明示的な `io` の発生を要求しない |
| `'e` | 保護された行の出現 |
| `'e?` | 対応する位置で保護を解除した出現。別の位置の `'e` は変更しない |
| `[_]` | その入力境界で全 family を許可する注釈。外側の保護の一括解除ではない |

`'e?` と variant の残余行変数は推論結果にだけ現れる。注釈として新設しない。`'e?` と `[_]` を同じフラグへ置き換えない。

この表は章5.4–5.5と章7.3を同時に満たす内部表現としての再構成である。章7.3の最終的な表示形式、複数の解除をどう印字するかまで確定するものではない。

### 10.3.3 置換と shallow handler

行変数は任意の実際の行へ置換できる。保護・解除・handler の作用は、その**出現位置**で、置換後の行へ作用する。未知の tail は処理対象 family を含まない、と仮定してはならない。

shallow handler の継続は同じ handler に自動で包み直さない。再開した継続には元の computation の effect があり得る。operation arm 自身が起こす effect も、handled computation から引いたという理由では消せない。handler の結果行は、残余と arm 側の effect を含む。

出典: 章5.1–5.5、章7.3、旧版 `spec/2026-05-31-effect-variable-subtractable.md`、`docs/effect-inference-brief.md`。

## 10.4 variant の残り

resolved tag の集合 `H` と有限の alternative support `R` に対して、残余は

```text
residual(H, R) = { (tag, payload) ∈ R | tag ∉ H }
```

である。payload を変えず、処理済み tag を除く。値の alternative には handler の保護 stack を付けない。effect の残余計算と同じ「選択と残余への分割」を使うが、effect の衛生性を必要とする根拠を値へ持ち込まない。

[`Yulang/Variants.lean`](../lean/Yulang/Variants.lean) は、入力の正確な分割、処理済み tag の不在、残余の最小性・最大性、二度除去しても変わらないこと、除去順の交換、payload 置換との両立を証明する。`residual_empty_iff` は「残余が空」と「入力の全 tag が処理対象」の同値である。

これは resolved tag に関する定理である。source の pattern、guard、payload の部分型、再帰的な open row の solver、case の網羅性検査との接続は、この定理だけからは出ない。

出典: 章4.5、`traps.md` T-variant。例: `:str str | :num int` から `:str` を除けば `:num int` が残る。

## 10.5 一般化・解決・表示の境界

- **一般化**: 構文的な値だけを一般化する。環境由来の未確定変数を量化してはならない。計算された binding は単相で共有する。再帰 SCC は同時に扱い、computed-value cycle を通さない。
- **operation の多相性**: 呼出側は operation-local 型変数を具体化する。handler 側は抽象型として受け取り、任意の具体型へ単一化しない。role 制約があれば、その証拠だけを利用できる。
- **method / role**: receiver の下界が定まるまで解決を保留する。field/with、role、effect 行の優先順位を守り、同じ階層の複数候補は曖昧とする。
- **cast**: 期待型境界で挿入する。直接の重複規則と、複数の間接経路を区別する。後者は選択が仕様上自由なので、型の主性と elaboration の一意性を同じ定理にしない。
- **公開表示**: 残余の行変数や実際の制約を消さない。内部の識別子を隠す処理には、型の意味を保つことの根拠が必要になる。

出典: 章2.1、章4.7、章5.1、章6.2・6.4–6.5、章7。

## 10.6 証明の区別

次の主張は別々に検証する。

1. **生成の停止**: 任意の有限な核の式に対して、制約生成が停止する。
2. **生成の健全性・完全性**: 独立に定義した宣言的型判断と、生成制約の解が両方向に対応する。
3. **制約 scheme の主性**: 一つの生成結果が、その式の許される型付けをすべて、かつ余分なく表す。
4. **solver の正しさ**: 実際に解を求め、失敗が解の不在を意味し、成功結果が全解を表し、停止する。
5. **実行時型安全性・衛生性**: elaboration と評価の対応、preservation/progress、呼出元の effect を内側の handler が奪わないこと。

2・3だけから4・5を主張しない。有限の包含制約の solver を証明しても、再帰的な型・保護の stack・role 解決を含む全言語 solver の証明に置き換えない。証明対象、量化子、依存公理は [`lean/README.md`](../lean/README.md) に記す。

## 10.7 既存仕様に残る判断

ここでは未確定の意味論を補って定理を強く見せない。

- `traps.md` T3の、最初は不明だった行が後で注釈外の具体 effect になった場合の検査時点。
- 同じ行変数に反変の許可と共変の検査が集まった場合の組合せ。各出現の局所契約を保つことと、後からの具体化をいつ検査するかは別の問題である。
- generic role、再帰する where、associated type の解決についての循環・停止条件。
- 章4.5の残余と、source の網羅性・guard の組合せ。

上の判断に依存しない核の定理は先に閉じる。未解決制約を受理済みプログラムと同一視しない。
