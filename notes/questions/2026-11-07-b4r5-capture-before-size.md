# B4r5: 捕捉で payload が一致した後にも、size 条件を検査するか

状態: **未決の一問**（2026-11-07）。E2 の報告ではない。
承認済みの record 正準残余、hidden field 除去、variant tag 合流、両 K2 は変更しない。

## 問い（推奨を先に記す）

**推奨は1**。次の impl は、型変数の捕捉後に payload が合流すると where が小さくなくなるため、
**宣言時に拒否する**という読みでよいか。

```yulang
role R 'a 'row:
    type value

impl R 'a (:{tick (int, 'a), tick ('a, int)}):
    where 'a: R (:{tick ('a, 'a)})
    type value = int
```

ここで `'a` を任意の同値解として選んでいない。
具体的な goal `R int (:{tick (int, int)})` では、**最初の role 引数 int が 'a を直接 int に決める**。
その後、既知になった二つの payload はともに `(int,int)` なので合流する。
where の goal も `R int (:{tick (int,int)})` になる。

型変数を異なる構文のまま数えると、head は二 payload の union を持ち size9、where はsize5。
出現回数はどちらも 'a が3で、宣言用の symbolic size/occurrence 条件は通る。
同じ構成子を成分ごとに合流して `tick((int|'a),('a|int))` としても、この例のsizeは9。
ただし 'a=int と決まった後は、正規化した実headもwhereもsize5であり、真下降しない。
型変数の大きさを単に1から大きな型へ置き換えた問題ではなく、捕捉後に新しく冪等縮約が生じる問題。

1. **推奨: 宣言時に、捕捉後の合流にも安全な条件を検査してこの impl を拒否する。**
   単に `N(head)` / `N(where)` の symbolic size を比べるだけでは足りない。
   実 matcher が決める捕捉の各 instance で、正規化後も where が真に小さくなることを保証する宣言 checker が必要。
   「where が小さくなければ宣言時に拒否する」という既存仕様を保つ選択肢。
   有限で decidable な十分条件 checker の具体形・完全性・full B4 はその後の証明対象とする。
2. **宣言は受理し、具体的な捕捉後に size を再検査する。**
   この例の `R int (:{tick (int,int)})` は、その場で「正規化後の where が小さくない」と拒否する。
   その場合、K2以外にも use-site 拒否を一種類増やし、独立 evidence/dictionary 意味にもその拒否を明示する必要がある。
   何を拒否するかがYulangコードから見えるので、internal実装選択として黙って採用しない。
3. **宣言時の symbolic N の size/occurrence だけで受理し、捕捉後は再検査しない。**
   この場合には、この例の self-loop と、その一般化が新しい停止障害候補になる。
   現時点では、この読みを承認済み規則だと仮定して E2 を主張しない。

spec6.3 の「合流は型が分かるまで遅らせる」と「宣言時に拒否する」との接続が未指定であるため、この一問を先に置く。
前回の same-tag padding を承認後の意味へそのまま当ててはいない。
一般 union 型注釈や、source に書けない optional field を反例の前提にしていない。
