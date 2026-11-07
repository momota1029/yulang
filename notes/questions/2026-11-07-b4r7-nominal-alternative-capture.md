# B4r7: non-variable branch は、保持された nominal alternative を有限照合できるか

状態: **未決の一問**（2026-11-08、契約上のファイル日付は2026-11-07）。E2ではない。
plain変数branchが合流済payload全体を捕捉する承認、全instance Paterson、record残余、K2は変更しない。

## 問い

**推奨は1**。non-variableのnominal branchについて、合流後に残る有限alternativeへのcover照合を認め、
複数coverがwhere/関連型を変えてしまうimplは宣言時に拒否する規則にするか。

```yulang
struct box 'a { value: 'a }

role R 't:
    type value
    our t.score: () -> int

impl R (:{tick box('a), tick box('b)}):
    type value = int
    our x.score () = 0

impl R (:{tick 'c}):
    type value = int
    our x.score () = 1

my i: box int = box { value: 1 }
my b: box bool = box { value: true }

my example(flag: bool) =
    my v = if flag: :tick i
           else: :tick b
    v.score ()
```

i/bの型引数は注釈で先に確定している。構築位置の保留castで後から同じ引数へ広げる例ではない。
vのtick payloadには `box int` と `box bool` のalternativeが残る。
nominal引数は不変なので、この型を `box (int | bool)` としてはいけない（spec6.5）。
plain `'c` は承認済み規則でpayload全体を捕捉する。
第一implの `box('a)` / `box('b)` はplain変数branchではなく、現specはその分解をまだ定めていない。

1. **推奨: 保持されたnominal alternativesへの有限coverを認め、必要なwhere決定性を宣言で検査する。**
   この例ではa=int,b=bool、または逆のcoverがあり、どちらも実headを再構成する。
   whereなし・関連型定数なので同じ辞書leafを与え、第一implも候補。第二implと**曖昧**になる。
   一般に複数coverでwhereや関連型が変わるimplは宣言で拒否する。
   捕捉の実計算は保持された有限alternativesだけを列挙し、同じ結果を与えるcover間の実装上の選択で済ませる。
   これは消えたpre-merge値の復元や任意Common型のsplitではない。
2. **有限coverを認め、canonical順の最初のcoverを捕捉として採用する。**
   head branchの初出順に、正準goal alternative順で完全coverを有限探索し、最初のものを採用する。
   この例も第一implが候補となって曖昧。
   whereがcoverで変わる場合もこの順で選ぶため、順序が言語意味になる。full正準順とその保存証明が必要。
3. **このnon-variable branchの有限coverは認めない。**
   第一implはこのgoalの候補にならず、第二implだけを選んでscore()は1になる。
   保持されたalternativeを分解して複数nominal branchへ当てることはしない、というhead照合規則を明記する。
   再構築したheadのCommon意味に一致するというだけでは候補にしない選択肢。

複数coverの問題は、例えば第一implに `where 'a: S` を追加すると現れる。
nominal不変性がaの構造を保持するため、このchildは全captureでサイズ下降できる場合がある一方、
a=int/a=boolで別のS辞書になる。全instance Patersonだけからwhere決定性を導いたことにはしない。
現在の保守的envelope checkerがこのようなwhereを拒否できても、それを未指定のcapture規則の代用にしない。

tupleの同様の例は、既存Commonの成分合流によって再構成照合が必要だと分かるため、
単に不完全なper-branch matcherを新規則の代案として質問していない。
ここではその合流を適用できないinvariant nominalを使った。

source例は実parserでok1/recovery0。既存nominal APIで引数不変性もLean確認した。
fullな「union/variant内nominal carrier」やsource全elaboratorを既に形式化したとは主張しない。
contractのexistential-substitution addendumに従い、この点を一問に置き、任意存在代入で埋めたE2は出さない。
拒否先行は従来どおり未決のworking choiceのまま。
