# B4r6: 合流前の impl 変数を、確定 goal からどう決めるか

状態: **未決の一問**（2026-11-07）。E2ではない。
capture後にも安全な宣言Paterson、record正準残余、同tag合流、両K2は承認済みとして維持する。

## 問い

**推奨は1**。次の二つのimplに対する確定goal `R :{tick int}` は、
第一implで `'a := int, 'b := int` と両方へ合流済みpayloadを捕捉し、**二候補の曖昧性**として報告する規則にするか。

```yulang
role R 't:
    type value

impl R (:{tick 'a, tick 'b}):
    type value = int

impl R (:{tick int}):
    type value = int
```

両implにwhereはないので、新しい全instance Paterson条件は空に成立する。
associated RHSは定数intなのでHDAもこの違いを排除しない。
goalのpayloadがintと分かっても、元の二変数の値は型の同値だけから一意には復元できない。
`int|int=int` の他にも `never|int=int` などがあるためである。
record tailの正準引き算を、variant payloadの任意分割へ読み替えることはしない。

1. **推奨: 合流したpayloadをplain変数branchへそのまま捕捉し、この例では両方intと決める。**
   第一implも候補となり、二implが同時に見えれば曖昧。
   より一般の非変数branchについても、実matcherが行う有限の分解/検査とその完全性を形式化する必要がある。
   この一問は一般union注釈を許すものでも、任意のCommon分割を探索する意味を承認するものでもない。
2. **合流前の変数が別の根拠で一意に決まるまで、第一implを解決対象にしない。**
   第一implはこの確定goalだけでは捕捉できず、第二implだけを選ぶ、または保留を報告する。
   確定したgoalであってもimpl内部の未確定を別に扱う規則が必要になる。

これはcheckerの計数方式ではなく候補集合/曖昧性が変わる点なので、内部実装選択として勝手に決めない。
「同tagの重ね書き自体は宣言エラーでない」という承認を、terminal第一implの一律拒否で回避しない。
追加のdeclaration形制限でこの例を避けたpartial theoremをfull B4として報告しない。

existential-substitution addendumに従い、上の運用上の捕捉をspecがまだ決めていないうちは、
任意Common代入存在を独立head意味に置いて新E2を主張しない。
拒否先行は従来どおり未決の作業上の選択であり、この一問では変更しない。
