# B4r9: lowerで解決開始できるdemandと、候補が返す区間制約

状態: 一問。intervalの基礎規則は変更しない。現行spec6.2の複数候補の曖昧エラーも変更しない。

**推奨は1**。解決開始判定のlower優先は、候補を調べ始める根拠であり、
candidateの具体headをlower anchorで選別する規則にはしない、と読むか。

```yulang
role Mark 'a:
    our a.mark: () -> int

impl Mark int:
    our x.mark () = 1

impl Mark any:
    our x.mark () = 2

my mark_value(x) = x.mark ()
my answer = mark_value 1
```

Markの通常引数はmethod signatureでは反変、残るwhereでは共変になる。
旧role文書どおりCovariant residualをinstantiateすると、通常引数は `(lower, top)` の区間へ戻る。
この例のint入力が作るlowerをintとして、候補int/anyが返す上下・交差制約を処理する順序が問題になる。
lower優先をcandidate headの選別に使うか、解決開始可否だけに使うかを区別したい。
どちらの案もupperと交差制約は保持し、中心を保存しない。

1. **推奨: 区間を維持してcandidate由来の制約を返す。**
   この例でdemandが `(int, any)` なら、int候補もany候補も整合する拡張を作る。
   両者を候補と数え、現行6.2どおり**曖昧**とする。
   判定は任意のpointを選ぶ探索ではなく、実生成したbounds/交差制約の整合と主型全体への接続で行う。
2. **lowerの単一具体anchorでcandidate headを選別する。**
   この例はlower anchorのintに当たるimplだけを候補として、intのimplを選ぶ。
   upperと交差制約は捨てず、残るboundsも通常machineへ戻す。
   これは「lowerが優先される」を、readinessに加えてcandidate headの比較にも使う選択。
   upper側だけで解ける場合には、そのanchorで対称に選別する。

旧文書は解決開始可否ではlower優先を述べ、candidateも同じcompact簡約を受けると述べるが、
この二つを組み合わせるときの候補関係式までは明示していない。
どちらかを、単なる `∃σ,head[σ]≈goal` へ戻す意味として実装しない。
入力値をanyへcastする問いではなく、roleの通常引数をどのinterval/制約として解決するかの問いである。

この回答に依存しない区間merge・交差制約・点退化・有限bound生成は同じroundで証明を続ける。
E1/E2の終了条件は未達のまま。
