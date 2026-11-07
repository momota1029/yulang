# B4r6: substitution-stable checker の envelope と、合流前変数

状態: **component証明、full E1/E2には未到達**（2026-11-07）。
第六回のユーザー決定はspec6.3が正本。第五回例を宣言時に拒否し、新しい利用時拒否を加えない。
旧proof/E2/公開入口/specは変更しない。

## 1. 有限 sufficient checker の設計

完全な「任意捕捉後のsize」条件を有限に検査する方法の一つとして、
headのlower boundとchildのupper boundを、既存の実Paterson checkerへ渡す。
`CommonRoleStablePaterson` はまず有限Formのrecursive idempotence stageでこの構成を実装した。
Formはvar/int/pair/union/tickであり、これをfull Common/source型文法だとは扱わない。

```text
head lower:
  rigidな構成子と、その下の安定した変数出現を残す。
  潜在的に合流するunion部分全体は、size1・変数出現0の定数へ置く。

child upper:
  symbolic N後の構文をすべて残す。

check D:
  lower(head) と upper(全where) を持つ実Roles.Impl comparisonを作り、
  実CheckedRoles.checkImpl comparisonを計算する。
```

Boolの有限再帰と、有限変数boundの既存occurrence checkerだけを実行する。
全無限代入の列挙、resolverのfuel、役割の非巡回性、利用時の追加size拒否は使わない。
`check_comparison_exact` はBool成功 iff comparison.WellFormed。
これはsemanticな「全捕捉で安全」の**十分条件**であり、その完全な決定手続きだとは主張しない。

選択した理由：潜在的なmerge下のvariableを、後で消えないものとして数えないこと。
普通のrigid位置のvariableは数えるので、unary constructorから引数へ降りる規則も、
`pair(tick a,b) → pair(a,b)` のような再構築も通る。
重複 `tick(union(a,a)) → a` は事前Nで同一branchを縮約するので通る。
`tick(union(a,b)) → int` のように捕捉へ依存しない小さいchildも通る。
任意terminal headはwhereが空なのでその形を理由に拒否しない。

代案：proper-subtermだけを許すcheckerなら証明は短いが、通常の再構築まで排除する。
有限個のcritical captureを列挙する方法は精度を上げる可能性があるが、網羅性が未証明。
semanticな全称条件を証明書として外から要求するだけでは、有限でdecidableなcheckerの実装にならない。
capture後に再checkする案はユーザーに不採用と決められたため実装しない。

## 2. 実際に証明した全称soundness

σを任意の有限Form割当てとし、各像をNした実Term代入をimages σとする。
templateを先にNしても、像を先にNしても、最後にNした結果は等しい。
Nはsize/occを増やさない。

```text
size(actual normalized child[σ])
  ≤ size(upper child[images σ])
  < size(lower head[images σ])
  ≤ size(actual normalized head[σ])
```

中央の真下降は、実 `Roles.size_decreases` をcomputed comparisonの実WellFormedから適用する。
occurrenceについても、代入後の個数を
`sumBelow bound (元変数occ × 代入像occ)` と正確に計算し、同じsandwichで非増加を示す。

`check_sound` は、任意Declaration、check=true、任意所属where、任意Form代入について、
capture後Nのsize真下降と任意post-nameのocc非増加を示す。
`accepted_wellFormed` は同じ成功から実stored `toImpl.WellFormed` を示す。
前回の9/5→5/5宣言は、このcheckerで宣言時にfalse。
これは必要な構成の局所証明であり、全Common同値normalizer/全regular captureへの橋はまだない。
任意Common解釈の代入を、実matcherの任意の逆解として選ぶ定義にしていない。

## 3. canonical record residual の別component

record tailは任意Common同値解でなく、具体的なrowから明示可視labelを引いた実capture。
`CommonRoleStableRecordResidual` は任意payload型でこのcomponentを扱う。
checkは明示label列が空でないこと、実headMatchesは各明示labelのactual lookup.isSomeを検査する。
payload型の照合全体をこのlabel checkerの別名にしていない。

実 `capture labels goal = residual labels (normalize goal)` はlabel一意のまま。
実lookupから明示labelのentry存在を回収するので、少なくとも一entryが除かれる。
任意非負payload weightについて、sizeをempty spineの1と各entryの1+weightの合計とすると、
tailのsizeは元goalより真に小さい。
任意変数name別payload occurrence weightについて、残余はfilterなので個数は非増加。

`checked_residual_decreases` が任意payload型/label列/有限goal row/重みについてこれを示す。
label一致は実matcherが計算したBool成功であり、未知tailへの都合のよい代入を仮定していない。
sourceからこのrecord branchを抽出する全checkerとの統合や、一般rebuilding whereは未証明。
これをfull B4へ移したsupport仮定だと扱わない。

## 4. 現在の一問：terminal headの合流前変数

新条件が完全に成り立っても、whereなしの宣言のhead matchingはまだ必要である。
head `R tick(union(a,b))`、associated定数int、whereなしならPatersonは空に成立する。
確定goal `R tick(int)` に対して、a/bをどう計算するかはrecordのcanonical subtractionとは別問題。
specはtagごとに合流すると述べるが、合流済みpayloadから元のimpl変数への操作的な捕捉をまだ指定していない。

[一問](../questions/2026-11-07-b4r6-merged-head-capture.md) は、
同時に `R tick(int)` の具体implも見えるYulang例を用い、
両変数へintを捕捉して曖昧とする推奨案と、未確定candidateが残るので全体を保留する案を分けた。
候補集合/返却結果が変わるため、観測不能な内部最適化とは扱わない。

`CommonRoleMergedCaptureBoundary` は、実二宣言がstable checkerとWFを通ること、
実constant associated RHSのHDA、実head解釈を証明する。
固定completion (int,int) と (never,int) が同じgoal headとCommon同値で、
両completionの変数0像は非同値であることも証明する。
**どちらかを実solverのcaptureだと定義していない**。任意completionの存在を新E2にしていない。
旧idempotent countergrammarのhead decoderがこの非同一branchを読めないことを、第一impl拒否の理由にもしない。

元契約addendumは「書かれていなければ、E2を出す前にnotes/questions/へ1問」と指示している。
この点が決まるまでは、existential Common substitutionを独立head semanticsに置いて閉じない。
root/constructor再帰型拒否、nominal opaque、no RoleRank/fuel、有限辞書、拒否先行のworking choiceは変更しない。

## 5. 全目標の正確な不足

全Common/source grammarのN、alias/optional/arrow/effect/nominal/record/variant rowの完全なbridge、
有限regular graphのcanonical captureとK2検査、全head候補集合の計算がまだない。
新local checkerのForm代入定理を任意Common/regular代入の定理とは呼ばない。

必要なmissing lemmaは次の二段階。

```text
任意の全source grammarの検証済み宣言D、任意の型/行確定finite regular goal gについて、
実finite matcherが計算する各canonical candidate/captureは独立head判断とiffである。
捕捉はspecで定めた実計算から得る。root/constructorの禁止検査はreject outcomeとiff。

任意の実accepted declaration i、任意の同matcher計算capture σ、任意c∈i.whereについて、
同iの宣言check成功と非rejectの実head一致から、
全normalization/regular cut後のchild measureがgoal measureより真に小さく、
全対応post-name occurrenceが非増加になる。
```

以上を用いるwell-founded実resolver、selection/rejection/ambiguityの独立iff、
全実impl/key/where childの辞書、一般finite-tree agreementとnominal agreementは未証明。
外部matcher/measure/success仮定を追加して同名full E1を閉じていない。

qualifiedの正確な残りは、任意finite verified D/visible V/method M、finite kind付き自由名A、
scheme環境Γ、任意full式e、結果outについて、実有限package Cを生成しmethod ID/ordinary・associated等式/
pending role goal/weak-captured-generalizedを保存し、任意kind保存Common割当てρで、
独立QualifiedTyping(D,V,M,Γ.evalρ,e,out.evalρ) iff
あるkind保存local割当てιがCのordinary/associated制約、canonical residual/K2を含む全独立role辞書、
同captured共有と各使用generalizedを満たすこと。
未解決record tailは具体化までpending。
全返却schemeの任意無制約parameterがmodelを与え、全元modelを同じrow/要求同値の全type slotで回収する全familyも必要。
Satisfiesを外部parameter条件へ移さず、単独qualified generatorの非存在も主張しない。
