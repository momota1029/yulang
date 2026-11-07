# B4r8 の点モデルを停止し、不変区間へ戻す

状態: 2026-11-08 のユーザー訂正を受けた設計・既存結果の再分類。E1/E2 の完了報告ではない。
本書を書き終えるまでは新しい証明を追加しない。未コンパイルの第八回matcher草案は削除した。
**同日追補:** ユーザーの追加訂正に従い、nominal全引数を不変とする読みを撤回する。
型引数のvarianceは型宣言時のmetadataであり、boxは共変、無限に入れ子になりうるlist等の引数は不変。
non-variable payloadのno-split決定も要確認へ戻った。以下はこの最新の状態を反映する。
**同日方向付け:** roleはintervalに対する制約を作り、lowerのheadが分かるまで遅延する。
候補は区間の伝播により残ったものから一つ/複数/零を分類し、代入を探索しない。
下記の旧anchor質問はこの方向付けにより取り下げ、点照合の二者択一を新たな前提にしない。
既存の証明・結果文書・仕様本文は変更しない。

## 1. 読み直した正本と、訂正する前提

次を実ファイルから全文読み直した。

1. `spec/06-roles.md` 6.3・6.5、特に2026-11-08の「不変な引数は、中心を持たない区間」。
2. `notes/reference/2026-06-02-role-system-yulang2.md`（124行）。
3. `notes/reference/2026-06-06-invariant-type-sandwich-yulang2.md`（168行）。

後二者は空だった最初のコピーではなく、ユーザーが配置し直した非空ファイルである。
旧文書は区間規則の出典として読み、現行specの新しい決定と衝突する箇所には現行決定を使う。
特に旧文書のconstructor引数を一律不変として記録する箇所は、2026-11-08の型宣言ごとのvariance決定で訂正される。
例えば旧文書の「曖昧なら残す」は、未確定demandの保留と、現spec6.2の確定後の複数implによる曖昧エラーを混同する根拠にしない。
K1のreceiver-less memberの整合条件は、本作業の根拠にしない。

これまでのB4の `Matches := ∃ σ, head[σ] ≈ goal` は**点の比較モデル**だった。
`Common.Equivalent` 自体の定理が誤りなのではない。これを実role照合の定義とし、
任意の点代入を探索するresolverをYulangのresolverと同一視したことが誤りである。
raw demand、candidate、関連型、qualified residualを区間と通常制約の生成として作り直す必要がある。

## 2. 中心を持たないcarrierと意味

raw role demandのboundsを表す入力は既存の型項または共有referenceの**二つ組** `(lower, upper)` とする。
この二境界の入力形式と、各constructor引数を不変とすることは別である。
headの子slotは宣言済varianceに従い、共変なら正側、反変なら負側、不変なら両境界を読む。
中心・代表となる実型・捕捉pointをfieldに追加しない。

意味の説明には、任意のCommon割当てρと任意の実型Tに対して

```text
Fits ρ (lo,up) T := evalρ(lo) ≤ T ∧ T ≤ evalρ(up)
Valid ρ (lo,up)  := evalρ(lo) ≤ evalρ(up)
```

を使う。ここでTは独立意味で全称量化する引数であり、runtimeの保存された中心ではない。
`∃T, Fits I T` と `Valid I` の同値は、前者から推移律、後者からlower自身を数学上の証人にして示せる。
これはresolverがlowerを唯一の実引数として選んでよいという規則ではない。

同じ実引数に二つの区間A,Bが到達したときのmergeは

```text
merge A B := (A.lo | B.lo, B.up & A.up)
```

である。既存Commonのjoin/meet則から、任意ρ,Tについて

```text
Fits ρ (merge A B) T ↔ Fits ρ A T ∧ Fits ρ B T
Valid ρ (merge A B)
  ↔ Valid ρ A ∧ Valid ρ B ∧ A.lo[ρ] ≤ B.up[ρ] ∧ B.lo[ρ] ≤ A.up[ρ]
```

が目標となる。従って元の二つの整合制約を維持した上で、**両方向の交差制約を実際に生成して通常のconstraint machineへ戻す**。
merge結果だけを表示して交差制約を捨てる実装、あるいは「どれかのpointが入りそう」で候補を選ぶ実装にはしない。

点区間 `(T,T)` は退化例として残る。任意Uに対し `Fits (T,T) U ↔ U≈T`。
endpointの意味保存・商・元modelの回収・この退化例には `Common.Equivalent` を引き続き使う。
区間を導入するためにCommonの同値関係や従来の正しい代数定理を削除する必要はない。
ただし点区間のembeddingだけで旧role resolver全体の移送を済ませたことにはならない。

## 3. head照合、capture、候補、pendingの区別

### 3.1 constraint-producing head照合

照合の入力はrole IDと点の型列だけでは足りない。少なくとも次の有限stateが要る。

- 現在のordinary type/row constraint graph、主型root、全role demand。
- 各通常引数と関連型の中心なしbounds、kind・共有ID・level。
- 根の呼出し側で可視な有限impl列、実際のmethod/associated宣言。
- 再collectの原因を区別する有限slot/path/子slot ID、および既に返した制約の記録。

candidateのheadと関連型RHSは同じannotation変数scopeからfreshな共有slotへlowerする。
member bodyの局所変数をcandidate headへ直接共有しない。
candidate側もdemand側と同じcompact規則で簡約し、同じ実引数のboundsをmergeして交差制約を生成する。
各候補の試行で生じた制約は区別し、別の候補を試す前にambient stateへ混ぜない。

独立意味の基本単位は「roleが課すinterval制約と、その伝播・遅延・選択の有限step」とする。
lower headが未確定の間はpendingであり、候補を求めるための代入探索は行わない。
この通常制約生成の意味保存は**全model family**について証明する。
新しいlocal割当てを意味上で量化する場合も、実生成器が作ったslotと制約への割当てに限る。
`∃ arbitrary Common σ, head[σ]≈goal` をruntimeの操作的定義へ戻さない。
実生成のiffは、固定したambient割当てごとに、独立なinterval/head制約の拡張model iff
実生成制約を満たすfresh local割当て、という形で証明する。

候補は、有限registryの各宣言を実propagation ruleへ接続し、現在のboundsの伝播で矛盾・head不適合が判明したものを除いた残存宣言である。
候補の意味を `∃ point σ`、あるいは「候補区間とdemand区間にどれかの共通pointがある」だけで定義しない。
生成制約のmodel存在のiffはconstraint machineとの意味保存に使う数学的定理であり、候補探索アルゴリズムではない。
§8のMark/int/anyを使った旧質問も、この点を曖昧にする枠組みだったため退ける。
具体例の最終分類は新しいhead propagationの実生成から導き、旧point matcherへケースを戻さない。

### 3.2 captureを点代入と呼び換えない

captureは、headの各位置を有限に分解し、fresh slotへ上下のboundsと等式を接続する処理である。
同じ変数の再出現は、既存slotへ区間をmergeし、新しい交差制約を返す。
一度目に選んだpointと二度目のpointを単にCommon同値で比較する処理を基礎にしない。

- plain変数の位置では、供給されたmerged payloadのbounds全体を接続する。`int ≤ a|b` を任意のsplitで解かない。
- record tailは、具体的なrecordから明示可視labelを引いたcanonical residualが決まるまで保留する。
  非退化intervalの残余bounds接続は新しく証明し、lowerをpointに固定しない。
  任意のmasked-equation解をtail像として選ばない。first-field-winsのNはこの操作と別に維持する。
- 同じtagのpayloadは合流後のboundsを使う。消えたpre-merge枝を復元しない。
- **non-variable branchのsplit/cover不許可は要確認へ戻った。** plain変数の承認から、
  box/list/tuple等のnon-variable全般を一律に候補外とする規則を導かない。
  旧第七回のbox不変性に依存する理由と第八回のno-split前提を、確定事項として新証明へ入れない。
- 同じnominal pathは一つのentryへ集め、子slotは**その型宣言で決まったvariance**に従って処理する。
  共変boxの子はunionで合流し、不変listの子はlowerのjoin/upperのmeetと交差制約を使う。
  effect familyにも既存のkind/variance宣言を参照する。旧referenceの一律不変を無断で一般化しない。

2026-11-08の**最新のユーザー訂正**を現在の作業前提とする。
共変boxでは `box int` と `box bool` が `box (int | bool)` へ合流し、この理由では型エラーにならない。
不変listでは、既に引数が確定した `list int` と `list bool` を同じslotへ合わせると
`list (int | bool, int & bool)` となり、整合に必要な `int | bool ≤ int & bool` が成立しない。
前版の「boxの合流が不整合」という記述はユーザーが撤回した説明に基づくので、本版では使わない。
source loweringが実際に同一slotへ入れるbridgeと、一般区間の交差条件の代数定理は別々に記録する。

### 3.2a head grammarで読む方向

varianceは型宣言時に決め、推論時に型bodyを見直して都合のよい方向を選ばない。
無限に入れ子になりうる引数の不変性は、構造全体を再構築するcastを避けるための規則。
単に別constructorの内側に現れるだけで不変とする旧解釈は使わない。
型宣言からvariance metadataを導出する有限算法とそのsoundnessは、新しい独立証明義務である。

| head branch/slot | 読み・生成する制約 | 状態 |
|---|---|---|
| plain型変数 | 供給されたmerged payloadのboundsをそのまま接続。消えた枝へsplitしない | 承認済み。新interval生成器への全bridgeは別 |
| base/any/never/unit | 現在のbound snapshotと通常の順序制約で比較 | lower head判明後のcandidate伝播へ接続。点代入探索にしない |
| tupleの成分 | 外側と同じ共変方向。負の外側に入れば向きを反転 | 既存Common pair構造則を再利用 |
| recordの可視field・variantのpayload | 共変。first-field-wins、tag合流とpayload全体を保持 | record残余は具体化まで保留。non-variable splitの一般規則は未確定 |
| arrowの引数/結果 | 引数で反転、結果は同方向 | 両effect rowの方向も既存arrow則に従う |
| 有限構造のnominal共変引数（box等） | 宣言の正方向を使い、同pathのproducer合流は子のunion | boxを不変区間の例にしない |
| nominal反変引数 | 宣言の負方向を使い、必要な箇所で向きを反転 | constructor名だけから不変と決めない |
| 無限に入れ子になりうるnominal引数（list/木等） | 中心なし(lower,upper)。同じ実引数のmergeと交差制約 | castで無限データ全体を再構築しない |
| named再帰型 | nominal IDと宣言済varianceの引数を読む。bodyは展開しない | 匿名再帰型のK2拒否と区別 |
| alias/associated | aliasは透明なlowering、associatedは通常の新変数と等式 | 他role projectionを勝手に展開しない |

`list('a), list('b)` を使ったnon-variableの問いへ置き換える場合も、
既に確定したlist int/list boolの矛盾した合流を「生成可能なwell-typed goal」として例示しない。
再確認が必要なことを記録する一方、実際に成立するsourceのloweringとpending/整合を先に調べる。
今回のplain変数以外に新しいcapture規則を確定したとはしない。

### 3.3 pending、selection、ambiguity

ユーザーの最新の方向付けを規範とする。role goalは引数intervalへの制約を作る。
通常machineのbound propagationが進み、**lowerのheadが分かるまでpending**にする。
`Valid I` だけ、または上界だけが具体的というだけで、代入を選んで解決を開始しない。
旧referenceのsingle-concrete/main-polarity/upper-anchorの記述を、この最新のlower-head deferralを迂回する許可にしない。
主型＋全rolesの共有、level、全出現sandwichは必要な通常制約・scheme生成の情報として保持する。

lower headが分かれば、propagationが残した可視宣言を数える。

- 一つ: そのactual impl headを選択する。annotation slotの接続から関連型等式を返し、実where列の**全条件**を新しいinterval制約として投入する。
- 複数: ambiguous。whereの結果を見て後から候補を選び直さない。
- 零: rejected/noImpl。K2によるrecursive-type rejectionとは診断理由を分ける。
- lower head未確定: pending。未対応や失敗をpendingへ偽装しない。

ここでの分類は同じconstraint snapshotの観測であり、一つのopen入力のstatusが全将来割当てで変わらないという命題ではない。
新しいordinary/associated制約を受けたら、実machineの現在のboundsから再collect/propagateする。
局所queryが返っただけで全componentが整合すると判断しない（CommonDemandBoundary）。
実行に必要な検査を終える境界の義務も、単一snapshotのquery定理とは区別する。

where-childは**headの選択後だけ**作る。未選択の候補のwhereを解くための探索木を作らない。
同じcaller-visible集合を全childへ使う。
head選択と辞書完成は別であり、childがpendingなら親には未解消義務が残る。
全childに有限evidenceが揃ったときだけ、actual declaration identityと全childを持つ完成dictionaryを返す。
coinductiveな辞書、fuel、深さ上限、RoleRankは追加しない。

K2の二拒否を維持する。pendingのintervalに匿名再帰記述が含まれるだけでは拒否しない。
実際にresolutionがその再帰型のrootへ到達、または選択のためのhead伝播がそのconstructorのinspectionを必要とした所を拒否位置として形式化する。
plain変数でpayloadをそのまま保持できる位置を、一律のrecursive inspectionへ変えない。
named recursionのbodyは展開しない。拒否先行は従来のworking choiceのままで、ユーザー承認済みと書き換えない。

### 3.4 residualのvarianceとlevel

raw role resolutionは中心なしの上下boundsを入力として扱う。
これは、内側のnominal引数が全て不変という意味ではない。constructorの子へ降りる向きは型宣言済varianceに従う。
宣言method型から導出したvarianceを反転して、schemeへ残すwhere引数を読む段階だけで
Covariantはlower、Contravariantはupper、Invariant/Unusedは全区間を使う。
旧role referenceの関連型のraw接続は上下boundsを保持する。再instantiateはCovariant(pos)を `(pos,top)`、Contravariant(neg)を `(bottom,neg)`、
Invariantを元のboundsへ戻す。主型の全出現・他role・ambient/captured/weak共有を保存する。

sandwichは主型全体と全rolesを読む。一つの区間で具体型が同伴しただけで変数を他の位置から消さない。
区間両側に現れる**変数同士**の等式、通常の全出現co-occurrence、具体構造のliftを区別する。
lower≤upperを通常machineへ返してから再collectする順序も保存する。
共有変数のlevel、世代化直前のinterval専用merge、浅い代表を使う条件はsource generationの義務であり、
有限dictionaryの静的存在定理だけで証明したことにはしない。

## 4. 既存Leanの再利用調査

role専用のinterval carrier、全体sandwich、role variance導出、level共有の実装は、調査した現行module群には見つからなかった。
名前にInterval/Boundがあることだけを理由に完成済みとはしない。

| 既存module/API | そのまま再利用できる事実 | 残る境界 |
|---|---|---|
| `LayerBoundTemplates.Constraint/Problem` | 有限lower/flow/upper/check。区間整合と交差制約の出力形式 | role専用lowering・kind/levelの生成 |
| `CommonBoundCoalescing.joinTypes/meetTypes/lower/upper` | 任意の評価関数Bound→Common.Tyと有限template、任意regular型を含むendpointのjoin/meet | fixed boundsの意味を前提とし、任意の新recursive equationsの求解ではない |
| `consistent_iff_satisfiable` | 任意評価関数・有限templateでrigid comparisons成立 iff Common model存在 | 比較の実行可能な決定手続きではない |
| `expand_satisfies/expand_retraction/all_instances_exact` | 任意固定bounds/template、整合なら全無制約parameterがmodel、全独立modelを全slotで要求同値まで回収 | role候補の生成・選択・再帰whereを含まない |
| `DemandBoundPropagation.request_exact/lower_exact/upper_exact` | 任意template・slot・極性で実pull collectorが既存collectorと一致。成功/fuel前提なし | 固定snapshotに限る |
| `CommonDemandSolver.request_exact/finishAll_exact` | 任意shared snapshotのquery一致、任意Compiledの全完了scheme列がreferenceと同一 | queryだけでは全体成功・pending解除を結論しない |
| `CommonDemandBoundary` | 局所lowerが非空でも独立矛盾で完成scheme列が空になる実反例 | role候補の整合を一slotのqueryだけで判定しないために使う |
| `CommonBoundRefWorklist.run_finished/run_closed/run_bound` | 任意pool・初期edge・実返却stateで停止/閉包、trace≤(5N+3)^2 | role解決ループや新slot生成の停止とは別 |
| `CommonBoundRefInspection.inspect_exact` | LowerRef/UpperRef、独立Realizes、PoolWidth、任意row/type割当ての下でinspection iff subtype | 新role loweringが前提を内部供給する証明が必要 |
| `CommonBoundRefSolver.compiled_models_exact` / `CommonBoundRefSolved.solve_all_instances_exact` | row grammar・child grammar・width atomsの三構文前提で、全独立Common modelと実schemeの全familyがiff | 任意のrole headをそのまま両向きtyLeへしてよいとはしない |
| `CommonCanonicalIntervals.instances_interval/canonicalEncoding_exact` | 任意scalar lattice polynomialとcaptured割当てのexact instance familyの区間/有限code | constructor/相関出力/mixed polarity/rows/qualified/regular familyは対象外。role carrierそのものではない |

特にA2 solverのupper grammarはvar/base/emptyRecord/pair/arrow/requiredだけを許す。
逆向き `var ≤ variant(...)`、一般record/default、top/bottom、union/interを無条件に追加できない。
nested nominal carrierも既存TyTermにはない。
従って「既存solverを呼べば全headが閉じる」とはしない。新moduleでのlowering/inspection拡張か、
実生成のpolar grammarから既存前提を導くbridgeが必要である。

raw syntaxは既存TyTermまたはshared Refのendpoint pair、独立意味はCommon.Tyのendpoint pairを第一案とする。
新しく必要なwrapperはrole ID/通常引数/associated名/metadataを付けるだけにし、
独立の新しい型代数、中心field、別のbound propagationアルゴリズムを重複定義しない。
CompactBoundsのlift済variantが必要ならendpointへのreadoutと意味保存を新moduleで証明する。

## 5. 既存証明をどう読むか

**全既存Lean定理は、元の定義・量化子・前提について真のまま。撤回するのはYulangへの未証明な移送である。**
「200」は概数として受け取り、末尾に現treeの全CommonRole moduleと定理名を採録する。
既存のfirst-order `Roles`、`CheckedRoles`、`RoleDictionaries`、associated/checker定理も、
実装しているfirst-order点言語の定理として保持する。全sourceのinterval解決を証明したことにはしない。

分類は次の三つ。

- **A: 独立代数/有限構文の事実。** Commonの意味保存、record residual、有限list/termの算術、独立計算言語の定理。
  intervalのendpointや有限生成の部品として再利用できる。ただし、その部品を実role生成器が呼ぶbridgeは別。
- **P: 点モデルの結果。** Matches/Dictionary/canonical capture/candidate/Plan/halting iffなど、その点モデルに量化する結果。
  statementを保ったまま真だが、intervalの選択・曖昧性・associated・解決不能性へ移送しない。
- **B: bridge待ち。** N、Paterson、head-determination、意味反映など、独立部分が有用でも、
  実interval head生成・candidate簡約・全where接続に結ぶ新しい定理が必要なもの。

例えば `CommonRoleSharedPayloadCapture` のlookup/同payload保存/有限表一意性はA、
同moduleの `approved_head_meaning` は旧point headの意味についてのPである。
`CommonRoleStablePaterson.check_sound` は全Form代入の算術として真だが、
全interval capture後のhead/where下降定理ではなくB。
`CommonRoleNominalCoverBoundary` の有限cover探索・旧point nominal APIの別型性も真だが、
同pathを複数point alternativeとして保持するYulangモデルには移送しない。
特に `box_invariant` のboxは旧API内の固定IDの不変headであり、現仕様の共変struct boxの定理ではない。
既存CommonNominalHeadsの一律不変APIも、宣言済invariant constructorへの新bridgeなしにnominal全般へ使わない。
単なる「全称σが現れる」ことを誤りと呼ばない。HDAやcongruenceの全称割当ては意味保存の検査であり、
runtimeの任意代入選択とは異なる。

### 5.1 旧E2の個別判定

| 旧定理 | 元モデルで何を証明したか | interval・現在の全承認規則へ適用できるか |
|---|---|---|
| `CommonRoleRegularResolutionObstruction.amended_registry_undecidable` / `no_total_actual_regular_resolver` | 二引数(clock μ,data)、point Common head同値、全whereを読むActualEvidenceに対する停止不能還元 | そのまま不可。interval loweringの橋なし。現K2はclock μのrole引数rootで拒否し、旧halting iffの前提が消える |
| `CommonRoleReachedRootObstruction.reached_root_registry_undecidable` | pair内部にclockを残すroot-only拒否の点モデル | そのまま不可。追加K2はheadがμのconstructorへ入る所で拒否。旧 `∀path ¬Rejects` はroot-only定義の事実 |
| `CommonRoleFiniteShadowObstruction.finite_tree_registry_undecidable` | head `{x:left,x:G^k int}` の隠れたfieldをraw checkerが数える有限木モデル | そのまま不可。tailの恣意選択は不要だが、承認Nがpaddingを消す。`normalized_examples_rejected` は小例の拒否済み。interval制約生成の橋も未証明 |
| `CommonRoleFiniteTailObstruction.normalized_registry_undecidable` | `{x:int,..a}` にa:={x:int}を選び、head同値を保ったままchildへclockを戻すモデル | **実subtractionと食い違う**。正準残余は{}。旧assignmentが実solverから生成される事実がなく、interval化で復活しない |
| `CommonRoleMergedObstruction.canonical_merged_registry_undecidable` | matcherは冪等contractするがcheckerは重複tag payloadを数えるモデル | そのまま不可。tailの任意像には依存しないが、承認済tag N/stable checkでpadding消失。小例拒否は既存 `proposed_rejects_minimal/growing`。intervalへの新bridgeなし |

従って、**現在のdeferred interval規則に対するE2として数えられる旧定理はまだない**。
root/constructor・shadow・mergedは旧弱いモデルの数学的反例として保持する。
finite-tailは特に実生成から外れた存在代入を用いたため、実Yulangの不可能性の証拠にしない。
associatedの旧 `checked_registry_counterexample` も、隠れたfieldからRHSを選べる旧定義の事実であり、
承認済みhead-determination checkやinterval associated生成へ自動移送しない。
head/where関連の旧obstructionを同じ理由で新E2に数えない。

## 6. B4 registry exactness の改訂statement

元7.6の任意有限verified D・caller-visible V・全finite regular descriptionを保ち、
独立意味を **interval制約＋伝播＋lower-head deferral＋選択後のwhere投入** として訂正する。
実resolverは代入探索器ではなく、既存DemandBoundPropagation/CommonDemand*のqueryと通常constraint machineを使う遅延resolverである。

目標statementの全入力を次の通り全称量化する。

```text
任意の有限kind付きrole/method/impl宣言D、caller-visible集合V、
Dの現行WellFormed・HeadDeterminesAssociated・承認済N/stable Paterson check、
型宣言時に確定したconstructor引数のvariance metadata、
任意の有限共有型/行constraint snapshot G、主型root M、
通常/associated引数のinterval demand有限列Q、既存slot/kind/level入力metadataに対して、

実deferred resolver propagateRoles(D,V,G,M,Q)は有限に停止して、
更新したordinary/associated制約・各demandのpending/selected/ambiguous/rejected・
選択されたactual implと生成した全where-child制約を返す。

lower headが未確定のdemandはpending、既知なら実伝播後の残存候補が
一つ/複数/零でselected/ambiguous/rejectedとなることが、
同じsnapshotに対する独立DeferredIntervalResolutionとiff。
K2拒否は実際の到達/inspectionに対応し、通常の不整合・候補零・曖昧性と区別する。

任意のambient Common型/行割当てρと所定outcome/planについて、
ある実返却制約付き分岐B・実生成fresh slot割当てιがBの制約をρ⊕ιで満たし、
所定のstatus/planを与えること iff 同じρでの独立interval evidence。
この存在割当ては実生成した制約の意味であり、candidateを発見する代入探索ではない。

全where-childが完成したselected demandについて、返される実有限dictionary Planと
独立有限dictionary evidenceの消去がちょうど一致する。
head選択だけでpending childを消した完成辞書を作らない。
```

raw goalに未解決名があることを新しいsupport/fuel/成功前提にしない。
pendingはresolverの正当な結果であり、lower headが既知の未実装branchをpendingで隠さない。
旧point matcherとの一致はB4の独立意味の定義ではない。
必要なら、実loweringと伝播がpinされたboundsに退化する範囲の保守拡張lemmaとして別途証明する。

HDAは同じimplのannotation slot接続が関連型等式を決める条件として扱う。
非退化interval中の全実型に対してRHSが同じという新しい過剰条件を足さない。
named recursionはIDと宣言済varianceの引数を読むだけでbodyを展開しないことを示す。

qualifiedの正確な不足lemmaは、任意verified D/V/method表・kind付き自由名A・scheme環境Γ・全式e・結果outについて、
実有限packageがmethod ID、ordinary/associated制約、interval demand、pending、weak/captured/generalized共有を保存し、
任意kind保存ambientρで独立QualifiedTyping iff 実生成local制約のmodelと全必要な独立有限interval dictionariesを持つこと。
未確定lowerのrole制約は消さずにscheme/residualへ保持する。
任意返却schemeの無制約parameter全てがmodelを与え、任意元modelを全type slotの要求同値・同一rowまで回収する。
Satisfies/残余条件を自由parameterへの追加条件にしない。

### 6.1 停止とPaterson check

pendingは「解けるまで再帰して待つ」操作ではない。有限queueの義務として保持し、そのsnapshotの処理は終了する。
通常bound propagationの有限worklist停止と、head選択に伴う新where生成の停止を分ける。
既存DemandBoundPropagation.request_exactは有限snapshotの実queryとreferenceの一致を与え、
それだけで新しいrole義務を無限に生成しないとは結論しない。

**Paterson-styleの宣言検査は今も必要な停止根拠であり、deferralだけでは置き換わらない。**
例えば既にheadが分かるintから始め、もし `impl R 'a where (list 'a): R` を許せば、
選択のたびにR(list int)、R(list(list int))、…のlower headも分かっており、pendingで止まる理由がない。
このimplは現行の「whereが小さい」という検査で宣言時に拒否する。
roleレベルacyclicityやdepth制限を導入する理由にはしない。

新しい下降lemmaは、任意の承認済宣言・実lower-head伝播による選択・任意の実where条件について、
そのchildが解決開始可能なら、Nと宣言varianceを反映した有限inspection/resource measureが親より真に小さいこと。
childのlower headが未確定ならpendingで処理を終える。
K2は匿名regular cycleをconstructor inspectionの無限な資源として使うことを禁止する。
この全体measureの構成と、実宣言checkからその下降を導く証明は**まだ未完成**である。
旧Form点代入の算術だけで証明済みとしない。

### 6.2 既存決定の必要性

| 既存決定 | deferred intervalモデルでの位置 |
|---|---|
| record tailの遅延・canonical subtraction | 基本deferralの具体例として残る。具体recordが来るまでtailを選ばない。単なるpending規則だけでは残余の正準性までは導かない |
| plain変数がmerged payload全体を受ける | plain変数への制約接続として残る。unionへの任意splitを導入しない |
| Nと宣言時stable Paterson拒否 | 選択後whereの生成停止を支える。intervalで保留するだけでは、全head既知の無限生成を除けない |
| K2 reached-root/constructor-inspection拒否 | 伝播・選択が再帰型を実際に要求する時に残る。pending型に再帰があるだけの拒否にはしない |
| named recursion対象外 | 維持。declared varianceを読み、bodyを展開しない |
| non-variable no-split | 最新variance訂正で要確認。box不変性を根拠に確定扱いしない |
| 拒否先行 | working choiceのまま。確定規則と混同しない |

区間化で上記決定が全て冗長になったとは判断しない。冗長性を主張するなら、同じ実propagation/evidenceでの保存定理が別に必要である。

## 7. 証明の順序と停止根拠

1. 新wrapperをendpoint pairだけで置き、既存Common lattice則からFits/Valid/merge/cross/pinのiffを閉じる。
   これは任意Common endpointで証明し、有限木への制限を付けない。
2. 既存LayerBoundTemplatesへ整合・交差制約を実生成し、任意ambient/local assignmentで生成iffと全model回収を閉じる。
   型代数、bound propagation、free-parameter familyを既存CommonBound*から再利用する。
3. 型宣言のvariance metadataと、主型＋全roleのcompact入力、共有slot/kind/level、variance読出しとreinstantiateを定義する。
   局所sandwichを使わず、旧referenceの全出現条件を独立意味で明示する。
4. 実head annotationから宣言済varianceに従ってcandidate制約を生成し、全branchの有限inspectionとcanonical record subtractionを接続する。
   non-variable splitは要確認のままにし、plain変数の承認をそれ以外へ一般化しない。
   lower headが分かるまでpending、伝播後の残存宣言の分類、選択後の全where投入の独立iffを証明する。
5. N/stable checkを「実interval接続が作る全bound family」に対して証明する。
   旧Form点代入のcheck_soundだけでこの全称命題を済ませない。
6. 共有slot/path原因の有限性とK2で許される有限inspectionを使い、通常制約の再collectとrole再帰の停止を分けて証明する。
   旧 `argsSize(goal)` をそのまま区間stateのmeasureと呼ばない。全whereとassociated再投入の新規義務を保持する。
7. 実Planの構築と独立interval evidenceのiff、退化point入力の一致、named recursionの非展開を閉じる。
8. qualified実生成と全familyへ接続する。届かなければ正確な不足lemmaを残し、親E1へ読み替えない。

既存CommonBoundRefの有限worklist停止を、slotを新しく作るrole全体の停止と同一視しない。
反例候補を探す場合も、実interval lowering・交差制約・readiness・全where再投入が生成することを先に証明する。
未指定の存在代入を反例の代わりに置かない。

## 8. 旧質問の取り下げと残る仕様境界

[Mark/int/anyの旧anchor質問](../questions/2026-11-08-b4r9-interval-candidate-anchor.md) は、
今回の「interval制約とdeferral・候補の伝播・代入を探索しない」というユーザー方向付けを受けて取り下げる。
任意代入の探索とlowerへの点固定の二択を、作業の土台や承認待ちとして残さない。
source例の具体的分類は、実際のlower生成とcandidate伝播から導く。

同日のvariance訂正によりnon-variable payloadの旧no-split決定は要確認へ戻った。
boxを使った旧例は撤回し、invariant例へ置き換える場合にも、矛盾したlist int/list bool合流を
well-typedな確定goalと偽って使わない。plain変数以外の新capture規則を勝手に確定しない。
この境界に依存しないinterval制約・伝播・pending・変数等式・where生成の証明を続ける。

## 付録: 既存CommonRole定理の全件索引

訂正時treeの `CommonRole*.lean` は65 module、明示的theorem宣言は733件。private lemmaも含む。
以下の索引は定理名の採録であり、intervalへの移送証明ではない。全て元のstatementでは保持する。
A/B/Pは§5の分類。混在moduleでは安全に再利用できる独立成分と、実resolverへのbridgeが要る部分を同じ行で区別する。

| module | 区間への適用範囲 | 全theorem名（当該ファイル内の宣言名。実namespaceはsource参照） |
|---|---|---|
| `CommonRoleActualEvidence` | P/B: 当該点/first-order/evidence/checkerモデルで真。実interval候補/辞書/E2への移送なし | `interpretTerm_encode`, `interpret_compile_head`, `interpret_compile_child`, `matches_compile`, `interpret_terminal_head`, `matches_terminal`, `unique_compile`, `unique_terminal`, `terminalAssignment_matches`, `ofSpecial_erase`, `toSpecial`, `dictionary_iff_special`, `Dictionary.derives`, `derives_to_special`, `derives_of_special`, `derives_iff_special`, `Dictionary.all_visible`, `associated_int_equation` |
| `CommonRoleAssociatedExactness` | P/B: 当該点/first-order/evidence/checkerモデルで真。実interval候補/辞書/E2への移送なし | `no_common_associated_registry_extension`, `checked_registry_counterexample` |
| `CommonRoleAssociatedObstructions` | P/B: 当該点/first-order/evidence/checkerモデルで真。実interval候補/辞書/E2への移送なし | `declaration_accepted`, `declaration_wellFormed`, `associated_wellFormed`, `every_head_instance`, `int_not_bool`, `no_associated_value_agrees`, `first_order_selected`, `first_order_resolved`, `first_order_associated`, `first_order_derivation`, `first_order_dictionary_plan`, `ground_head_equivalent`, `finite_ground_associated_conflict` |
| `CommonRoleCanonicalMergedEvidence` | P/B: 当該点/first-order/evidence/checkerモデルで真。実interval候補/辞書/E2への移送なし | `goal_finite`, `goal_ready`, `capture_reconstructs`, `capture_agrees`, `head_matches_exact`, `captures_unique_on_used`, `requirements_determined`, `matches_compile`, `matches_terminal`, `child_interpreted`, `Dictionary.all_visible` |
| `CommonRoleCanonicalPayloadCandidates` | P/B: 当該点/first-order/evidence/checkerモデルで真。実interval候補/辞書/E2への移送なし | `finite_ready`, `payload_capture_exact`, `head_capture_exact`, `head_matches_exact`, `mem_candidates`, `unsupported_explicit`, `example_supported`, `merged_capture`, `concrete_capture`, `actual_candidate_list`, `approved_ambiguous`, `other_payload_selected`, `actual_two_images`, `approved_independent_overlap`, `TerminalEvidence.all_visible`, `approved_no_dictionary`, `other_payload_dictionary`, `example_dictionary_exact`, `approved_no_plan`, `other_payload_plan`, `example_plan_exact` |
| `CommonRoleCanonicalRows` | A: 任意Payloadの有限row正規化・正準残余。interval payloadへの実接続は別 | `mem_residual`, `mem_selected`, `residual_excludes`, `residual_commute`, `residual_idempotent`, `residual_map`, `lookup_residual`, `lookup_normalize`, `normalize_unique`, `normalize_of_unique`, `normalize_idempotent`, `capture_unique`, `capture_no_hidden`, `capture_normalize`, `former_clock_removed`, `mass_partition`, `residual_mass_le`, `selected_positive`, `residual_mass_lt` |
| `CommonRoleCaptureNormalization` | A/B: 明示文法の意味保存/点HDA/有限算術。endpoint事実は再利用可、実interval生成へのbridgeなし | `subst_encode`, `subst_eval`, `join_congr`, `normalize_meaning`, `capture_zero_actual`, `symbolic_checked`, `symbolic_sizes`, `symbolic_occurrences`, `captured_head`, `captured_child`, `captured_sizes`, `normalization_capture_noncommute`, `symbolic_check_does_not_imply_captured_descent`, `late_check_rejects`, `capture_safe_rejects`, `actual_merge_entries`, `actual_merge_unique`, `coalesced_meaning`, `coalesced_checked`, `coalesced_size`, `coalesced_captured`, `coalesced_late_check_rejects` |
| `CommonRoleComputation` | A/B: 独立有限計算・構文・Common点解釈の事実。intervalからの還元/照合は別 | `Eval.deterministic`, `diverge_no_eval`, `diverge_not_halts`, `no_halting_classifier` |
| `CommonRoleFiniteShadowExamples` | P/B: 当該点/first-order/evidence/checkerモデルで真。実interval候補/辞書/E2への移送なし | `loop_sizes`, `loop_accepted`, `loop_ready`, `loop_matches`, `loop_child`, `growing_sizes`, `growing_accepted`, `normalized_examples_rejected`, `payload_finite`, `chain_ready`, `growing_step`, `payload_eval`, `chain_equivalent_iff`, `no_natural_descent_measure` |
| `CommonRoleFiniteShadowHalting` | P/B: 当該点/first-order/evidence/checkerモデルで真。実interval候補/辞書/E2への移送なし | `matched_step`, `unique_terminal`, `unique_compile`, `instantiate_lift_finite`, `machine_to_dictionary`, `dictionary_to_machine`, `dictionary_iff_machine`, `start_finite`, `dictionary_exact`, `actual_plan_exact` |
| `CommonRoleFiniteShadowObstruction` | P/B: 当該点/first-order/evidence/checkerモデルで真。実interval候補/辞書/E2への移送なし | `eval_queryCode`, `queryCode_exact`, `signature_actual`, `configuration_ready`, `no_total_finite_shadow_resolver`, `finite_tree_registry_undecidable` |
| `CommonRoleFiniteShadowRegistry` | P/B: 当該点/first-order/evidence/checkerモデルで真。実interval候補/辞書/E2への移送なし | `lift_size`, `lift_occurrences`, `compile_wellFormed`, `compile_accepted`, `declarations_wellFormed`, `declarations_accepted`, `environment_cores`, `environment_checked`, `head_determines_associated`, `visible_declared`, `constraints_declared`, `associated_wellFormed`, `head_equivalent`, `matches_compile`, `matches_terminal`, `child_interpreted` |
| `CommonRoleFiniteShadowSemantic` | P/B: 当該点/first-order/evidence/checkerモデルで真。実interval候補/辞書/E2への移送なし | `child_interpreted`, `reflect`, `of_machine`, `arbitrary_common_exact`, `guarded_iff_arbitrary_common` |
| `CommonRoleFiniteTailClock` | A/P: 有限構文/N/Common意味の事実と点時計/captureが混在。実interval還元は未証明 | `fork_size`, `fork_occurrences`, `lift_normal`, `clock_normal`, `fork_instantiate`, `fork_equivalent`, `atom_absorbs`, `head_clock_matches`, `clock_finite`, `capacity_positive`, `member_below_capacity`, `compile_normal`, `compile_wellFormed`, `compiled_checked`, `assignment_fresh`, `assignment_finite`, `assignment_data` |
| `CommonRoleFiniteTailExamples` | P/B: 当該点/first-order/evidence/checkerモデルで真。実interval候補/辞書/E2への移送なし | `old_verified_api_accepts`, `normalized_checked`, `declaration_fixed`, `declaration_sizes`, `goal_ready`, `head_matches`, `child_returns`, `normalization_does_not_commute_with_capture`, `post_capture_sizes`, `finite_children_differ`, `requirements_not_determined` |
| `CommonRoleFiniteTailHalting` | P/B: 当該点/first-order/evidence/checkerモデルで真。実interval候補/辞書/E2への移送なし | `unique_terminal`, `unique_compile`, `machine_to_dictionary`, `dictionary_to_machine`, `dictionary_iff_machine`, `start_finite`, `dictionary_exact`, `actual_plan_exact` |
| `CommonRoleFiniteTailObstruction` | P/B: 当該点/first-order/evidence/checkerモデルで真。実interval候補/辞書/E2への移送なし | `eval_queryCode`, `queryCode_exact`, `configuration_ready`, `no_total_normalized_resolver`, `normalized_registry_undecidable` |
| `CommonRoleFiniteTailRegistry` | P/B: 当該点/first-order/evidence/checkerモデルで真。実interval候補/辞書/E2への移送なし | `declarations_wellFormed`, `declarations_accepted`, `environment_cores`, `environment_checked`, `head_determines_associated`, `normalized_wellFormed`, `visible_declared`, `constraints_declared`, `associated_wellFormed`, `declarations_normal`, `matches_compile`, `matches_terminal`, `child_interpreted` |
| `CommonRoleFiniteTailSemantic` | P/B: 当該点/first-order/evidence/checkerモデルで真。実interval候補/辞書/E2への移送なし | `interpretGoal_commutes`, `forget`, `child_interpreted`, `reflect`, `arbitrary_common_exact`, `guarded_iff_arbitrary_common` |
| `CommonRoleHeadDetermination` | A/B: 明示文法の意味保存/点HDA/有限算術。endpoint事実は再利用可、実interval生成へのbridgeなし | `eval_congr`, `recoverable_sound`, `checkAssociated_sound`, `checkRegistry_sound`, `declaration_check_sound`, `verify_isSome_iff`, `verify_preserves_declaration`, `visible_associated_accepted`, `visible_associated_determined`, `hidden_associated_rejected`, `hidden_associated_not_determined`, `constant_associated_accepted`, `constant_associated_determined` |
| `CommonRoleInspectedSemantics` | P/B: 当該点/first-order/evidence/checkerモデルで真。実interval候補/辞書/E2への移送なし | `lift_eval`, `decode_encode`, `interpret_encode`, `finite_root`, `finite_view`, `finite_not_blocked_raw`, `finite_not_blocked`, `variable_capture_allowed`, `constructor_on_clock_rejected`, `finite_ready`, `instantiate_eval`, `interpretDescription_encode`, `not_ready_no_dictionary`, `Dictionary.all_visible` |
| `CommonRoleLinearClock` | A/B: 独立有限計算・構文・Common点解釈の事実。intervalからの還元/照合は別 | `instantiate_encode`, `instantiate_eval`, `checkLinear_exact`, `wrapPattern_size`, `wrapPattern_occurrences`, `compile_wellFormed`, `compile_accepted`, `terminal_accepted` |
| `CommonRoleLinearDictionaries` | P/B: 当該点/first-order/evidence/checkerモデルで真。実interval候補/辞書/E2への移送なし | `Reachable.trans`, `safe_child`, `no_semantic_head_overlap`, `no_reachable_overlap`, `resolves_iff_machine_halts`, `Dictionary.derives`, `machine_to_dictionary`, `dictionary_iff_machine_halts`, `Dictionary.all_visible` |
| `CommonRoleLinearEvidence` | P/B: 当該点/first-order/evidence/checkerモデルで真。実interval候補/辞書/E2への移送なし | `checkRegistry_exact`, `compiled_registry_accepted`, `compiled_registry_wellFormed`, `derives_transport`, `machine_to_derives`, `derives_to_machine`, `derives_iff_machine_halts` |
| `CommonRoleLinearExecution` | A/B: 独立有限計算・構文・Common点解釈の事実。intervalからの還元/照合は別 | `run_step`, `other_step`, `ret_step`, `copy_step`, `copied_step`, `run_code_present`, `step_reflect`, `raw_halting_outcome`, `copy_halting`, `evaluation_halting`, `halts_exact` |
| `CommonRoleLinearInterpreter` | A/B: 独立有限計算・構文・Common点解釈の事実。intervalからの還元/照合は別 | `Steps.trans`, `one_step`, `copy_steps`, `evaluation_steps`, `predecessor_outcome`, `outcome_of_steps`, `machine_exact` |
| `CommonRoleLinearInterpreterRules` | A/B: 独立有限計算・構文・Common点解釈の事実。intervalからの還元/照合は別 | `literal_instantiate`, `literal_occurrences`, `generic_linear`, `entry_linear`, `generic_step`, `entry_step` |
| `CommonRoleLinearMatching` | A/B: 独立有限計算・構文・Common点解釈の事実。intervalからの還元/照合は別 | `ground_heads`, `Ground.equivalent_iff`, `Pattern.eval_congr`, `int_not_pair`, `int_not_variant`, `pair_not_variant`, `extract_semantic`, `matchingAssignment_agrees`, `matchingAssignment_head`, `finite_match_reflection` |
| `CommonRoleLinearProgram` | A/B: 独立有限計算・構文・Common点解釈の事実。intervalからの還元/照合は別 | `generic_member`, `entry_member`, `rules_linear`, `compatible_of_equal`, `generic_matches_unique`, `generic_source`, `entry_source`, `entry_control`, `same_code_entry_unique`, `entry_matches_unique`, `rules_matches_unique`, `no_terminal_source`, `images_agree`, `instantiate_congr`, `linear_step_deterministic`, `step_deterministic` |
| `CommonRoleLinearRepresentation` | A/B: 独立有限計算・構文・Common点解釈の事実。intervalからの還元/照合は別 | `decodePattern_encode`, `pattern_encode_injective`, `compile_injective`, `compile_entry_eq_iff`, `terminal_ne_compile`, `compile_ne_terminal` |
| `CommonRoleLinearSimulation` | A/B: 独立有限計算・構文・Common点解釈の事実。intervalからの還元/照合は別 | `wrapPattern_eval`, `clock_unfold`, `wrapped_clock`, `clock_cancel`, `clockAssignment_eval`, `GoalEquivalent.refl`, `GoalEquivalent.symm`, `GoalEquivalent.trans`, `compiled_patterns`, `matched_child_finite`, `finite_step_instance`, `instanceStep_iff` |
| `CommonRoleLinearSubcodes` | A/B: 独立有限計算・構文・Common点解釈の事実。intervalからの還元/照合は別 | `self_mem_subcodes`, `pair_first_subcodes`, `pair_last_subcodes`, `seq_first_subcodes`, `seq_last_subcodes`, `cond_test_subcodes`, `cond_yes_subcodes`, `cond_no_subcodes`, `while_test_subcodes`, `while_body_subcodes`, `pair_first_mem`, `pair_last_mem`, `seq_first_mem`, `seq_last_mem`, `cond_test_mem`, `cond_yes_mem`, `cond_no_mem`, `while_test_mem`, `while_body_mem`, `subcodes_trans`, `tree_encode_injective`, `code_encode_injective` |
| `CommonRoleMergedCaptureBoundary` | P/B: 当該点/first-order/evidence/checkerモデルで真。実interval候補/辞書/E2への移送なし | `stable_checked`, `wellFormed`, `environment_cores`, `associated_determined`, `merged_head_interpreted`, `concrete_head_interpreted`, `full_payload_head`, `separated_payload_head`, `bottom_not_int`, `completions_differ`, `distinct_declarations` |
| `CommonRoleMergedExamples` | P/B: 当該点/first-order/evidence/checkerモデルで真。実interval候補/辞書/E2への移送なし | `minimal_checked`, `growing_checked`, `minimal_sizes`, `growing_sizes_occurrences`, `minimal_normal`, `minimal_from_merge`, `minimal_matches`, `minimal_child`, `no_finite_self_dictionary`, `no_self_descent_measure`, `proposed_rejects_minimal`, `proposed_rejects_growing` |
| `CommonRoleMergedHalting` | P/B: 当該点/first-order/evidence/checkerモデルで真。実interval候補/辞書/E2への移送なし | `unique_terminal`, `unique_compile`, `machine_to_dictionary`, `dictionary_to_machine`, `dictionary_iff_machine`, `dictionary_exact`, `actual_plan_exact` |
| `CommonRoleMergedObstruction` | P/B: 当該点/first-order/evidence/checkerモデルで真。実interval候補/辞書/E2への移送なし | `start_description`, `eval_queryCode`, `queryCode_exact`, `no_total_canonical_merged_resolver`, `canonical_merged_registry_undecidable` |
| `CommonRoleMergedPayload` | A/P: 有限構文/N/Common意味の事実と点時計/captureが混在。実interval還元は未証明 | `merged_entries`, `merged_tag_unique`, `interpret_data`, `interpret_padded`, `padded_equivalent`, `interpret_head`, `head_meaning`, `unlift_lift`, `decode_data`, `contract_data`, `contract_padded`, `decode_head`, `data_size`, `data_occurrences`, `padded_size`, `padded_occurrences` |
| `CommonRoleMergedRegistry` | P/B: 当該点/first-order/evidence/checkerモデルで真。実interval候補/辞書/E2への移送なし | `normalize_head`, `compile_normal`, `compile_wellFormed`, `checkImpl_sound`, `compile_checked`, `merged_head`, `all_heads_from_merge`, `declarations_wellFormed`, `declarations_normal`, `environment_cores`, `checkEnvironment_sound`, `environment_checked`, `visible_declared`, `constraints_declared`, `associated_wellFormed` |
| `CommonRoleMergedSemantic` | P/B: 当該点/first-order/evidence/checkerモデルで真。実interval候補/辞書/E2への移送なし | `generated_match_exact`, `requirements_determined_common`, `pattern_determines_used`, `requirements_determined_all_common`, `generated_candidate_exact`, `visible_candidate_exact`, `unique_common`, `child_interpreted`, `head_determines_requirements`, `reflect`, `of_machine`, `arbitrary_common_exact`, `canonical_iff_arbitrary_common` |
| `CommonRoleNominalCoverBoundary` | P/A: 旧point nominal API・有限cover提案実験・有限term算術。宣言variance付きの新same-pathモデルには移送しない | `argument_equivalent_exact`, `box_invariant`, `coded_box_exact`, `boxes_distinct`, `joined_not_integer`, `joined_not_boolean`, `no_single_box_upper`, `cover_exact`, `covers_enumerated`, `forward_cover`, `reverse_cover`, `joined_fails`, `covers_change_child`, `private_child_decreases`, `all_term_substitutions_decrease`, `allow_cover_two_candidates`, `forbid_cover_one_candidate` |
| `CommonRoleNormalizedDeclarations` | A/B: 明示文法の意味保存/点HDA/有限算術。endpoint事実は再利用可、実interval生成へのbridgeなし | `tail_of_equivalent`, `tail_trans`, `hidden_tail`, `record_congr`, `normalize_meaning`, `normalizeTerm_encode`, `normalizeTerm_meaning`, `normalized_head_match_exact`, `checkImpl_sound`, `checkEnvironment_sound`, `another_size_erasure`, `union_padding_scope` |
| `CommonRolePackedHalting` | P/B: 当該点/first-order/evidence/checkerモデルで真。実interval候補/辞書/E2への移送なし | `descriptionAssignment_eval`, `finite_step_description`, `machine_to_dictionary`, `derives_to_old`, `dictionary_iff_machine`, `dictionary_exact`, `no_rejection`, `actual_plan_exact` |
| `CommonRolePackedRegistry` | P/B: 当該点/first-order/evidence/checkerモデルで真。実interval候補/辞書/E2への移送なし | `packGoal_injective`, `packImpl_injective`, `packImpl_wellFormed`, `declarations_wellFormed`, `declarations_accepted`, `environment_cores`, `environment_checked`, `head_determines_associated`, `constraints_declared`, `associated_wellFormed`, `packed_head`, `packed_child`, `matches_compile`, `terminal_head`, `matches_to_actual`, `unique_of_actual` |
| `CommonRolePackedSemanticReflection` | P/B: 当該点/first-order/evidence/checkerモデルで真。実interval候補/辞書/E2への移送なし | `packed_head`, `packed_child`, `terminal_head`, `matches_compile`, `matches_to_actual`, `arbitrary_unique`, `unique_at_configuration`, `reflect`, `of_old`, `arbitrary_common_exact`, `guarded_iff_arbitrary_common` |
| `CommonRoleReachedRoot` | P/B: 当該点/first-order/evidence/checkerモデルで真。実interval候補/辞書/E2への移送なし | `clock_rejected`, `pair_not_recursive`, `finite_not_recursive`, `recursive_unrolling`, `instantiate_eval`, `interpretTerm_encode`, `Dictionary.derives`, `recursive_has_no_dictionary`, `Dictionary.all_visible` |
| `CommonRoleReachedRootExamples` | P/B: 当該点/first-order/evidence/checkerモデルで真。実interval候補/辞書/E2への移送なし | `declaration_sizes`, `declaration_accepted`, `root_not_recursive`, `root_matches`, `child_returns_to_goal`, `unique_head`, `no_rejection` |
| `CommonRoleReachedRootObstruction` | P/B: 当該点/first-order/evidence/checkerモデルで真。実interval候補/辞書/E2への移送なし | `eval_queryCode`, `queryCode_exact`, `signature_actual`, `no_total_reached_root_resolver`, `reached_root_registry_undecidable` |
| `CommonRoleRegularHalting` | P/B: 当該点/first-order/evidence/checkerモデルで真。実interval候補/辞書/E2への移送なし | `machine_iff_raw`, `machine_halts_exact`, `derives_exact`, `resolves_exact`, `dictionary_exact`, `no_ambiguity`, `actual_plan_exact` |
| `CommonRoleRegularObstructions` | P/B: 当該点/first-order/evidence/checkerモデルで真。実interval候補/辞書/E2への移送なし | `declaration_sizes`, `declaration_accepted`, `declaration_wellFormed`, `observe_loop_wrap`, `loop_unfold`, `chain_step`, `int_not_wrap`, `growing_equivalent_iff`, `chain_equivalent_iff`, `chain_fresh`, `no_natural_descent_measure` |
| `CommonRoleRegularRegistry` | P/B: 当該点/first-order/evidence/checkerモデルで真。実interval候補/辞書/E2への移送なし | `mem_registry`, `registry_linear`, `declarations_accepted`, `declarations_wellFormed`, `no_overlap`, `registry_safe`, `entry_key_unique`, `environment_cores`, `roles_lt`, `rule_source_bound`, `rule_target_bound`, `visible_shape`, `constraints_declared`, `associated_wellFormed`, `checkConstantAssociated_sound`, `head_determines_associated`, `checkDeclaration_sound`, `each_declaration_checked` |
| `CommonRoleRegularResolutionObstruction` | P/B: 当該点/first-order/evidence/checkerモデルで真。実interval候補/辞書/E2への移送なし | `checkAssociated_sound`, `checkEnvironment_sound`, `environment_checked`, `amended_preconditions`, `associated_equations`, `actual_derives_exact`, `actual_dictionary_exact`, `no_total_actual_regular_resolver`, `amended_registry_undecidable` |
| `CommonRoleRegularUndecidability` | A/B: 独立有限計算・構文・Common点解釈の事実。intervalからの還元/照合は別 | `no_total_regular_role_classifier`, `no_total_regular_dictionary_classifier` |
| `CommonRoleRegularWire` | P/B: 当該点/first-order/evidence/checkerモデルで真。実interval候補/辞書/E2への移送なし | `termsWire_list`, `signatureAt_exact`, `databaseWire_actual`, `clockGraph_actual`, `clockGraph_denotes`, `data_denotes`, `startGoal_denotes`, `eval_taggedCode`, `eval_queryCode`, `queryCode_exact`, `tagged_eq_iff`, `congrArg2`, `listWire_injective`, `termWire_injective`, `termsWire_injective`, `goalPatternWire_injective`, `implWire_injective`, `associatedBodyWire_injective`, `assocImplWire_injective`, `groundWire_injective` |
| `CommonRoleRewrite` | A/B: 独立有限計算・構文・Common点解釈の事実。intervalからの還元/照合は別 | `compile_checked`, `compiled_head_iff`, `compiled_matches_iff`, `evidence_iff_halting`, `no_compiled_evidence_decider` |
| `CommonRoleSemanticPadding` | A/B: 明示文法の意味保存/点HDA/有限算術。endpoint事実は再利用可、実interval生成へのbridgeなし | `padded_declaration_accepted`, `padded_head_exact` |
| `CommonRoleSharedCaptureDescent` | P/B: 当該点/first-order/evidence/checkerモデルで真。実interval候補/辞書/E2への移送なし | `encode_variables`, `normalized_variables`, `actual_head_is_goal`, `canonical_capture_strictly_decreases` |
| `CommonRoleSharedPayloadAgreement` | P/B: 当該点/first-order/evidence/checkerモデルで真。実interval候補/辞書/E2への移送なし | `previous_merged_matches`, `previous_concrete_exact`, `canonical_concrete_exact`, `finite_head_agreement`, `previous_no_unique_at_int`, `previous_unique_other`, `previous_selected_plan`, `actual_plan_agrees_previous` |
| `CommonRoleSharedPayloadCapture` | A/P: lookup/有限表/opaque値保存はA、interpret_payload/approved_head_meaning等のhead解釈は点モデルP | `lookup_repeated_payload`, `assignment_exact`, `captured_as_is`, `unmentioned`, `bindings_unique`, `capture_sound`, `capture_complete`, `capture_exact`, `capture_unique`, `both_same`, `duplicate_unchanged`, `total_captured_as_is`, `actual_merge`, `interpret_payload`, `approved_head_meaning`, `approved_two`, `no_bottom_split` |
| `CommonRoleStablePaterson` | B: finite Formの全点代入に対する算術checker。全interval捕捉への移送なし | `normalize_idempotent`, `normalize_subst`, `normalize_before_subst`, `normalize_size_le`, `normalize_occurrences_le`, `lower_size`, `lower_occurrences`, `upper_size`, `upper_occurrences`, `term_subst_occurrences`, `args_subst_occurrences`, `occurrence_mono`, `head_size_bound`, `child_size_bound`, `head_occurrences_bound`, `child_occurrences_bound`, `check_comparison_exact`, `check_sound`, `subst_identity`, `instantiated_identity`, `accepted_wellFormed`, `unary_accepted`, `rebuilding_accepted`, `previous_rejected`, `repeated_accepted`, `constant_accepted`, `terminal_accepted` |
| `CommonRoleStableRecordResidual` | A/B: 任意重みの有限row下降。interval head/where下降へのbridgeは未証明 | `lookup_member`, `matching_explicit_entry`, `capture_is_normal`, `residual_count_le`, `checked_residual_decreases`, `repeated_label_allowed`, `empty_head_rejected` |
| `CommonRoleTreeReflection` | A/B: 明示文法の意味保存/点HDA/有限算術。endpoint事実は再利用可、実interval生成へのbridgeなし | `pattern_match_reflects` |
| `CommonRoleTuringBridge` | A/B: 独立有限計算・構文・Common点解釈の事実。intervalからの還元/照合は別 | `eval_left`, `eval_right`, `eval_project`, `eval_eqConst`, `encodeNat_injective`, `encodeBool_injective`, `encode_head`, `encode_tail`, `eval_state`, `eval_leftTape`, `eval_current`, `eval_rightTape`, `eval_updateCode`, `eval_matchCode`, `eval_runningCode`, `eval_stepCode`, `eval_running_stopped`, `eval_running_transition`, `eval_step_transition`, `compile_of_runs`, `machine_of_eval`, `runs_of_compile`, `compile_exact`, `compile_halts_iff`, `decodeBits_append`, `decode_serialize`, `serialize_injective`, `eval_serializeBody_leaf`, `eval_serializeBody_node`, `eval_serializeLoop`, `eval_serializeCode`, `eval_initialCode`, `classifier_of_runs`, `classifier_exact`, `no_turing_halting_classifier` |
| `CommonRoleTuringDelimited` | A/B: 独立有限計算・構文・Common点解釈の事実。intervalからの還元/照合は別 | `frameOnto_append`, `reads_frameBits`, `ReadsFrame.deterministic`, `frame_stream_prefix_free`, `stream_blank`, `initial_tape_injective`, `eval_frameBody`, `eval_frameLoop`, `eval_frameCode`, `eval_initialCode`, `classifier_of_runs`, `classifier_exact`, `no_turing_halting_classifier` |
| `CommonRoleWhereExactness` | A/B: 明示文法の意味保存/点HDA/有限算術。endpoint事実は再利用可、実interval生成へのbridgeなし | `no_common_dictionary_registry_extension`, `checked_dictionary_transport_counterexample` |
| `CommonRoleWhereObstructions` | P/B: 当該点/first-order/evidence/checkerモデルで真。実interval候補/辞書/E2への移送なし | `declarations_accepted`, `declarations_wellFormed`, `root_sizes`, `int_dictionary_plan`, `bool_dictionary_plan`, `actual_int_elaboration`, `actual_bool_elaboration`, `plans_differ`, `environment_cores`, `associated_wellFormed`, `encoded_declarations`, `encoded_associated_bodies`, `associated_checker_accepts`, `head_determines_associated`, `combined_declaration_check_accepts`, `each_declaration_verified`, `root_associated_is_int`, `root_goals_equivalent`, `where_argument_not_determined` |
