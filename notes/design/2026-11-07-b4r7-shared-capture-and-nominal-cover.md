# B4r7: 共有payload捕捉とnon-variable nominal branch

状態: **component証明と一問、full E1/E2未到達**（2026-11-08）。
第六回の質問への承認をspec6.3から読み、plain変数branchの実captureを実装した。
同時に、non-variable nominal branchの有限coverは未決として切り分けた。

## 1. 全head branchの作業地図

| branch | 決まっている運用 / 今回の到達点 | 全目標へ残るもの |
| --- | --- | --- |
| plain変数、同tag下のplain変数群 | supplied merged payloadを全変数へそのまま保存。任意opaque Payloadで実有限表を計算し、lookup仕様とのiff/一意性を証明 | 他のhead位置からの同変数拘束、全graph型比較との統合 |
| 基底型 / any / never / unit | 既知の型・kindを比較する。今回の実candidate componentはintと有限Groundを扱う | 全scalar/goal型の比較、full Common Nへのbridge |
| tuple/pair | Commonのpair_union_groupにより、同shape producer unionは成分ごとに合流する。再構成全体の照合を行う必要がある | 全tuple shapeのcanonical projectionと再構成チェックの完全性 |
| record | first-winsで可視fieldを読む。tailは具体goalから明示labelを引くcanonical residual。既存実row componentで下降済み | 全payload照合、mask/optional/推論されたtailとの結合、全source checker |
| closed variant row | tagごとに合流、plain payload変数は共有capture。実merge→stored payload→computed assignmentのbridge済み | non-variable payload一般、異なる構成子を持つmerge、full N |
| arrowとeffect row | 既存Common.arrow iffがdomain/resultと両rowを反映。注釈から未指定のrow代入を選ばない | 実分解/capture/graph比較の全実装と完全性 |
| nominalとnamed再帰 | ID/arity/kind/順序とinvariant引数を保持。bodyは展開しない | 複数nominal alternativeへのnon-variable照合/captureが今回の一問。一般nominal resolver agreementも未証明 |
| alias | transparent aliasはhead elaborationで展開し、nominalと取り違えない | 全source lowering / 同値Nのbridge |
| optional field | 推論/表示の形をsource head注釈と勝手に同一視しない | 全inferred requirementとの対応 |
| associated | 他roleのprojectionを展開しない。既存HDAとordinary equationを保つ | full選択/辞書/生成への結合 |
| anonymous regular graph | rootに到達した拒否、非変数constructor検査時の拒否は維持 | 全graphの実classifier/有限decompositionとmeasureへの統合 |

この表は全文法のmatcherを完成したという意味ではない。
未対応branchを「候補がない」としてfull E1へ流すことはしない。
今回のcomponent classifierは範囲外を明示的にunsupportedと返す。これはsource言語の新しい拒否ではない。

## 2. plain変数の実共有capture

`CommonRoleSharedPayloadCapture.bindings names payload` は、各nameに同じpayloadを持つ有限entry列を作り、
first-winsの実normalizeで重複名を除く。
`assignment` はその実lookupであり、payloadのconstructorを一切調べない。
任意Payload型で同じ関数を使うため、regular記述やnominal情報の内部を捕捉時に復元する操作はない。
周囲のrole根のK2チェックが省略できるという意味ではない。

独立仕様 `Captures names payload image` は、所属名はsome payload、不在名はnoneという二つの全称条件。
実assignmentがその仕様を満たすiffを証明し、像を一意にする。
任意の同値splitを探索する「∃Common代入」ではない。
total化のfallbackは不在名だけに使い、実headが読む所属名は常にpayloadそのもの。

実Variants.Merged.normalizeにvariable branchesを渡したstored rowを計算し、
そのheadを計算済captureで解釈すると、同payloadの反復unionになることを証明した。
Commonでのidempotenceにより、元のsupplied payloadと同じhead意味になる。
任意Common解釈を量化するlemmaはこの意味保存の比較であり、未指定の操作的captureを仮定していない。

## 3. 実候補、曖昧性、terminal辞書

`CommonRoleCanonicalPayloadCandidates` は実Roles.Implのrole/head fieldsを読む。
このcomponentの文法はplain-variable mergeとint payloadだけ。
goal payloadは有限Ground。任意opaque Payloadの共有capture関数を、ここでは有限Groundへinstantiateする。
compound非変数をunsupportedとして区別し、full sourceのnoImplへ読み替えない。

tryCaptureの実table存在 iff 独立HeadCapturesという定理を証明した。
独立判断はrole/tag一致と、実格納headの構文解釈、上のpointwise Capturesを読む。
candidate filterやclassifyHeads自体を独立意味の定義にしていない。

第六回の実二implについて、任意Ground payloadで候補列を正確に計算する。
intでは二候補でambiguous、それ以外は第一implに一意。
独立TerminalEvidenceは全実where=[]、実所属、capture、一意性を必須とし、実RoleDictionaries.Planへ消去する。
intでは辞書/Planがなく、一意な場合は実第一implと全child列[]を返す。
一般のnested whereをterminal判断へ置き換えたとは言わない。

`CommonRoleSharedPayloadAgreement` は、この有限familyの候補存在を旧独立Common Matchesとiffにする。
旧側に任意Common像の存在が現れるが、新captureは既に計算済みで、その明示像を証明に用いる。
旧候補の一意性と実Plan返却も一致する。これは全Common finite-tree agreementの代用ではない。

## 4. stable checkerへの接続

`CommonRoleSharedCaptureDescent` はvariable groupのForm templateを実stored Termへencodeし、
計算済shared capture後のN head引数が、N済goal引数そのものになることを示す。
既存stable checkerの全Form代入soundnessを**この計算済capture**にinstantiateし、
実where childのN後sizeが実N済goalより真に小さく、全occが非増加とする。
任意solver代入を新しい外部前提として渡していない。
ここはfinite Form/idempotence stageであり、全Common/regular Nの完成ではない。

## 5. non-variable nominalの一問

tupleのunion-of-pairsでは、per-original-branchの完全一致だけを要求するmatcherは不完全になる。
既存Commonの成分合流があるため、それを同じ意味を保つ対等な言語案として質問しない。

nominal引数は不変なので事情が違う。
実CommonNominalHeads APIで、任意引数A,Bについてbox A subtype box B iff A≈Bを証明した。
box intとbox boolは異なり、box(int|bool)へ引数を合流して両方を置き換えることはできない。
保持されたpost-merge alternativesを有限coverでnominal branchへ割り当ててよいかは、
plain変数の「payload全体を捕捉する」規則だけでは決まらない。

[一問](../questions/2026-11-07-b4r7-nominal-alternative-capture.md) は、型を先にbox int/box boolへ確定した値をifで合流するsource例を使う。
選択肢はfinite coverとwhere決定性の宣言検査（推奨）、finite coverのcanonical順選択、cover不許可。
推奨のwhere決定性条件は**未承認の提案**。現在の定理の前提へ黙って足していない。
関連型の既存HDAは維持する。

`CommonRoleNominalCoverBoundary` のCoversは、int/bool/int|boolの三codeの有限support実験。
実bool cover iff実nominal APIによる有限support関係を証明し、二coverを有限列挙した。
これは全Commonのnominal-union head matchingのsmall-model theoremでも、nested nominal carrierでもない。
全captureの探索結果をこの三codeへ制限できるという主張はない。

size-only nominalFrameでは、同一alternativeのみを縮約した実Term frameが第一引数より大きく、
全occが第一引数以上であることを任意有限Term代入について示す。
二coverがwhere変数へ別の型を渡せるという点は、size下降だけで自動的に消える問題ではない。
これをfull source declaration checkerがその例を必ず受理すると示した定理にはしない。

## 6. 正確な不足

必要なfull matcher lemmaは、任意verified registry D、任意型/行確定finite regular goal gについて、
specが指定した有限capture/inspection計算のcandidate/reject結果 iff独立head判断。
captureは任意Common splitとして外から供給せず、実分解と再構成から得る。
今回のnominal operationが未決な間に、このlemmaの意味を独断で完成しない。

必要なfull descent lemmaは、任意同accepted宣言i、任意同実capture σ、任意c∈i.whereで、
N済child measure<N済goal measure、全対応occ非増加。
これを全regular graphでwell-founded実resolverへ接続し、selection/rejection/ambiguityと全実辞書のiff、
一般finite-tree agreement、named nominal agreementを証明することが残る。
既存のchecker/record componentを、全head grammarの同名E1へ読み替えない。

qualifiedの未証明lemmaは、任意finite verified D/visible V/method M、finite kind付き自由名A、
scheme環境Γ、full式e、結果outについて、実有限package Cを生成し、method ID/ordinary・associated等式/
pending role goals/weak-captured-generalizedを保ち、任意kind保存Common割当てρで、
独立QualifiedTyping(D,V,M,Γ.evalρ,e,out.evalρ) iff
あるkind保存local割当てιがCのordinary/associated制約、canonical residual/K2を含む全独立role辞書、
同captured共有と各使用generalizedを満たすこと。
全返却schemeの任意無制約parameterがmodelを与え、全元modelを同じrow/要求同値の全type slotで回収する全familyも残る。
未解決tailは具体化までpending。Satisfiesをparameterの追加条件にしない。

E1/E2には未到達。contract addendumと今回の明示指示に従い、未指定のnon-variable branchを一問へ置いた。
RoleRank/fuel/depth bound、coinductive辞書、新しい利用時Paterson拒否は導入しない。
拒否先行は依然working choiceであり、specへ確定事項として追記しない。
