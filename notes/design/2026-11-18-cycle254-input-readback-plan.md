# Cycle254: 個別入力readbackから出力深さへ
開始2026-11-18T10:35:05Z。最新integration155c7aa0c、I50継続。
前回253全公開treeと手元bytes一致、前回completed、実行中writerなし。

## 先に閉じる主張
実Frame、Holds model、ground Inputs labelsがある任意のplanについて、
全inputNamesの各nameに、model(binder name)と同値な閉じた正規Patternが存在し、
そのencode sizeとconstructor depthをsource labelsのmassで抑える。
253のcoveredHeadやwhere非空は要求しない。代わりに実完了inspectionから
Complete query、正規化済みtemplateからcanonical shapeを導く。

証明経路:
1. finiteな親Patternの実observational projectionは、親以下のsizeの
   finiteな子Patternを持つ（既存inversion/project_valueを用いる）。
2. query.variablesの複数nameは各々同じprojectionを参照する。
   名前ごとのboundを証明する。複数nameのsizeを足したjoint boundとはしない。
3. Complete translationで各head input nameが失われない既存定理を使い、
   実head schemaとsource labelへ接続する。
4. produced child outputとassociated RHSへの接続は、この定理の後に進める。

## 停止性との境界
これは各modelのreadback存在であって、全model共通の実行producerではない。
全source Step Acc、source pool閉包、private非流出、strict progressは残る。
狭いnamed-output poolの閉包は253で診断済みなので再実装しない。
規則の変更も意味論の選択もしない。I49のsource反例停止条件に該当する
新しい反例が出た場合は、該当依存を止めて分析を記録する。

## 第2段の接続と未完境界（10:54 UTC）
実child要求のtargetは、Producedで指定されたparent output binderと一致した。
defaultは役割の位置引数を読むため、impl binderと分けてRoles.TermをPatternへ写し、
RoleDecl.defaultsScopedから有限入力の代入を証明した。
既存Evidence treeとsource traceが与えられれば全要求outputに有限な閉じた代表が
あることを証明。Evidenceの存在・生成、実schedulerの停止は仮定から消していない。
さらに実source traceのsites_boundedを使い、各入力名のsizeを元rootLabels massへ
接続した。静的child producer graphは、子identityが親identityより大きく、
source由来の有限frontierに含まれるため整礎。alias/equation graphとは別物。

次は、要求名をroot要求＋registryのwhere出力名の有限集合へ列挙する。
これが実traceで保たれれば、explicit/defaultのbodyの深さも固定有限menuから取れる。
そのbudgetとproducer graphの有限rankを組み合わせ、Evidenceから構成する代表の
上界をsource量で抑える。これは未解決・未証明状態全体のsnapshot閉包ではない。

## Phase 3: source-uniform additive budget

The source mass bridge is now proved in `GeneralNominalSourceReadback254.input_bound`. The local input-label bound reviewed independently in phase1 is therefore connected to the original source root mass by a new theorem (not independently reviewed).

`GeneralNominalOutputMenu254` derives a finite menu of possible requested names from the initial root and registry where-clauses. Defaults are looked up only at these names, so no finiteness assumption on the defaults map is made. Explicit and default body depths have one budget T. `GeneralNominalProducerRank254` counts remaining source-frontier identities, retaining duplicates. An actual child-call edge strictly decreases this rank. The frontier contains N=(1+branching)^R entries, where R is initial normalized input mass. This is not a bound on scheduler refreshes.

`GeneralNominalSourceOutputDepth254.mixed_uniform` and `point_uniform` establish one D=R+T*N before quantifying over future states and models. Every requested output WITH a current finite Evidence tree has a closed semantic representative of raw depth at most D. Representatives themselves may depend on the model. The proof does not generate Evidence, bound unevidenced intermediate equations, show second-normalization depth preservation, prove full state support closure, or prove operational Step Acc.

A real nonvacuous cycle252 initial Evidence tree is constructed; all later models with Evidence for that root satisfy depth4, rather than the falsified maximum2. This is a real existing source regression, not an arbitrary favorable evidence assumption at the initial state.

## Phase 4: separate raw template result (before implementation)

Add `GeneralNominalRawOutputBudget254`: a finite list of expression templates is
obtained by compiling the source/registry finite body menu under the immutable
source interpretation. For every actual reachable Frame, requested output,
Supplies provenance, and successful compileBody, the resulting raw Expr belongs
to this list. This needs neither Models nor Evidence. A maximum rawDepth bounds
all such expressions, and arbitrary replacement of variables by source-name
references preserves this raw depth by cycle253's reference_depth theorem.
The source names in those references are NOT proved finite here; this is only
the template half of raw journal finiteness. Other atom kinds and whole-state
closure remain open. Raw explicit templates are compiled without a normalizing
pass, exactly as compileBody does, unlike normalized semantic bodyDepth.

## 実際に残る停止性の穴（後半自己点検）

- ground代表の上界では `∃D, ∀state, ∀model, ∀Evidence, ∃representative` の順序。
  `∃representative, ∀model` ではない。Evidenceがない未解決の出力に、この結果を
  当てて有限poolを作ることはできない。
- static EdgeのFrameはSelectedの仮定を持たない。candidate-frame child-callの
  順序として正しいが、型等式のalias graphやsource constructor containmentの
  graphと同一ではない。I50の循環時K2拒否の条件を閉じたとは言わない。
- RawOutputBudget254では現実のcompileBodyが生成する有限Expr templateを得た。
  Models/Evidenceは不要。しかし実referenceの名の有限列挙を別に要する。
  出力body以外のhead schema、center7/8/9、refreshされたatom種別も残る。
- `GeneralPresenceSnapshotNormal252.lower_exact/upper_exact` のconsumerが要求する
  のは、全旧atomのmapping後atoms⊆poolという構文上の閉包。意味同値な浅い代表の
  存在では置き換えられない。PublicBasis253はvarだけのpoolなので、非var atom
  の扱い（public参照に置換する手続きとその意味保存）を先に仕様化する必要がある。
- 追加回帰では4つの異なるvariant tagをbalanced joinした閉じたPatternが、
  normalizeでright-associated rowになって深さ4→5となることもstrict証明した。
  これは構文のみの境界検査でsource到達の新反例ではない。再normalize後の深さへ
  無条件に読み替えない、という既存の制限が実際に必要なことを示す。
- したがって次の大きな補題は `PublicBasisSourceClosure` の具体的置換と全atom分類。
  その後、private非流出を全source traceへ持ち上げ、同内容reobserveを除いた
  strict新factまたは細分化測度を構成する。有限poolの存在だけではAccは出ない。

### 次のpool拡張で分類すべきcenterの正確な場合

`GeneralNominalCenters.rootSite` はpoint入力なら既存端点、非pointならpurpose7。
今回のsource boundaryはpointなので初期purpose7を無条件に追加する必要はない。
`Plan.binder` はoutputNamesならpurpose2、input captureの両端が同名ならその端点、
それ以外はpurpose8(name,0)。`Plan.emittedCenter` はnormalized clause引数がvarなら
binderを継承し、compoundならpurpose9(clause.id,index)。versioned側にもこれらとの
一致補題がある。このためpurpose8/9の有限列挙だけでは不十分で、binderが継承する
実端点名がpublic pool内であることをtrace全体で証明する必要がある。旧private
aggregateを単にpublicとみなす拡張はしない。次回はこの分類をclosure設計へ使う。
