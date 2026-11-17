# cycle244: materialized journal の物理置換とモデル同値レビュー

## 状態と検証の区別

対象は I47 の既存案Aの内部補助。言語意味・選択・停止条件を変更しない。
今回の3モジュールは、環境置換前に direct trust0 / warningAsError の検証が
成功した。その後の独立公理監査中に環境が失われた。会話中のソースから
復元した現在の3ファイルは**再検証未了**であり、以前の成功をそのまま
現在のバイト列の検証証明として扱わない。独立公理監査の成功も未確認。
新しい Origin/Projection congruence の2草稿は検証しておらず成果に含めない。
大規模依存再構築は禁止に従って行わない。

## 243 からの実質差分

243 の `JournalView.compile state mapping` は保存された実 kernel state を
走査して有限 expression journal を作る。`JournalSupport.sources` はその
有限構造の全 semantic read set を生成し、read set 上の assignment の
**文字通りの等号**から Models 同値を得る。これは新セル activation に使える。

244 の3ファイルは既にある任意の expression journal を入力とする。
保存 state、元 plan、registry を読み直して再 compile する必要がない。
各 expression に有限 substitution を施し、任意 mapping/model に対して
`Models (subst J mapping) model ↔ Models J (read mapping model)` を狙う。
この任意 syntax の量化により、最初の compile 後の複数回 rebase に使える。
ただしこれは操作系、選択、metadata、停止性を自動的に更新するものではない。

## 3ファイルの全成分・量化子レビュー

### ProjectionSubst244

* Bounds: lower / upper の両 TyTerm を置換。Fits の actual は任意に固定。
* Capture: name は保持、bounds を置換、optional origin を map。
* Report anchors: origin と bounds の双方を置換。
* Report tests: origin を置換、Test は同一のまま。
* captures の交差条件: 全 first/last、同名条件、全 origin、全 actual を保持。
  第二の交差条件では全 a/b と全 x/y の証人を保持する。optional origin の
  none と some を場合分けし、置換による origin 構文の衝突を単射性の仮定で
  排除してはいない。Option.map の存在元へ戻すだけでよい。
* anchor の観測存在と、すべての観測に対する Fits を両方保持する。
  test の原条件は観測に対する全称のみで、存在を勝手に加えていない。

### PacketSubst244

* Requirement の equal と interval 両ケース、全端点を置換。
* Use.same の二つの origin を置換。Use.observed は存在と全称の両条件を保持。
* Schema の tests/uses を map、unknown flag は同一。unknown_kept は定義等号。
* Equation の target TyTerm と完全な Effect.Expr をともに置換。
  既存 EffectView.subst は nominal 内部の actual-mode 済み構文を維持する。
* Child は site と全 equations を置換。site の identity・role・output name
  などは既存 Site.subst の保存対象で、消去しない。
* Packet の全8成分: raw、ordinary、projection、input、binders、head、
  children、outputs を置換。raw は type/row の両構文を扱う既存 ViewSubst。
* exact は任意 Packet / mapping / model であり compiled packet に限らない。
  全子・全 binder・全 output equation の量化は map membership と対応する。

### JournalSubst244

* observed arguments の bounds と optional origin を置換。両側とも同じ
  任意 actual に関する存在・全称観測条件を保持。
* ClassView の全 body equations と全 EqualOutputs atoms を置換。
  ここで Ready は追加しない。元 ClassEffects が翻訳失敗を真とする点も
  変えず、別の readiness obligation のままにする。
* Effect の private raw、projection、historical class、live class を全て置換。
* Journal の current raw、source raw、全 observed list、全 live sites、
  全 packets、全 effects の6成分を置換。
* exact は任意 Journal について成立する形。LegacyEmpty は不要。
* compiled_exact だけが実 Journal232.Models との接続のため LegacyEmpty を
  要する。これは243の exact theorem と同じ制限で、旧記録を捨てていない。
* repeated の順序は `read first (read last model)`。first を最初に構文へ
  代入し、その構文に last を代入した順序に対応し、逆順ではない。
* 任意回数の syntactic substitution を意味的に合成できるが、式のサイズや
  停止性の上界はこの定理から出ない。

## 次の最大義務: 任意 syntax の Same-congruence

243 の literal equality support は、242 の public replacement producer が
要求する Same-congruence とは異なる。Same は各 type が Equivalent、各 row
が文字通り同じという関係である。Equivalent は type の構文等号ではないため
「全 source term の評価が同じ」として既存 support theorem を適用してはならない。

以下の依存グラフなら新しい意味判断なしに既存意味論から構成できる。

1. **基礎評価**
   `AssignmentCongruence238.type_eval`, `row_eval`, `atom_iff`, `all_iff` を再利用。
   `RawCongruence238.equiv_iff`, `subtype_iff` が左右の型値の輸送を与える。

2. **任意 RawView**
   Parameter.Fits の type/row を分岐。FitsAll は同じ actual argument list を
   保持して帰納。Descriptor.Denotes の nominal witness list も同じものを使い、
   target の Equivalent を推移で輸送。ordinary/head/interval/nominal の4条件を
   組み合わせて `Same first last → View.Models first ↔ View.Models last`。
   old rawState を仮定するのではなく、任意 expression View の定理が必要。

3. **任意 Origin の観測輸送**
   source case は type_eval による Equivalent witness。nominal/structural case
   は親の witness を輸送し、元 nominal/shape argument witness を保持する。
   結論は「同じ actual を観測」ではなく
   `Observes first origin value → ∃other, Observes last origin other ∧ Equivalent value other`。
   逆向きも Same.symm で得る。test_iff は既存238の証明を再利用可能。
   Head と Same-origin の存在・全称条件へ展開して接続する。

4. **Projection / Schema / ObservedSite / LiveSite**
   Bounds.Fits は端点の type_eval と観測 actual の Equivalent を使う。
   Projection の anchors/tests/二種類の全capture対を観測輸送で処理。
   Schema Requirement の equal/interval、Use.same/observed を別々に輸送。
   LiveSite は lower/center/upper の全3評価を輸送。output target の構文は
   site.Holds の外だが、全式一覧と支援定理には残す。
   ObservedSite の origin存在・全観測Fitsも同様である。

5. **任意 Effect.Expr**
   Expr/source は type_eval、primitive/nominal/record/variant/join は既存
   型構成子の Equivalent-preservation を相互帰納（Expr と List Expr）で組む。
   nominal引数の各 type を変える際は nominal の意味的合同性を利用し、
   arbitrary argument values の文字通り等号を要求してはならない。
   その後 target の type_eval と合わせ Equation.Holds を輸送。

6. **Packet / Class / Effect / Journal**
   上記の固定構造 producers を全リスト成分へ合成する。Class の双方向tyLeは
   atom_iff。任意 Packet の全8成分、Effect の全4成分、Journal の全6成分へ
   接続し `Congruent J.Models` を生成する。Congruentを仮定として追加するだけの
   ラッパーはこの義務を閉じたことにならない。

7. **242 public replacement へ接続**
   old/new entries coherent、External、TargetsWithin、oldtargetsがhidden内を
   明示し、任意 publicModel を**同じまま**両辺に置く。
   lhs = ∃internal, PublicAgree hidden internal publicModel ∧ oldDefs internal ∧ J.Models internal
   rhs = ∃internal, PublicAgree hidden internal publicModel ∧ newDefs internal ∧
         (JournalSubst244.subst J (Lookup242.substitution oldEntries)).Models internal。
   JournalSubst exact と Lookup242.patch_exact により rhs consumer は
   J.Models (patch oldEntries internal) と一致する。6の構造Congruent producerと
   PublicModel242.replacement_models_iff を適用すれば、結論の存在モデルを
   仮定することなく双方向保存が出る。

## repeated materialized state の最小設計

保存するのは finite Journal と current private definition entries、hidden domain。
source identity、registry、観測slot構造、I45に関係するdescriptor metadata等は
別の operational metadata として保持し、expression Models と混同しない。
1回の rebase は `journal := subst journal oldLookup; entries := newEntries`。
この操作の意味は7の固定public量化子の同値で指定できる。2回目も任意syntaxの
同じ定理を適用できるため historical state 再compile は不要。

ただし schema/packet/viewのmetadataが元kernel操作に使える状態へ輸送されたことは
まだ証明されていない。新 source adapter、frame validity、selection、cacheの
freshness/known、全実stepの activation check、有限進捗 producer は未完成である。
別建てに保持した他ownerの定義 RHS は Journal.Models に自動では含まれず、追加
read set または combined External の義務が必要。singleton→multipleを無条件に
許すため hidden domain を広げる旧shortcutも再導入しない。

## 追記: 他owner定義の書換えが挟まる追加義務

point担当の指摘を確認した。SyntaxGrowth244 の2固定block交互代入は実rebase列
ではない。A→join(B,B)、B→join(A,A) を同時に保持し、実 EscapedStore242 の
操作として A を除去・inlineすると、B の定義自体も書換わり B を自己参照する。
次回も元の未変換B blockを使う toy iterate は実Store操作と異なる。したがって
syntax growth例は有限名から構文有限が出ない診断であり、I47Aの反証でも、実操作
無限列でもない。

全Journal Same-congruence が閉じても、実owner操作にはもう一段必要となる。
他ownerの定義blockを全てinlineし、変換後にも Coherent/External/activation条件が
成立する producer を用意し、その新blockを次回操作へ渡す必要がある。元の条件を
そのまま次回へコピーすることはできない。

## 復旧後8本の独立read-only QA

### finite witness / readback

SupportedAt は特定modelの既存証人を有限readset上で保持する片方向局所主張。
Supports は全model間の双方向同値であり区別されている。witness_write は有限な
特定証人の保護域を返す。bounded_family_write は有限itemsと各要素のsupportを
明示するので、全候補を暗黙有限扱いしていない。これら単独では実Evidenceの
有限支持producerが完成したことにはならない。

### syntax / dependency

SyntaxGrowthは保存構文を2固定代入で膨張させる独立toy syntax。有限2名でも
構文pool有限ではないことを示すだけで、実kernel Stepや言語意味失敗を主張しない。
DependencyRewrite の Acc は定義依存 Edge の方向（source→owner）についての
rank降下によるもの。solver transition の Acc、全探索停止、式サイズ上界ではない。

### 実Presence ASTとrow支持

DefinitionRewriteは実TyTerm/RowTerm/Atomに対する代入。retained targetのtype
mappingがvarそのものという前提から、blockを全atom置換した結果とRHSだけ置換した
target維持blockが構文的に一致する。Allモデル同値も任意Model/assignmentである。

SubstitutionSupport.typeSources はarrowのincoming/outgoingのrowSourcesを含み、
mappingSourcesはtypeSourcesとrowSourcesの両方を含む。row varの代入でもtype側を
余分に含む保守的な上界であり、rowを消す過小supportではない。

### 複数target owner

transformed_externalは、rankが各dependency上で狭義減少し、同ownerの全targetが
同じrankであるという追加条件を使う。そのため別targetへの参照も排除できる。
各entryの自己参照不在だけをExternalと誤認していない。targets_preservedと
transform_coherentはそれぞれ実target一覧と重複targetの同一RHS条件を保持する。
owner_block_shape/exactはremoved/retainedのtarget非交差を明示する。

### readyCheckの正確な限界

readyCheck=true は removedとretainedのrank条件、retained全target同rank、
target非交差を検査する。これは現checked_shape/exact/checked_externalに十分。
ただし Coherent は検査していない。またremoved全target同rankを要求しないため、
removed block内でrankが低い別targetを読むことは許され、removed自身の全block
Externalは導出されない。従って完全なpublic replacementの準備完了チェックではない。
old definition projectionに使うときはremovedのCoherent/External等を別途渡す。
falseは十分条件を認証できない診断で、言語の拒否・選択変更を意味しない。

実到達stateからこのrank／owner分割を生成するproducer、各step後にもそれを維持する
producer、操作metadataとexpression-storeの対応はまだ必要である。

## 追加2本の独立read-only QA

OwnerSequence244のreadManyは先頭removedの読替えを残り列の読替えの外側に置き、
rewriteManyの実代入順と一致する。targets不変から各後続stepへの非交差を導き、
有限列全体のAll意味同値を帰納している。Coherent/同rank/共通rank下Externalの
保存もその量化内で健全。ただしblocksは呼出側が与える列であり、全owner storeから
書換え後のremoved blockを選び続ける実schedulerやその到達性を構成してはいない。

CrossRead244はrank不要の実局所十分条件を与える。retainedの元Externalを別入力とし、
removed RHSの全supportがretained targetsを避けるなら変換後もExternal。rowsを含む
support上界を利用するのでrow参照を落としていない。retainedCheck=trueから形・任意
Modelでの意味・変換後Externalを導く範囲は正しい。

なおこのCrossReadを『最小条件』とは呼ばない。retainedが参照していないremoved entry
のRHSまで全検査するため、必要条件より強い十分条件である。将来細分化するならretained
RHSから実際に到達するlookupだけへ検査を限定できるが、今回の健全性に不要である。
removed自身のExternal/Coherentや実操作時の全条件は依然として別義務。
