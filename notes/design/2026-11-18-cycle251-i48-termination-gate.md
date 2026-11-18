# Cycle251: I-48 停止性ゲート（見通し未確立、部品追加を停止）

2026-11-18 01:12 UTC、integration `00793b4ac` を再取得して I-48 を初めて確認。
開始00:31のintegration `9ec236c79`には未掲載だった。それまでの27moduleは
公開済み、直前に検証したSourcePlanProducerの接続1定理は保全する。
以後のLean部品追加を停止し、この設計・最終監査のみを行う。

## 測度候補と、上界をまだ与えられない理由

候補は辞書式 `(未生成owner予算, 各ownerの未達成細分化rankの総和)`。
ただし現在の証明には、いずれの自然数上界も存在しない。先に有限入力列を
受け取るPlanTraceはこの予算を構成せず、sourceの次の一歩を列挙しない。

- **distinct owner**: keyは(root demand identity, declaration id)。宣言集合が有限でも
  root identityの集合がsource実行中に有限である証明が要る。子需要の再生成を
  「同じownerなので有限」と言うのは循環する。ground sourceの有限部分式と
  許可される置換から有限root候補集合を先に構成する必要がある。
- **予約slot**: 既登録handle一つについては2×inputNames.lengthで、更新でtarget
  listは変わらない（250/251）。しかしowner総数未確立なので全体のslot上界には
  ならない。現frameと指定protectedNamesのfreshnessは将来のallocationとの分離
  ではない。名前を二つのnamespaceに分ける案は、実source識別子への写像と
  sharing保存を証明して初めて使える。今周期では採用していない。
- **termの大きさ**: SnapshotGrowth251はtargetが常に[2]、typedReadsが常に{0}、
  SafeOrderを維持しても、raw2=union(var2,var2)のsnapshot更新でtree(n+1)へ
  成長し、height(tree n)=nになることを証明した。値は常にvar0と同値。
  従って固定slot数・型意味の不変・SafeOrderだけから構文有限性は出ない。
  これは任意raw入力の表現側反例で、source到達性やI45違反の反例ではない。
  DuplicateUnion251はroot一段の局所簡約にすぎず、一般の冪等正規化ですらない
  （tree2→tree1→tree0）。これを有限性の修復と数えてはいけない。
- **public escape**: 既存metadataはsnapshotで旧読取りへ移す。しかし将来sourceの
  binder/output/child targetがprivate予約名をpublicに露出しないこと、public
  demand identityやowner keyへprivate termの構文版が戻らないことは未証明。
  初期protectedNamesだけを有限public universeと見なしてはいけない。

有限表現の候補は、固定有限public basis上の共有DAGまたは同値な記述の有限
正規形。ただしDAG共有だけでもdepthの成長は止めない。有限basis上のunion/
intersectionであっても、nominal application/row/arrow等のconstructor深さが
source規則で増えない理由が必要。意味同値による商だけを挿入するのは、決定性・
有限性・I45で固定すべきsource名の保存を後回しにするため、現時点で採用しない。

## 239・240型の再現を試みた結果

239のpoint descriptorを別名に付け替える一歩はI45をそのまま残して禁止する。
RoleBinder251のsingleton_pointは旧endpoint mappingを読むが、それだけでは
source Step自体の不動性の証明ではない。239旧反例から新Stepへの射は未定義。

240のnonpoint根が同値な新source名を次々参照する一歩は、既登録handleのlo/hi
を再使用する限り、aggregate allocationの増加を止められる。登録済みの実Plan
二個を同じhandleで処理する構造回帰は通った。しかし「同じroot identityのまま」
「別のchild/public名が新root keyにならない」「旧class/effectが最後のinstallに
対応する」が未確立。従って240型が新source Step全体で再現しないとはまだ言えない。

さらに上記snapshot raw反復は同値な構文版がslotの中で増える経路を示す。
実source packetからこのrawが何度も生成される閉じたYulang例は得ていない。
到達する新source反例を得たと偽って停止理由にせず、測度未確立として停止する。

## EvidenceNodeまでの依存と危険度

1. **最優先／最大リスク: source Stepと有限性不変条件**。有限root/public basis、
   owner上界、private escape分離、constructor深さ／正規形上界、I45 point固定、
   genuine refinementでrankが減ること。これが閉じてからAccを証明する。
2. **mixed-time packet**: 251で全8field、actual input/child/output、mode/default、
   singleton binder、old origin/fresh aggregate、実Plan key整合を局所的に証明。
   残りはsource transitionからPlan・Live/class requestを生成する正当性と
   effect.plan.bindings↔handleの最後のinstallの不変条件。Acc前の追加は停止。
3. **Permittedの導出**: 独立RolePacket.Holdsと有限traceのPermittedの同値はある。
   source eligibility/unique candidateからHoldsを得る証明はない。translation
   readyと意味受理は別。unknownなら空の式が自明に成り立つ回帰も明示した。
4. **後継boundaryの12性質・199/202/204/206/218/230/239/240**: 同じsource意味を
   保つ健全性・完全性を上記生成器で閉じ、Accを含む境界定理へ束ねる。今回の
   fixtureは構造検査で、230が新境界で受理される意味回帰の代用ではない。
5. **EvidenceNode**: 1〜4の後。finite command listを渡す外部オラクルやPermittedを
   仮定したままB4 Statement完成としない。

## 結論と再開条件

測度は決まっておらず、239/240型をsource全体で排除する説明も完成していない。
I-48に従って、今周期の検証済み成果を保全した後は部品追加を止める。
次は停止性設計だけを進め、上記有限basis/深さ/escapeの根拠を作るか、閉じた
source反例を提出する。現時点で新しい言語意味の選択を求めるYulang反例はない。
