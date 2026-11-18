# cycle260：実outputの意味証明書を持つ部分rebase

Status: Draft implementation design. I51/I52継続。既存Lean/specは変更しない。

## 狙いとデータ

259の252実source probeで、report受理とbasis閉包だけではOutputsが足りないと確認した。
今回は同じPlanの `emittedSchema` を入口で読む。reportだけから出力を推測しない。
一般source compilerはまだ宣言せず、実252のsource/packet/installを接続する。

表現の選択肢は専用output Fact型を新設するか、既存有限driverのbinder indexを
有限の束縛方程式表のアドレスとして使うか。後者をこの断片に採る。capture用0/1に
重ならないoffset2以降を、実emittedSchema.equationsのindexに固定する。
これはsource名の再予約でなく有限table indexであり、outputを別名に書き換えない。
表の意味は各実Equation.Holdsをversioned variablesで読む。unknown schemaやreport
未対応は言語拒否/noopと混同せず、別の内部decode errorを返す入口を設計する。

## 外側の定理

- 任意schema・offset・assignmentについて、有限output keys全成立 iff schema.Holds。
  keysのindex範囲とcapture key0/1との非衝突を明示する。
- 実252 Planに対しdecoderは実reportの5factsと実output equation1件を返す。
  完成stateのModels iff source Models ∧ 実Outputs iff 当該packet Holds。
  source Modelsだけから元assignmentのOutputsが出るとはしない。
- 任意初期sourceモデルaからslot3の型だけをcompleteしたassignmentで、同じpacketの
  Holds、旧installation Models、新有限終点Modelsを同時に構成する。
  まず同一assignmentでの制約対応を示し、slot3型だけを解放した存在公開射影を分ける。
- 実decoderのnewStep/checkedrun/settleは初回install・以後noop、Acc。旧sourceの
  microstep一般simulationや全言語停止性とは区別する。

## 停止性と残る危険

既存remaining.lengthの減少を使用する。output table長はこの固定sourceから直接計算。
一般sourceのowner/output依存循環・pool閉包・child/presence全coverageは未解決。
新しいK2拒否規則を加えない。252の実初期/installedの同一assignmentモデル対応が
難しければ必要な仮定を記録し、構築した証明書による対応と区別する。

## 最初の接続結果

実252の終点Models iff 実packet Holdsを同一assignmentで示した。さらに同じassignment
で旧checked installation後のjournal Modelsと同値、終点からleaf Evidenceも構成できる。
公開射影は別定理としてslot3型だけを解放する。固定outputを要求する場合は
`replace output`の終点Models iff `Equivalent output P`であり、bottomを通していない。

現在のoffset2 output keysは一つのPlanの表に限る。owner引数が違っても同じoffset2を
使う一般decode関数を、複数ownerの共有表へそのまま合成してはいけない。次に必要な
独立課題は、owner別の方程式アドレスを注入的にし、固定capture0/1と他ownerのkeysに
衝突しないことを証明すること。単一252接続を全source対応と呼ばない。

## owner別outputアドレスの設計

複数ownerの式表を共有するときの別案として、output keyを
`binder(2 + pair(owner,index))` とする。既存GeneralNominalIdentities.pairの注入性を使い、
ownerまたはindexの異なる出力義務が衝突しないことを証明する。
これは固定有限owner集合×各schemaの有限indexから列挙する式表で、無限に新しい
source名を作るものではない。keyの数値の大きさを実行回数や時間の上界とはしない。
まず式表の一般意味と単一252(owner0,index0)が元binder2と一致することを検証する。
capture binder0/1は依然単一Planの意味であり、全consumerを含む複数ownercompilerは
このoutput表だけから完成したとは言わない。

## 次の実source：206のrole default

252の明示associated式を閉じたので、独立した206回帰へ進む。既存
`GeneralDictionaryVersionedGap206233` と `...Install233` を読んだ。
このsourceのemittedSchemaは空だが、role default `(role0,name0,var0)` のClassEffectsは
output0と入力center1の型同値を要求する。packet Holdsだけで済ませると既存bottom反例を
再現する。実lookup/bodySchema/bodyVariablesを読む別の有限obligationとして表現し、
同一assignmentでnew終点Models iff旧installed Modelsを狙う。

このsourceのreportはcapture空なので、252用capture decoderの「空は未対応」を勝手に
消さない。206専用入口で実reportのblocked/conflict/arityなし・capture不要を証明し、
既存の全初期モデル→packet Holdsと実default lookupから省略がないことを示す。
新しい型推論規則やdefaultの意味は選ばない。公開投影を証明するなら、初期sourceが
読まないoutput0型だけを補完し、ほかの全成分・全rowを保存することが必要。

## 206 default接続の結果と202の対照回帰

206の実lookup・bodySchemaからowner37の既定式を取り込み、終点Models iff旧installed
Modelsを同一assignmentで示した。packet HoldsだけではなくClassEffectsを終点に要求し、
既存bottom counterを除く。output0型だけを入力center1の型へ補完し、他の全成分と全rowを
保つ公開射影も構成した。初期モデルをすべてそのまま終点モデルにする主張ではない。

次は202の「初期sourceが既にdefaultを満たす」対照を同じ入口で確かめる。
有限factsの初回書込みがあっても、初期Modelsと終点Modelsの集合が等しい場合がある。
従ってfact増加の停止測度と、モデル集合の真の細分化は区別する必要がある。
旧202は既にCommitted/Stableなので、もし新関係が一歩進めばそれは意味的stutterとして
対応させるべきで、旧install一歩と一致したとは報告しない。

202を実ソースで再確認すると、要求outputはslot1で入力centerもslot1なので、defaultは
すべてのassignmentで反射的に成立する。206は要求output0と入力center1が別である。
両者のtable keyが同じでも、異なるsourceごとに固定したlayoutの意味は異なる。
これを同じ共有layoutへ混ぜず、それぞれ実request.targetを保持してcompileする。

## 同一ownerの複数要求をまだ混ぜない

読取レビューと追加検査で、単一body decoderのkeyはowner/indexだけなので、同じownerに異なるrequestを渡すとindex0が衝突することを確認した。206の実planでoutput0（実要求）とoutput1（非要求の内部引数）を渡すとproposalは同じだが、既存counter上で前者のBodyHoldsは偽、後者は反射的に真になる。RequestAddressProbeで確認する。output1は実requestsに属さないことも証明し、到達sourceの拒否・I50反例・既存fixtureの失敗とは区別する。

次の表現案は(owner, obligation kind, request index, equation index)を有限table住所に符号化するか、各ownerの全request schemaを一つに連結しoffsetを保持すること。前者を設計候補の先頭に置く。いずれも固定有限request列の取得と実requests coverage、EqualOutputsの別義務が必要で、このcycleの単一要求decoderを一般compilerとして繋ぐことはしない。言語の受理規則は変えない。

## 内部address衝突に対する局所修復を選ぶ

I-52の表現選択として、単一bodyのtable住所に `(owner, kind, request index)` を含める。
既存の注入pairを二重に使った値をoutput-keyのowner欄に置き、最後のequation indexは
そのまま残す。kindはemitted/capture/body等を共有表へ統合するときに衝突しないための
明示的な数であり、この段階で完全なkind列挙やcallerの割当規則を仮定なしに保証しない。

証明する型：任意owner/kind/request/equationについてkey等号は4成分の等号を導く。
任意Plan・指定output・実lookup bodyについて、当該namespaceの全key意味 iff実BodyHolds。
実206の2つの内部要求targetをrequest0/1へ分けたproposalは異なる。
これは有限表住所の修復であり、実requestsの全列挙・正しいrequest index割当・EqualOutputs・
全Stepのsource compiler接続は引き続き未証明。既存252/206/202の検証済みrunnerは変更しない。

## 一般compilerへ進む前の接続点再点検

`GeneralNominalCenteredHeadOutputs.requests` は固定宣言のoutputNamesそのものではなく、
現stateのalias classに属するsiteの要求を集めた列である。したがって新しいrequest indexは
「今この瞬間の列の何番目か」を毎回取り直してはいけない。alias拡大・重複・順序変化で
同じ住所のpayloadが変わる。修復moduleのrequestは、固定した有限候補表の中で安定な
indexとしてcallerが供給する必要がある。候補は `(output.name, output.target)` の固定表
からのindex、または元source/宣言の安定識別子を含むkey。まだそのproducerは証明していない。

既存 `GeneralNominalSourceOwnerCandidates252.mixed_finite_owners` は source初期条件と
旧mixed到達path、Generated、Installable、not Committed の下でowner候補所属を示す。
全state/全request/全内部slotが同じ有限候補に入るという定理ではない。
`GeneralNominalPublicPorts253.mixed_finite_ports` も実installのpurpose2〜5のportsについて
同じ条件付きであり、全alias-class requestsの固定表閉包を直接与えない。
これらを新finiteStateのobserverへそのまま当てて一般Closedを得たとは言わない。

次の狭い実装目標：固定sourceで二つの実requestが同じalias classに入る回帰を選び、
要求の和集合保持とEqualOutputsを含む全body obligationsをrequest別keyに配置する。
そのfixtureで、初期/終点Modelsと旧installedの同一assignment対応を先に閉じる。
続いて実requestsを固定candidate表へ写すmembership/意味不変補題、最後にsourceからの
candidate表生成を証明する。I50の出力依存cycle拒否・ground readback上界はこの有限
table住所修復だけでは解決しない。

固定index producerを待たず、名前付きrequest `(name,target)` 自体を注入pairで符号化する
薄い入口も置く。これなら同じrequestがalias列の別位置に移っても住所は変わらず、異なる
nameまたはtargetは分離する。有限性はなおsource由来の有限request候補表が必要であり、
Nat全体を有限と扱わない。lookup bodyの一意性は同じPlan/declarationを固定した場合だけ。

次回fixtureの読取候補は `GeneralNominalCenteredHeadAllocV7MergeRegression`。
そこでは同じalias classに `⟨0,aTarget⟩` と `⟨0,bTarget⟩` の二つの実requestがあり、
履歴モデルはある一方、EqualOutputsと異なる出力の両立が失敗する具体例がすでにある。
ただしこれは古いV7境界の分類であり、現在のversioned境界へ無条件に転用しない。
`GeneralNominalVersionedMixedInstallRequests235.requests_iff` のAbsorbed条件は、
子の新output要求が既に表現済みである場合に限る。出力無し子なら導出できるが、
任意子を持つPlanの要求集合不変を仮定して一般化してはいけない。
