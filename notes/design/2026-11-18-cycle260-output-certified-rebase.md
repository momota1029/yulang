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
