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
