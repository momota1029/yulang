# Yulang Lean cycle44 — source identity と名前付き Index の有限閉包

- 開始: 2026-11-09T16:27:17Z
- 検証終了: 2026-11-09T16:34:39Z
- 基点: integration/m1-final `8ab3e83d6a0c95de906fb1ae1d6d731159e91067`
- 公開先: work/dots-main のみ。予定9ファイル（新規Lean3、design、report、追記import/Audit/README、heartbeat）。公開照合は末尾に追記する。
- cycle43 の completed と対応報告を確認。並行実行なし。開始心拍をGitHubへ公開し読戻した。監査branchの取得も成功し、X13–X17とsource共有・associated typeの仕様を参照した。実機の新規実行はしていない。
- 小単位ローカルcommit: 5b73c193e, a57ea126e, 4fc582ff2, 24e0aa52b。

## 部分目標と達成範囲
任意の有限source identity表と名前付きIndex要求から、共有occurrenceを含む有限str閉包を構成し、独立導出とのiff、出力モデルのiff、および実producerとaliasの意味論的記録を区別した実行証人まで接続する。
この限定した目標は達成。実行証人には最終出力のモデルを明示的に要する。無条件の実行成功を達成したとは扱わない。入力は構文解析済みと仮定した表と要求列ではなく、単なる有限データであり、ソースparserの意味保存は証明していない。

### 定理の共通量化
以下、table は任意の有限自然数列、Slot table はそのoccurrence位置、source は位置の名前、requests は任意の名前対列、s は任意の State table.length、a は全slotへの Common.model のComp割当とする。S = SourceIdentity.extend table s は共有sourceの等式を加えた状態。Derived はstr Evidence、同一sourceへのalias、名前付き要求の3規則から独立に定める。全般的な整合性やWellScopedは暗黙に置かない。

## 主要定理（量化と前提）
`Yulang.CommonRoleDynamicIndexSource`:
- [soundness/completeness] `edges_exact`: 全table,requests,i,jについて、生成辺(i,j)への所属 iff 同じsource名、または名前対がrequestsに属する。
- [soundness/completeness] `derived_exact`: 全table,s,requests,iについて、生成辺上の既存Derivedと今回の独立Derivedは同値。
- [soundness/completeness] `saturate_exact`: 同じ全入力で、計算閉包へのiの所属 iff 独立Derived i。
- [closure] `alias_closed`: 全table,s,requests,i,jで、source名が等しくiが閉包に属すればjも属する。
- [closure] `request_closed`: 同じ全入力で、名前対がrequestsに属しiが閉包に属すればjも属する。
- [semantic exactness] `output_models`: 全table,s,requests,aで、出力の全原子をaが満たす iff sの全原子を満たし、同名occurrenceの値が意味同値で、SからDerivedな全iの値がstrと意味同値。初期モデルを全て保存する主張ではない。
- [soundness] `output_coherent`: 全table,s,requests,aで、出力モデルなら同名occurrenceの値が意味同値。
- [termination auxiliary] `capacity`: 全table,s,requestsで閉包長はtable.length以下。`stopped`: 同じ全入力で、有限候補から新規事実を探すfirstFreshはnone。
- [coverage] `scoped_request_present`: 全table,requestsについてWellScoped（全要求の両端名が表に現れる）を仮定し、任意r∈requestsに対して、その名前を持つslot i,jと生成辺(i,j)が存在する。
- [coverage] `named_request_all_occurrences`: 全table,s,requests,r,i,jについて、r∈requests、source i=rの左名、source j=rの右名、Derived iを仮定するとDerived j。

`Yulang.CommonRoleDynamicIndexSourceExecution`:
- [semantic auxiliary] `alias_models`: 全table,s,xs,i,j,aについて、source i=source jとi∈xsを仮定すると、record S (j::xs)のモデル iff record S xsのモデル。整合性仮定なし。aliasをIndex呼出しと扱わない。
- [conditional actual execution] `trace_executes`: 全table,s,requests,xs,aで、xsがSと生成辺のTraceであり、aが完全出力のモデルなら、xsはExecuted。Executedはseed記録、同一sourceの意味論的同値記録、実produceIndexの成功等式からなる混合実行証人。全要求が実行されるという主張ではない。
- [conditional actual execution] `saturate_executes`: 全table,s,requests,aで、aが完全出力のモデルなら、Sからの計算閉包は上記Executedを持つ。モデルの存在は別途必要。
- [unconditional fixedness] `output_fixed`: 全table,s,requests,iで、完全出力から同じ要求を再飽和した集合への所属 iff Sからの最初の閉包への所属。状態・リスト順序・重複原子の等値ではない。

`Yulang.CommonRoleDynamicIndexSourceExamples`（具体例なので追加前提なし）:
- `well_scoped`: table=[10,10,20,30], requests=[(10,20),(20,30)]はWellScoped。
- `alias_and_downstream_present`: slot0だけstr根拠を持つ初期状態に共有等式を加えた状態から、slot1,2,3は計算閉包に属する。
- `downstream_initially_pending`: 同じ初期状態で実produceIndex 2 3はnone。
- `actual_named_steps`: 同じ状態にalias slot1=strを記録した状態で、実produceIndex 1 2はslot2=strの追記状態を返し、その状態で実produceIndex 2 3はslot3=strの追記状態を返す。外から出力scalarをproducerへ渡さない。

## 検証
コマンド: `cd lean && lake build Yulang.CommonRoleDynamicIndexSourceExamples --wfail`。281 jobs（キャッシュを含む）PASS、exit0。source本体279 jobs、execution280 jobs、examples281 jobsを順にbuildした。最後は差分なしの再確認。
19定理の `lake env lean --trust=0 /tmp/Cycle44Audit.lean` はexit0。依存はpropext/Classical.choice/Quot.soundのみ。監査用一時ファイルは今回3モジュールだけimportし、今回追加した19件をprintした。既存Audit全体や全体build、verify-lean.shは最新指示に従い実行していない。全体PASSとは言わない。

### focused build 出力全文
```text
Build completed successfully (281 jobs).

real	0m0.151s
user	0m0.125s
sys	0m0.059s
EXIT:0
```
### focused audit 出力全文
```text
'Yulang.CommonRoleDynamicIndexSource.edges_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDynamicIndexSource.derived_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDynamicIndexSource.saturate_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexSource.alias_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexSource.request_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexSource.output_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexSource.output_coherent' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexSource.capacity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexSource.stopped' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexSource.scoped_request_present' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDynamicIndexSource.named_request_all_occurrences' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDynamicIndexSourceExecution.alias_models' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDynamicIndexSourceExecution.trace_executes' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexSourceExecution.saturate_executes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexSourceExecution.output_fixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexSourceExamples.well_scoped' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDynamicIndexSourceExamples.alias_and_downstream_present' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexSourceExamples.downstream_initially_pending' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDynamicIndexSourceExamples.actual_named_steps' depends on axioms: [propext, Quot.sound]

real	0m1.084s
user	0m0.804s
sys	0m0.284s
EXIT:0
```

## 未達と次の一手
一般B4の主要5橋は依然未完（source_boundary_adequate / generated_work_closed / saturate_terminates_and_closes / saturated_frontier_exact / resolve_dictionary_order_sound）。今回は主に1・2・3の有限str部分を前進させたので、残りの本数を減らさない。
- 任意のroleや動的child生成、四方向分類、辞書の観察同値には接続していない。
- 表にない名前を含む要求は辺を生成しない。WellScopedのcoverageは別定理であり、入口は未検査の入力を拒否する実装ではない。
- 最終モデルの存在・矛盾の発見・全要求の成功は未証明。具体例も一般実行定理の最終モデルを構成したものではない。
- 次の候補: (1) WellScopedを計算して不在endpointを拒否するsource入口、(2) 実source構文から名前付き要求の抽出と意味保存、(3) str以外の既存checked宣言へ、根拠生成と再訪の有限領域を拡張。
新しい意味論の判断はしていない。質問ノート追加なし。

## 中断・制限
環境中断なし。初回source補題のnamespace/tauto/予約語エラーと、回帰例のFin数値instance・予約語・リスト所属簡約エラーを修正後buildを再実行した。失敗をPASSに数えていない。
開始心拍でupdatedを誤って16:29:10とし、実時計16:30:10の時点で修正した。開始時刻は16:27:17を維持。最後の公開後時刻は下の照合追記とGit履歴が正本。
利用枠への計上は不明。25分のサイクル上限内で公開・報告まで行う。
