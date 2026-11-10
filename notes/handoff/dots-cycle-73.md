# dots cycle 73 — DynamicIndex入力監査とcycle72復旧

## 結果

**16モジュールの入力台帳を追加し、中断したcycle72の検査を復旧した。成果はlocalのみ。**
DynamicIndex系15モジュールと実producerの1モジュールについて、入力名・型・依存定理、
実sourceからの導出案、仕様6.2/6.3/5.5との対応を台帳J節に記録した。
I-13の全量監査は部分達成で、cycle72までの公開期限は満たしていない。
B4の主要5橋、M1の健全性・完全性・主型性は完成していない。

部分目標「中断したDynamicIndex系のsource/診断境界を整理し、全15回帰を検査する」は閉じた。
production Leanの追加・変更、新しい定理、新しい質問ノートはすべて0。
既存Q1/Q2とcycle23/24の質問を再利用し、言語意味論を選び直していない。

- 台帳: `notes/design/2026-11-10-boundary-inputs-ledger.md` J1〜J4。
- inventory: CommonRole系242行、Mainから93、Auditから242。
  台帳で名前が出るものは71から85に増えた。**名前の出現は入力監査完了数ではない。**
- docs成果commit: `14fbcde403b600f041cfb4b94a082cb82dbc31d7`。
- 復旧記録: `notes/heartbeat/dots-main-crash-72.md`。

## 有用な境界の区別

1. `CheckedSource.run = ok`はsource名の両端が存在するというscope成功であり、
   全義務の解決成功ではない。seed無しのrepresented requestでもokを返す。
2. 普通のoutput atomsのモデルと、conditional requestを含む元SourceModelのモデルは
   同じではない。strの強制は一致するが、全model iffにはpendingを含むPacketが必要。
   既存のResidualSource以降は、その全model iffを実際に証明済みである。
3. helper `inspect`は任意Packetを受けるため、falseという印だけでは成功を意味しない。
   実solve結果と元request所属を伴う定理で、初めてreceiverのstr強制と結び付く。
4. pendingはslot対の正準列、diagnoseは元requestの順・重複を保持する列である。
   同じrequestが二つでもpendingは一組でよく、aliasの二slotから同名pendingが二つ
   生じても元requestが二回あったとは限らない。
5. `checked_source_exact`のoutput slotは任意。局所producerの成功は、元の義務の存在や
   辞書の正しさを保証しない。モデル保存の`checked_request_models`にはrequest所属が必要。
6. 実producerは固定boxImplを呼ぶfixtureであり、一般の可視impl集合を解かない。
   spec6.2の`Index str int`がcharを返す例と、boxのpayloadをstrとして伝播する本断片は別。
   これは仕様矛盾の新発見ではなく、実装済み範囲の明確化である。

## 復旧と開始状態

予定起動は2026-11-10T07:27:00Z。最初のdate記録は07:29:05Z。
`git fetch origin integration/m1-final work/dots-main work/dots-audit`を行い、
GitHubアプリでも最新standing ordersとinboxを読み直した。STOPは無く、末尾I-13は不変。
integrationは`434d3ceefce3bc2dbd8d5cb5d84c6295a9c40cf8`で、HEADの祖先だった。
既に取込済みなのでmergeを重ねていない。

APIのcompareでworkはintegrationから1commit遅れ、workの先頭は
`872066861d13cfa1784bffdaa7bfbb973998c00f`。API心拍はcycle68 completed。
git transportのorigin/work/dots-mainは古い`822c4cc50a80eb0f1ec22af12070b4905212fd4d`。
このstale refをAPIの最新公開状態の代わりに使っていない。

local HEAD `23484c0841604fde26adedd25bf5b373dfc90216`とcycle69〜71成果は全保持。
cycle72の心拍だけがrunning（updated=07:00:41Z、elapsed=3.7分）のままで、報告は無かった。
cacheのfocused buildは295 jobs/exit0だが、scratch回帰の1命題でState等号の
Decidable不足によりexit1だった。命題を弱めず、既存
`CommonRoleDynamicIndexEqualitySource.reverse_equality_checked`を使って修正した。
全15回帰と10公理確認の成功を07:30:57Zに確認し、約1.9分で復旧した。

## 検証

環境: `ELAN_HOME=/workspace/scratch/1d0b4aaa3394/elan`、
PATHへ`$ELAN_HOME/bin`を追加。Lean v4.35.0。
長いコマンドには5分のtimeoutを付け、1秒で制御を返す実行にした。
最初のshell background起動は終了マーカーを確認できなかったため、成功とは数えず、
明示的なsession付き実行で完了コードを回収した。

### focused build

```sh
cd lean
timeout 5m lake build Yulang.CommonRoleDynamicIndexOccurrenceDiagnostics Yulang.CommonRoleDynamicIndexExamples Yulang.CommonRoleDynamicIndexSourceExamples --wfail
```

exit 0。出力全文:

```text
Build completed successfully (295 jobs).
```

### 境界回帰15件・公理確認10件

```sh
cd lean
timeout 5m lake env lean ../../cache/yulang73/boundary-check.lean
```

exit 0。新しいproduction定理ではない。
公理は全10件ともpropext / Classical.choice / Quot.soundのみ。
下記の本文を同じimport環境で再実行できる。

```lean
import Yulang.CommonRoleDynamicIndexOccurrenceDiagnostics
import Yulang.CommonRoleDynamicIndexSourceExamples
import Yulang.CommonRoleDynamicIndexExamples
open Yulang
open CommonRoleSourceIdentity (Slot)
open CommonRoleSettledConstraints (State)
namespace Cycle73BoundaryCheck
example : CommonRoleDynamicIndexCheckedSource.missing [10,20]
    [(10,99),(10,20),(10,99)] = [(10,99),(10,99)] := rfl
example : CommonRoleDynamicIndexSource.edges [10,20] [(10,99)] = [(0,0),(1,1)] := rfl
example : (match CommonRoleDynamicIndexCheckedSource.run [10,20] State.empty [(10,20)] with
    | .ok _ => true | .error _ => false) = true := rfl
example : CommonRoleOrdinaryKnownness.produceIndex
    (CommonRoleDynamicIndexSource.output [10,20] State.empty [(10,20)]) 0 1 = none := rfl
example : CommonRoleDynamicIndexResidualSource.residual [10,20] [] []
    [(10,20),(10,20)] = [(0,1)] := rfl
example : CommonRoleDynamicIndexResidualResume.pendingNames [10,10,20] [] [] [(10,20)] =
    [(10,20),(10,20)] := rfl
example : (CommonRoleDynamicIndexResidualBatches.compact [10,20]
    ⟨[],[],[(10,99)]⟩).requests = [] := rfl
example : CommonRoleDynamicIndexResidualBatches.run [10,20]
    ⟨[0],[],[(10,99)]⟩ [⟨[],[(0,1)],[(98,20)]⟩] = .error [(10,99),(98,20)] := rfl
example : CommonRoleDynamicIndexOccurrenceDiagnostics.diagnose [10,20]
    ⟨[],[],[(10,20),(10,20),(10,99)]⟩ [] =
    [[⟨(10,20),[((0,1),true)]⟩,⟨(10,20),[((0,1),true)]⟩,⟨(10,99),[]⟩]] := rfl
example : (CommonRoleDynamicIndexOccurrenceDiagnostics.inspect [10,20]
    ⟨State.empty,[]⟩ (10,20)).endpoints = [((0,1),false)] := rfl
example : CommonRoleOrdinaryKnownness.produceIndex
    (CommonRoleDynamicIndexSource.output [10,20,30]
      (CommonRoleDynamicIndexConsistentSource.input [0] [(1,0)]) [(20,30)]) 1 2 = none := rfl
example : CommonRoleOrdinaryKnownness.checkedProduceIndex
    (CommonRoleDynamicIndexEqualitySource.output [10,20,30] [0] [(1,0)] [(20,30)]) 1 2 =
      some (CommonRoleCandidateStateFrontier.extend
        (CommonRoleDynamicIndexEqualitySource.output [10,20,30] [0] [(1,0)] [(20,30)]) 2 .str) :=
  CommonRoleDynamicIndexEqualitySource.reverse_equality_checked
example : (CommonRoleDynamicIndexResidualSource.build [10,20] [] [] [(10,20),(20,10)]).pending =
    [(0,1),(1,0)] := rfl
example : (CommonRoleDynamicIndexResidualResume.resume [10,20] [] [0] [] [(10,20),(20,10)]).pending = [] := rfl
example : ∃ a : Slot [10,20] → Core.PresenceGeneration.Comp Common.model,
    PresenceNormalForm.All Common.model a
      (CommonRoleDynamicIndexEqualitySource.output [10,20] [] [] [(10,20)]).atoms ∧
      ¬ CommonRoleDynamicIndexResidualSource.Models [10,20]
        (CommonRoleDynamicIndexResidualSource.build [10,20] [] [] [(10,20)]) a :=
  CommonRoleDynamicIndexResidualSource.atom_only_loss_repaired
#print axioms CommonRoleDynamicIndexCheckedSource.run_ok_iff
#print axioms CommonRoleDynamicIndexConsistentSource.saturate_executes
#print axioms CommonRoleDynamicIndexEqualitySource.saturate_executes
#print axioms CommonRoleDynamicIndexSourceSemantics.source_forces_iff
#print axioms CommonRoleDynamicIndexSourceSemantics.output_models_not_source_models
#print axioms CommonRoleDynamicIndexResidualSource.build_models_exact
#print axioms CommonRoleDynamicIndexResidualResume.resume_models_exact
#print axioms CommonRoleDynamicIndexResidualBatches.solve_models_exact
#print axioms CommonRoleDynamicIndexResidualFrontier.solve_residual_exact
#print axioms CommonRoleDynamicIndexOccurrenceDiagnostics.diagnose_represents
end Cycle73BoundaryCheck
```

出力全文:

```text
'Yulang.CommonRoleDynamicIndexCheckedSource.run_ok_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexConsistentSource.saturate_executes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexEqualitySource.saturate_executes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexSourceSemantics.source_forces_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexSourceSemantics.output_models_not_source_models' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualSource.build_models_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualResume.resume_models_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualBatches.solve_models_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualFrontier.solve_residual_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexOccurrenceDiagnostics.diagnose_represents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

既存定理の読み方:
- run_ok_iff: 任意table/state/requests/outについて、ok iff WellScopedと計算されたoutの等号。補助。
- 二つのsaturate_executes: 任意table/str seeds/type links/requestsについて実traceが成立。
  狭い正の有限断片の健全性補助。全言語の停止ではない。
- source_forces_iff: 同じ有限入力と任意slotについて、全独立sourceモデルでstr iff Derived。
  当該断片の健全性・完全性。主型性ではない。
- output_models_not_source_models: 固定二slot入力でoutputを満たすがsourceを満たさない
  assignmentが存在する。境界を示す補助反例。
- build_models_exact: 任意table/seeds/links/requests/assignmentでPacket.Models iff SourceModel。
  当該断片の健全性・完全性。
- resume_models_exact: 任意の同入力と有限extra/assignmentで、再開Packetと全再構築の
  model iff。当該断片の健全性・完全性。
- solve_models_exact: 任意table/p/有限updates/assignmentで、全更新後のPacketモデル iff
  元の全batchのsource conjunction。当該断片の健全性・完全性。
- solve_residual_exact: 任意table/p/有限updates/i/jで、pending所属 iff元request所属かつ
  receiverが全sourceモデルでstrに強制されない。当該断片の診断の健全性・完全性補助。
- diagnose_represents: 任意table/p/有限updatesについて、元batchと元requestの順・重複を
  保った独立診断関係が成立。補助。一般の四分類や辞書同値ではない。

### inventory・リンク・差分

`python tools/boundary-input-inventory.py`で再生成し、`--check`を実行。
exit 0:

```text
PASS: inventory matches source hashes, imports, and ledger mentions.
CommonRole import scope=242; Main=93; Audit=242; ledger mentioned=85. Mention counts are not audit completion counts.
```

TSVの列数・一意性・件数、ledgerの全相対リンク、J節16行と実moduleの存在を検査。
一時検査scriptは初回に余分な閉じ括弧があって構文エラーになった。
そのscriptだけを直した再実行はexit 0:

```text
PASS: 242 unique TSV rows, 7 columns, Main=93/Audit=242, mentions=85; all ledger relative links resolve; 16 J-section module rows cover all 15 DynamicIndex modules plus OrdinaryKnownness.
```

`git diff --check`成功。`git diff --quiet 23484c084 -- lean`成功でproduction Lean無変更。
`bash tools/verify-lean.sh . origin/integration/m1-final --no-build`はexit
0。出力全文:

```text
verify-lean: . @ 14fbcde40 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

これはdiff-only検査であり、全体検証のPASSではない。
**全体lake build、全Audit/AxiomGate、verify-lean.shのbuild付き実行はしていない。**
公開後の全体検証は監督役の仕事で、remote CIも今回の未公開成果に対しては確認不能。

## 公開ブロッカーと未公開一覧

cycle69以降のGit object作成は審査拒否で、新しい許可はない。
今回のremote書込は0回。blob/tree/commit/ref作成更新、push、同等の別経路を試していない。
開始/終了の心拍と復旧記録もlocalだけで、外から見えるremote心拍の代わりにはならない。

公開するファイルは最新integrationとの差分で17path（本報告を含む）:
- `lean/Audit.lean`
- `lean/README.md`
- `lean/Yulang.lean`
- `lean/Yulang/CommonRoleAddressedCaptureModels.lean`
- `notes/design/2026-11-10-boundary-input-coverage.tsv`
- `notes/design/2026-11-10-boundary-inputs-ledger.md`
- `notes/design/2026-11-10-cycle69-addressed-capture-models.md`
- `notes/design/INDEX.md`
- `notes/handoff/dots-cycle-69.md`
- `notes/handoff/dots-cycle-70.md`
- `notes/handoff/dots-cycle-71.md`
- `notes/handoff/dots-cycle-73.md`
- `notes/heartbeat/dots-main-crash-72.md`
- `notes/heartbeat/dots-main.md`
- `notes/questions/2026-11-10-cycle70-associated-sugar-checking.md`
- `notes/questions/2026-11-10-cycle70-invocation-sharing-boundary.md`
- `tools/boundary-input-inventory.py`

新しい承認後は最新integration/API live workを再取得し、対象外pathを保った
non-force・expected-headの一括公開と全blob/tree照合を行う必要がある。
承認が来るまで拒否された操作を再試行しない。

## Yulang2との照合・次の候補

既存監査`y2-claims-role-boundaries-cycle-2.md` ROLE-MORE-001〜005、
`x-oracle.md` X13〜X16/C3-PARENTを再読。新しいYulang2実行、parser確認はしていない。
旧whereの差を新specへ採用せず、小さいfixtureの成功を一般source橋としない。

B4の残る主要橋は5本:
`source_boundary_adequate`、`generated_work_closed`、`saturate_terminates_and_closes`、
`saturated_frontier_exact`、`resolve_dictionary_order_sound`。

次の監査候補:
1. interval candidate/frontierのcaller入力と宣言capture前提。
2. 一般ordinary stateからgraph adapterへのreadoutとadequacy前提。
3. Mainのassociated/where exactness前提とI-13台帳の対応。

## 時間・資源

報告保存: 2026-11-10T07:37:32Z。
予定起動から10.5分、最初のdateから8.5分。
25分以内。時間を埋める補題や全体ビルドは追加していない。
開始・終了とも空き48G/全63G、使用13G。作業場とLean cacheは一つを再利用。
使用量枠は不明。
