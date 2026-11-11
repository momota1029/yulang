# dots cycle 104 — checked source句とordinary制約の一つの入口

## 部分目標と結果

**既存の有限なgrouped associated clausesと名前つきordinary不等式を、一つの検査済み
入口から実mixed閉包へ接続し、元sourceだけで定義した独立モデルとのiffを閉じた。**
callerはProgram、検査成功、slot map、extra名、初期State、fuel、モデルを渡さない。
checkerは空のequationsを持つbare role句も検査し、元の全role義務を保持する。
ordinary整合性とrole解決成功は区別した。部分目標は閉じた。

新規CommonRoleCheckedMixedSourceは215行、11公開定理。
source commit `037353a7657c2a647b84d679084c1ab9154b5bcd`、tree
`3e5029f1b755de9733fdca0f5184584d7c94ba18`。8 source pathを公開し、
git fetchで取得したcommit/treeと全source pathの一致を確認した。

開始時の心拍に書いた目標はsourceからのordinary生成までを広く表現していたが、
実際に閉じた範囲は**既存grouped clausesと既存named inequalitiesの接続**である。
式から不等式を導く橋やparser loweringを証明したとは扱わない。
T1c全体、外側の一般resolve_exact、X13〜X16の外側入口、B4の5橋は未完成。
新しい言語意味論の選択0件、質問ノート0件。

## 定理の量化子・前提・位置づけ

すべてYulang.CommonRoleCheckedMixedSource。srcは任意の有限Sourceであり、
既存Clauseの列と、scalar/すでにscope解決済みNat名の間の普通の不等式列を含む。
env/rolesは任意の既存registry。実行にwf : Roles.WellFormed env.cores、
正確性にawf : Roles.AssocWellFormed env rolesを明示する。
独立Derivesは元の両向きscalar制約、元の相互variable辺、元source句のassociated
Stepだけを使う。独立Modelsは一つのsource型valuationの存在を結論に持つ。

1. checked_derives_exact（健全性/完全性）: 任意src、checkerが実際に返したp、
   任意名a/base bについて、計算されたProgram上のnamed導出と元source導出はiff。
2. checked_evidence_exact（健全性/完全性）: 任意の検査済みp、計算された任意slot/base
   について、実mixed閉包出力のpaired evidenceと元source名の独立Derivesはiff。
3. checked_source_exact（健全性/完全性）: 任意検査済みpと任意allocated valuation v
   について、vが実出力を満たすiff、一つのsource型valuationへ因数分解でき、
   元不等式と全独立導出のscalar等式を満たす。effect行は同一視しない。
4. checked_solver_exact（健全性/完全性）: 任意検査済みpで、実出力のordinary整合性
   true iff 元sourceの独立Modelsが存在する。モデル存在や成功は前提でない。
5. checked_roles_retained（補助）: 任意検査済みpのrole義務列を消去すると元句のrole列
   と等しい。順序・重複を保ち、空equationsのbare roleを落とさない。
6. run_none_iff（補助）: 任意srcで、外側runがnone iff 既存の有限fragment checkerの
   ValidSourceでない。scope/arity/associated nameを検査するが、全言語の拒否規則ではない。
7. run_true_iff（健全性/完全性）: 任意srcで、外側runがsome true iff ValidSourceかつ
   独立Models。検査成功、p、State、extra、slot、modelは外側の前提から消えた。
8. run_false_iff（健全性/完全性）: 任意srcで、外側runがsome false iff ValidSourceかつ
   独立Modelsが存在しない。実ordinary solverの結果を特徴づける。
9. derives_congr（補助、両側）: 任意left/rightのwhole-clauseとordinary不等式のmembership
   がそれぞれ一致すれば、任意a/base bの独立Derivesはiff。
10. models_congr（両側）: 同じmembership前提で、任意left/rightのModelsはiff。
11. run_congr（両側）: 同じmembership前提で、外側Option Bool結果は完全に一致する。
    allocation、slot数、state、role義務の重複数が同じであることは前提にしない。

ordering定理はwhole clauseとordinary不等式の並べ替え・重複を含む。
一つのClause内のequationsを並べ替えた場合はClause値が変わるため、この前提では
扱っていない。全言語の健全性・完全性・主型性、四分類の完成は主張しない。

## 境界とreview

some trueはordinary consistencyであり、全roleのdischargeではない。未seedや
unsupportedなreceiverにroleが残っていてもtrueになり得る。bare roleはcheckerの
Packageに保持されるが、本Boolean結果ではその解決完了を判定しない。
Derivesは直接paired evidenceと元の相互辺の閉包で、一般ordinary entailmentではない。
例えばint <= a、a <= c、c <= intでa/cが全ordinaryモデルでintでも、直接seed pairが
無いのでassociated生成を起動しない。この限界を実行回帰にも含めた。

独立read-only reviewerが定理、依存する実行・宣言的定義、spec6.3、設計、READMEと
最終検証artifactを調べ、blockingな数学的/spec不一致なしと報告した。
checkerがbare roleも検査すること、source DerivesがpやStateを読まないこと、
actual mixed saturationへの接続、全11定理の前提とorderingの範囲を確認した。
reviewerはビルドや公理監査を再実行していない。親workerが実行したログを照合した。
最初の25guardのreview後に6個の境界guardを追加した。production source変更はない。

## 検証

focused buildは362 jobs、31個の実行guard、5個のkernel exampleとno_seed補題が成功。
11定理の公理はpropext / Classical.choice / Quot.soundのみ。全体lake build、全Audit、
全体verify-leanのbuildはstanding ordersに従いローカルで実行していない。
以下のverify-lean PASSはdiff-onlyであり、全体検証PASSと取り違えない。

```text
cd lean; ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake build Yulang.CommonRoleCheckedMixedSource --wfail
✔ [362/362] Built Yulang.CommonRoleCheckedMixedSource (968ms)
Build completed successfully (362 jobs).
exit 0
```

```text
cd lean; ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang104/boundary.lean
exit 0
```

```text
cd lean; ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang104/axioms.lean
'Yulang.CommonRoleCheckedMixedSource.checked_derives_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleCheckedMixedSource.checked_evidence_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCheckedMixedSource.checked_source_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCheckedMixedSource.checked_solver_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCheckedMixedSource.checked_roles_retained' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleCheckedMixedSource.run_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCheckedMixedSource.run_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCheckedMixedSource.run_false_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCheckedMixedSource.derives_congr' depends on axioms: [propext]
'Yulang.CommonRoleCheckedMixedSource.models_congr' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleCheckedMixedSource.run_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

```text
python3 tools/boundary-input-inventory.py --check
PASS: inventory matches source hashes, imports, and ledger mentions.
CommonRole import scope=272; Main=93; Audit=272; ledger mentioned=145. Mention counts are not audit completion counts.
exit 0
```

```text
bash tools/verify-lean.sh . origin/integration/m1-final --no-build
verify-lean: . @ eee600c2d (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
exit 0
```

git diff --checkとstaged diff checkも成功。
production module SHA256:
`9e0b5b3a84ca61737939f509719a1db099272b9eb9e9c9aed9bc5bd488717180`。

実行回帰はordinary専用5からreceiver10、associated output20、ordinary専用25、
次receiver30、output40、ordinary専用50へ情報が流れるchain、順序逆転・重複、
遅延矛盾、空入力、ordinary-only、scope/arity/nameの不正、bare clause保持と検査を含む。
unsupported boolのordinary evidenceは残り、associated outputは生成しない。
semantic-only knownnessの三角形もassociated処理を起動しないことを確認した。

最初のkernel例2つはdecideがopaqueな既存solverでreductionを止めた。期待する実行結果
のguardは保持したまま、正のchainのkernel例は一般のrun_true_iffの適用、unseededの
kernel例はno_seedと具体的モデルの構成にした。chainの受理自体をkernelで構成的に
証明したとは数えない。最初の失敗logは作業中に上書きされたため、履歴はこの記録で
区別する。最終全suiteのexit0だけを成功として扱う。テストの期待値は弱めていない。

## exact-source CI

source commit 037353a7657c2a647b84d679084c1ab9154b5bcdの両CIは、
2026-11-11T00:10:09Zの確認でcompleted/success。
- Lean inference kernel: https://github.com/momota1029/yulang/actions/runs/42928826432
- Core CI: https://github.com/momota1029/yulang/actions/runs/42928826381

source公開後にproduction Lean変更はない。最終notes-only commitのCIと上記exact-source
CIを区別する。最後のreport/heartbeat公開でも同じLean blobを保つ。

## Yulang2・specとの照合

定義前にspec6.3の「関連型変数は普通の型変数」「等式は先に束縛しない」と、
兄弟の更新・安定化の境界を再読した。保持されたaudit x-oracle X13〜X16とC3-PARENTを
照合した。それらはsource例であり、本adapterの完全性oracleではない。
新しいYulang2実行はない。既存one-placeholder構造・int/str encoderと宣言的Stepを
再利用し、新しい言語意味論やunsupported scalarのrole意味は導入していない。

## 復旧・公開・運用

開始2026-11-10T23:57:47Z。integration/workは双方7aeeb586。
remote standing orders/inboxを再読しACTIVE、上限なし、I-11の25分上限、全体検証禁止を
確認した。cycle103のcompleted心拍・reportがあり、保持workspaceを継続した。
開始時に前cycleのLean/Lake/Git processや他writerなし。integrationを保持cloneへmerge。
復旧不要。開始と終了の空きは47G。clone増設・cacheコピー・データ削除なし。

開始heartbeat c1a49bb0。source部分公開037353a7は00:07:21頃、開始から約9.6分。
8source pathを個別blobで送りSHAを照合し、live treeをbaseにSHA-only treeを構成した。
expected-headつきnonforceでwork/dots-mainだけを更新した。integrationへの書込みなし。
git fetchでsource commit/treeを取得し、localとのlean/notes/design差分が空と確認した。

10分heartbeatは00:07:41に準備したが、最初のblob操作の自動承認reviewがdeadlineで
timeoutした。これは拒否ではなく、branch更新もまだ始めていなかった。期待blobの
readが404で不在なのを確認し、toolが許可した1回だけの再試行で同一blobを作成した。
heartbeat de2c0cd8を00:10:48までに公開、取得した本文・SHAの一致も確認した。
この約3分の公開遅れを成功した時刻に書き換えず記録する。source公開は影響なし。
未確定のref更新やblind retryはない。最終公開はreportとcompleted heartbeatのみ。

公開した異なるpathはreportとheartbeatを含め10。使用量の枠は不明。
ログは../cache/yulang104。最終ref/tree/blob取得の照合後に親へ完了報告する。

## B4に残る5橋と次候補

1. source_boundary_adequate: grouped clause/named ordinaryの検査済み接続は閉じた。
   実parser/一般式/宣言からnamed inequalities、scope、invocation、templateを導く橋は未完成。
2. generated_work_closed: 固定有限入力の閉包を使用する。実whereで生成した新childと
   fresh allocationをsource領域へ閉じる橋は未完成。
3. saturate_terminates_and_closes: 既存有限Horn閉包の停止を利用する。一般Form、動的に
   仕事/辺/slotを増やすscheduler、fairness、plateau後の新情報の一般停止は未完成。
4. saturated_frontier_exact: 本Option Bool三結果はfragment検査/ordinary整合性であって、
   language-visibleなpending/selected/ambiguous/rejectedの四分類ではない。その接続は未完成。
5. resolve_dictionary_order_sound: 正準source義務順での辞書構成・観察同値は未完成。

大きな未完パッケージの完成数は変わらない。
次候補: (a) checked scalar expressionからnamed ordinary inequalityへの意味保存、
(b) 本closure出力の実evidenceから保持bare role義務の検査へ接続し結果を区別する橋、
(c) 実generated childのsource領域閉包。未完成の橋をcaller前提に隠さない。

## 再実行可能な境界回帰

```lean
import Yulang.CommonRoleCheckedMixedSource
open Yulang Roles.AssocExamples
open CommonRoleCheckedMixedSource
open CommonRoleNamedOrdinaryInputs (Input)
namespace Cycle104
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
set_option synthInstance.maxSize 4096

def clauses : CommonRoleAssociatedClauseExtraction.Source :=
  [⟨10,index (box (.var 0)) Roles.Examples.int,[⟨0,20⟩]⟩,
   ⟨30,index (box (.var 0)) Roles.Examples.int,[⟨0,40⟩]⟩]
def input : Input :=
  [(.var 5,.base .str),(.base .str,.var 5),
   (.var 5,.var 10),(.var 10,.var 5),
   (.var 20,.var 25),(.var 25,.var 20),
   (.var 25,.var 30),(.var 30,.var 25),
   (.var 40,.var 50),(.var 50,.var 40)]
def src : Source := ⟨clauses,input⟩
def go := run (singletonEnv boxImpl) requiredRoles box_paterson
def observed (src : Source) (a : Nat) : Option Inference.Base := do
  let p ← check requiredRoles src
  let i ← CommonRoleSourceDescent.representative (table src p) a
  CommonRoleOrdinaryKnownness.detect (finish (singletonEnv boxImpl) requiredRoles box_paterson src p).atoms i
#guard (check requiredRoles src).isSome
#guard ((check requiredRoles src).map fun p => p.equations.length) = some 2
#guard ((check requiredRoles src).map fun p => p.obligations.length) = some 2
#guard observed src 5 = some .str
#guard observed src 20 = some .str
#guard observed src 25 = some .str
#guard observed src 40 = some .str
#guard observed src 50 = some .str
#guard observed src 99 = none
#guard go src = some true
#guard go ⟨clauses.reverse,input.reverse⟩ = some true
#guard observed ⟨clauses ++ clauses,input ++ input⟩ 50 = some .str
#guard go ⟨clauses,input ++ [(.var 50,.base .int),(.base .int,.var 50)]⟩ = some false
#guard go ⟨clauses,[]⟩ = some true
#guard observed ⟨clauses,[]⟩ 40 = none
#guard go ⟨[],[(.base .int,.base .str)]⟩ = some false
#guard go ⟨[],[]⟩ = some true
#guard go ⟨[],[(.var 7,.base .bool),(.base .bool,.var 7)]⟩ = some true
#guard go ⟨[⟨10,index (box (.var 1)) Roles.Examples.int,[⟨0,20⟩]⟩],input⟩ = none
#guard go ⟨[⟨10,⟨0,[]⟩,[⟨0,20⟩]⟩],input⟩ = none
#guard go ⟨[⟨10,index (box (.var 0)) Roles.Examples.int,[⟨99,20⟩]⟩],input⟩ = none
-- Bare clauses are checked, although ordinary consistency does not discharge them.
#guard go ⟨[⟨10,index (box (.var 1)) Roles.Examples.int,[]⟩],[]⟩ = none
#guard go ⟨[⟨10,⟨0,[]⟩,[]⟩],[]⟩ = none
#guard go ⟨[⟨10,index (box (.var 0)) Roles.Examples.int,[]⟩],[]⟩ = some true
#guard ((check requiredRoles ⟨[⟨10,index (box (.var 0)) Roles.Examples.int,[]⟩],[]⟩).map
  fun p => (p.obligations.length,p.equations.length)) = some (1,0)
-- Explicit evidence intentionally does not implement semantic-only knownness.
def semanticOnly : Source := ⟨clauses,
  [(.base .int,.var 10),(.var 10,.var 25),(.var 25,.base .int)]⟩
#guard go semanticOnly = some true
#guard observed semanticOnly 10 = none
#guard observed semanticOnly 20 = none
-- Bool is ordinary evidence, but not supported by the existing role encoder.
def unsupported : Source := ⟨clauses,[(.var 10,.base .bool),(.base .bool,.var 10)]⟩
#guard observed unsupported 10 = some .bool
#guard observed unsupported 20 = none
#guard go unsupported = some true
-- The concrete positive-chain expectation above runs executably. Kernel checking
-- uses the proved outer correspondence because the role solver is opaque.
example : go src = some true ↔ Models (singletonEnv boxImpl) requiredRoles src := by
  simpa only [go,show CommonRoleSourceRoleObligations.ValidSource requiredRoles src.clauses by decide,
    true_and] using run_true_iff (singletonEnv boxImpl) requiredRoles box_paterson box_assoc_wellFormed src
example : go ⟨[],[(.base .int,.base .str)]⟩ = some false := by decide
example : go ⟨[⟨10,⟨0,[]⟩,[]⟩],[]⟩ = none := by decide
theorem no_seed (cs : CommonRoleAssociatedClauseExtraction.Source) (a : Nat) (b : Inference.Base)
    (h : Derives (singletonEnv boxImpl) requiredRoles ⟨cs,[]⟩ a b) : False := by
  induction h with
  | initial upper _ => simp at upper
  | transfer _ _ _ ih => exact ih
  | equation _ _ _ _ _ _ ih => exact ih
example : go ⟨clauses,[]⟩ = some true := by
  apply (run_true_iff (singletonEnv boxImpl) requiredRoles box_paterson box_assoc_wellFormed _).mpr
  refine ⟨by decide,⟨fun _ => .base .int,?_,?_⟩⟩
  · intro q h; simp at h
  · intro a b h; exact False.elim (no_seed clauses a b h)
example (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles) (s : Source) :
    run env roles wf s = run env roles wf ⟨s.clauses.reverse ++ s.clauses,
      s.ordinary.reverse ++ s.ordinary⟩ := by
  apply run_congr env roles wf awf
  · intro c; simp
  · intro q; simp
end Cycle104
```

最終report準備: 2026-11-11T00:12:51.824392+00:00、開始から約15.1分。部分目標を閉じ、時間を埋めるための補題は追加しなかった。
