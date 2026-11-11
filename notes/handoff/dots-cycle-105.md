# dots cycle 105 — 実mixed evidenceから保持されたrole義務を解く

## 部分目標と結果

**実mixed閉包の出力から各source receiverのscalar evidenceを集め、保持された全role義務へ接続する有限の橋を閉じた。**
外側の入口にcallerがhead map、Program、checker成功、slot map、State、fuel、導出やrole成功を渡す必要はない。
ordinary整合性とrole dischargeは別々のBoolean観測として返す。bare roleも落とさない。
新規CommonRoleEvidenceDischargeは181行、公開定理10本。部分目標は閉じた。

source commit `db347815c19ccdb2fe7b4aeba2caf3fd2621cf64`、tree
`f4491ae1caaad54dcb75050d894b2bffa29d7b7d`。8 source pathを公開し、
公開treeから各blobのSHAを取得して全一致を確認した。保持cloneへfetchし、
公開commit/treeと全lean/notes/design差分が空であることも確認した。

T1c全体、一般resolve_exact、X13〜X16の外側入口、B4の5橋は未完成。
新しい言語意味論の選択0件、質問ノート0件。false dischargeを新しい言語の拒否規則にしない。

## 定理の量化子・前提・位置づけ

全てYulang.CommonRoleEvidenceDischarge。srcは任意の有限Sourceで、既存のgrouped clausesと
scope解決済みNat名を使うordinary不等式列を含む。env/rolesは任意の既存registry。
実行にwf : Roles.WellFormed env.cores、正確性にawf : Roles.AssocWellFormed env rolesを明示する。
独立Dischargedは、元sourceのDerivesによるreceiverのscalar bと、既存Discharges env.cores
(fun _ => b) cの存在である。後者は構造的Fillsと宣言的Resolvesを使い、allocated stateや実行結果を読まない。
AllDischargedは元の全句に対する連言。Modelsは一つのsource型valuationを要求する。

1. derived_support（補助）: 任意src、検査済みp、任意名a/base bで、元sourceからa:bを
   導けるなら、計算されたtableにname=aのslotが存在する。bare roleに追加slotを仮定しない。
2. heads_exact（健全性/完全性）: 任意検査済みp、任意a/bで、実mixed閉包から集めたheadsに
   bが入るiff元sourceのDerives a b。直接paired evidenceの範囲で完全。
3. run_one_exact（健全性/完全性）: 任意検査済みp、保持義務oと元句cのerasureが一致するとき、
   oの実行がtrue iff元句cの独立Discharged。候補headをcallerから受け取らない。
4. run_roles_exact（健全性/完全性）: 任意検査済みpで、実role全検査がtrue iff元sourceの
   AllDischarged。空equationsの句を含み、義務を消去して成功にしない。
5. run_none_iff（補助）: 任意srcで、外側結果none iff既存有限fragmentのValidSourceでない。
6. ordinary_projection（補助）: 任意srcで、結果pairの第1成分はcycle104のordinary入口と等しい。
7. run_success_iff（健全性/完全性）: 任意srcで、some(true,true) iff ValidSourceかつModelsかつ
   AllDischarged。checker成功、head map、state、モデル存在、role成功は外側前提ではない。
8. discharged_congr（補助、両側）: 任意left/rightのwhole-clauseとordinary不等式のmembershipが
   それぞれ一致すれば、任意句cに対するDischargedがiff。
9. all_discharged_congr（両側）: 同じmembership前提でAllDischargedがiff。
10. run_congr（両側）: 同じmembership前提でOption(Boolean pair)全体が等しい。
    成功時だけの一致ではなく、noneと成功しない全pairも含む。

全言語の健全性・完全性・主型性、B4完成を主張しない。新たな主型性定理はない。
orderingはwhole clauseとordinary不等式の並べ替え・重複を含むが、一つのClause内のequationsを
入れ替えた場合はClause値が変わるのでこの前提では扱わない。

## 境界・review

some(true,false)はordinary整合性があってもrole証拠が不足/未対応/不成立の観測。
some(false,true)もあり、role側だけのtrueを受理としない。矛盾したstateでは複数scalar evidenceを
持ち得るため、最初の一つを選ぶのでなく全候補を調べる。成功には共通source valuationも必要である。

このadapterではground goalでもreceiverの独立scalar evidenceを要求する。bool/unit evidenceは
ordinaryに残るが既存int/str encoderではroleを解けない。これは有限断片の明示した制限であり、
新しいsource-level拒否判断ではない。直接pairと相互辺の閉包を使い、一般ordinary entailmentは解かない。

独立read-only reviewerが新module、依存する実行/宣言定義、spec6.3、設計と境界artifactを読み、
blockingな数学的/spec不一致なしと報告した。whole-clauseの範囲とground receiverの制限を文書に明記した。
追加提案のsome(false,false)guardを足し、境界suite全体を再実行してexit0を確認した。
reviewer自身はビルド/公理監査を再実行していない。親workerが実行ログを照合した。

## 検証

focused 363 jobs、21実行guard、5 kernel example、10公理監査が成功。公理は
propext / Classical.choice / Quot.soundのみ。全体lake build、全Audit、全体verify-leanの
buildはstanding ordersに従いローカルでは実行しなかった。以下のPASSはdiff-onlyである。

```text
cd lean; ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake build Yulang.CommonRoleEvidenceDischarge --wfail
✔ [363/363] Built Yulang.CommonRoleEvidenceDischarge (1.0s)
Build completed successfully (363 jobs).
exit 0
```

```text
cd lean; ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang105/boundary.lean
exit 0
```

```text
cd lean; ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang105/axioms.lean
'Yulang.CommonRoleEvidenceDischarge.derived_support' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleEvidenceDischarge.heads_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleEvidenceDischarge.run_one_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleEvidenceDischarge.run_roles_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleEvidenceDischarge.run_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleEvidenceDischarge.ordinary_projection' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleEvidenceDischarge.run_success_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleEvidenceDischarge.discharged_congr' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleEvidenceDischarge.all_discharged_congr' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleEvidenceDischarge.run_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

```text
python3 tools/boundary-input-inventory.py --check
PASS: inventory matches source hashes, imports, and ledger mentions.
CommonRole import scope=273; Main=93; Audit=273; ledger mentioned=146. Mention counts are not audit completion counts.
exit 0
```

```text
bash tools/verify-lean.sh . origin/integration/m1-final --no-build
verify-lean: . @ f4e421b7f (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
exit 0
```

git diff --checkとstaged diff checkも成功。production module SHA256:
`c5e0c0e78f61430ba0d3db37d0e7c6f0bcf9b366667c05bb1ba5e2316d8ef476`。
最初のfocused buildはdeprecated if_posの警告を--wfailが失敗として扱った。
ite_eq_leftへ置換して成功した。最初のdiff gateは未commit/untracked sourceだけで失敗した。
明示8pathをcommit後に再実行してPASS。初回ログ/exitはcache/yulang105のinitialファイルに保持した。

5 kernel exampleのうち、空入力・ordinary矛盾・不正句は具体結果をkernelで確認した。
残り2つは一般の順序不変性と正のchainの外側iffを適用したもの。opaqueな既存solverを含む
chain成功そのものは実行guardで確認し、具体的kernel構成の証明とは数えない。

## exact-source CI

source commit db347815c19ccdb2fe7b4aeba2caf3fd2621cf64の両CIを00:36台に確認し、completed/success。
- Core CI: https://github.com/momota1029/yulang/actions/runs/42932468973
- Lean inference kernel: https://github.com/momota1029/yulang/actions/runs/42932468975

これはこの正確なsource commitに対するremote CI結果。ローカルで全体検証したという意味ではない。

source公開後にproduction Lean変更はない。最終report/heartbeatのみのcommitと上記source commitを区別する。

## Yulang2・specとの照合

定義前にspec6.3の関連型等式、未知receiverを一意implだけで決めない規則、兄弟更新の安定化、whereの
連言性を再読した。最新work/dots-auditをfetchし、x-oracle X13〜X16とC3-PARENT/C3-PARENT-NEGを照合。
これらはsource-level互換性の背景であり本adapterの完全性oracleではない。新しいYulang2実行はない。
既存structural template/Fills/Resolvesとint/str encoderのみ使用し、新しい意味論は導入しなかった。

## 復旧・公開・運用

開始2026-11-11T00:26:39Z。integration/workとも91043342であることをlive取得し、
standing orders/inbox ACTIVE、上限なし、I-11の25分上限、full build禁止を確認した。
cycle104 completed heartbeatとreportがあり、前cycleのLean/Lake/Git processや別writerなし。
保持cloneへintegrationをmergeして継続、復旧不要。開始空き47G、clone/cache増設や削除なし。

開始heartbeat b4087cb9。source部分公開db347815は00:34:48頃、開始から約8.2分。
全8fileを個別blobで作成して各SHAを照合し、live treeをbaseにSHA-only treeを組み、
expected-headつきnonforceでwork/dots-mainだけを更新した。integration書込みなし。
最初のlocal source JSON読出しは全8file合計が出力上限を超えてparse失敗したが、
公開write前でありremote影響なし。その後はfileごとに読出し・blob化した。未確定writeやblind retryなし。

10分heartbeat 0e6f147eを00:37:02までに公開。検証済みsource treeを保持し、report準備状況を記録した。
終了準備時刻2026-11-11T00:37:25.618735+00:00、開始から約10.8分。終了空き47G。Lean/Lake/Gitの作業processなし。
最終publishはreportとcompleted heartbeatのみ。部分目標が閉じたためI-11に従い余分な補題を足さず終了する。

公開した異なるpathはsource8とreport/heartbeatの計10。使用量の枠は不明。
ログは../cache/yulang105。最終ref/tree/blobを取得して照合後、親へ完了を報告する。

## B4に残る5橋・次候補

1. source_boundary_adequate: checked grouped/named sourceから実closureとrole dischargeへの有限接続は閉じた。
   実parser/式/宣言から普通不等式、scope、invocation、templateを導く橋は未完成。
2. generated_work_closed: 固定有限sourceを使用する。実whereの生成child/fresh allocationを領域へ閉じる橋は未完成。
3. saturate_terminates_and_closes: 既存有限Horn閉包の停止を利用。一般Form・動的仕事/辺/slotとfairnessの停止は未完成。
4. saturated_frontier_exact: 二つのBoolean観測はlanguage-visibleな四分類ではない。独立な診断treeへの接続は未完成。
5. resolve_dictionary_order_sound: source義務の正準順での辞書構成と観察同値は未完成。

未完の大きなパッケージの完成数は変わらない。次候補は(a) 閉じたrole呼出しの詳細な既存診断を保持する
source結果tree、(b) source式からnamed ordinary不等式への意味保存、(c) 実generated childの領域閉包。
未完成の橋をcaller前提に隠さない。時間を埋めるための補題は追加しなかった。

## 再実行可能な境界回帰

```lean
import Yulang.CommonRoleEvidenceDischarge
open Yulang Roles.AssocExamples
open CommonRoleCheckedMixedSource (Source)
open CommonRoleEvidenceDischarge
namespace Cycle105
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
set_option synthInstance.maxSize 4096

def clauses : CommonRoleAssociatedClauseExtraction.Source :=
  [⟨10,index (box (.var 0)) Roles.Examples.int,[⟨0,20⟩]⟩,
   ⟨20,index (box (.var 0)) Roles.Examples.int,[]⟩]
def seed : CommonRoleNamedOrdinaryInputs.Input :=
  [(.var 5,.base .str),(.base .str,.var 5),(.var 5,.var 10),(.var 10,.var 5)]
def src : Source := ⟨clauses,seed⟩
def go := run (singletonEnv boxImpl) requiredRoles box_paterson
#guard go src = some (true,true)
#guard go ⟨clauses.reverse,seed.reverse⟩ = some (true,true)
#guard go ⟨clauses ++ clauses,seed ++ seed⟩ = some (true,true)
#guard go ⟨clauses,[]⟩ = some (true,false)
#guard go ⟨clauses,[(.base .str,.base .int)]⟩ = some (false,false)
-- This bare receiver is not present in ordinary or associated allocation.
#guard go ⟨clauses ++ [⟨77,index (box (.var 0)) Roles.Examples.int,[]⟩],seed⟩ = some (true,false)
#guard go ⟨clauses,seed ++ [(.var 20,.base .int),(.base .int,.var 20)]⟩ = some (false,true)
#guard go ⟨[],[]⟩ = some (true,true)
#guard go ⟨[],[(.base .str,.base .int)]⟩ = some (false,true)
#guard go ⟨[⟨10,index (.var 0) Roles.Examples.int,[]⟩],seed⟩ = some (true,false)
#guard go ⟨[⟨10,index (box (.var 0)) Roles.Examples.int,[]⟩],seed⟩ = some (true,true)
#guard go ⟨[⟨10,index (box (.var 0)) Roles.Examples.int,[]⟩],
  [(.var 10,.base .bool),(.base .bool,.var 10)]⟩ = some (true,false)
#guard go ⟨[⟨10,index (box (.var 0)) Roles.Examples.int,[]⟩],
  [(.var 10,.base .unit),(.base .unit,.var 10)]⟩ = some (true,false)
#guard go ⟨[⟨10,index (box (.var 1)) Roles.Examples.int,[]⟩],seed⟩ = none
#guard go ⟨[⟨10,⟨0,[]⟩,[]⟩],seed⟩ = none
#guard go ⟨[⟨10,index (box (.var 0)) Roles.Examples.int,[⟨99,20⟩]⟩],seed⟩ = none
-- Semantic-only interval knownness is deliberately not explicit paired evidence.
#guard go ⟨clauses,[(.base .str,.var 10),(.var 10,.var 5),(.var 5,.base .str)]⟩ = some (true,false)
-- Ground templates still follow this adapter's explicit receiver-evidence rule.
#guard go ⟨[⟨77,index (box Roles.Examples.str) Roles.Examples.int,[]⟩],[]⟩ = some (true,false)
#guard go ⟨[⟨77,index (box Roles.Examples.str) Roles.Examples.int,[]⟩],
  [(.var 77,.base .int),(.base .int,.var 77)]⟩ = some (true,true)
#guard go ⟨clauses ++ [⟨20,index (.var 0) Roles.Examples.int,[]⟩],seed⟩ = some (true,false)
#guard (go src).map Prod.fst = CommonRoleCheckedMixedSource.run
  (singletonEnv boxImpl) requiredRoles box_paterson src

example : go ⟨[],[]⟩ = some (true,true) := by decide
example : go ⟨[],[(.base .str,.base .int)]⟩ = some (false,true) := by decide
example : go ⟨[⟨10,⟨0,[]⟩,[]⟩],seed⟩ = none := by decide
example (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles) (s : Source) :
    run env roles wf s = run env roles wf ⟨s.clauses.reverse ++ s.clauses,
      s.ordinary.reverse ++ s.ordinary⟩ := by
  apply run_congr env roles wf awf
  · intro c; simp
  · intro q; simp
example : go src = some (true,true) ↔
    CommonRoleCheckedMixedSource.Models (singletonEnv boxImpl) requiredRoles src ∧
    AllDischarged (singletonEnv boxImpl) requiredRoles src := by
  simpa only [go,show CommonRoleSourceRoleObligations.ValidSource requiredRoles src.clauses by decide,
    true_and] using run_success_iff (singletonEnv boxImpl) requiredRoles box_paterson box_assoc_wellFormed src
end Cycle105
```
