# dots cycle 86 — ソースから計算する canonical な名前割当て

## 結果と部分目標

**既存の有限 source と input だけから名前の写像を計算し、独立な導出・model の存在・readiness を保ち、安全な名前変更の後にも同じ source/input の組を返し、再実行しても変わらない割当てを閉じた。**

cycle85 の検査は caller が写像を選ぶ入口だった。今回の `CommonRoleComputedSourceAllocation.allocate` はその写像を source と input の support の最初の出現位置から計算する。caller は写像、単射性の証明、domain list、package、ordinary State、model、fuel、solver の成功を渡さない。新規モジュール171行、公開12定理。

これは名前表現の部分目標の完了であり、宣言から source/input を生成する完了ではない。B4 の主要橋は5本のまま。core/associated registry の wf/awf、scalar/one-binder の有限断片は引き続き前提。言語意味論、invocation の共有方針、最終分類は選んでいない。

## 何が一般化され、何が境界のままか

- 全ての有限 source/input を量化する。固定した Parent 例の成功だけではない。
- support に重複があっても同じ名前は同じ index になる。capacity は**出現数**であり、distinct name 数へ最小化する表ではない。例えば input の名前 [1000000,1000000,7] は [0,0,2] になる。未使用 index は許す。
- 全 query に対する evidence iff を得た。support 外の名前は capacity へ写り、使用中の名前の範囲と交わらない。cycle85 の任意写像と違い、この計算写像では query の support 所属を前提にしない。
- canonical なのは、同じ順序の source/式/input を衝突なく名前変更した場合。source や input の順序、重複、role/member ID、Goal の binder は保持する。兄弟の並び替えの後にも**同じ組**になるとは主張しない。readiness の順序独立は既存入口の別の定理。
- `Models` は source に現れる名前だけを制約する既存定義。空 source と input 内の矛盾だけなら readiness=true となることを回帰検査に入れた。全 input の大域的整合性へ定義を強めてはいない。
- bool/unit は既存 ordinary evidence だが、今回の role receiver の符号化対象ではない。false はこの有限 readiness 検査の失敗であり、言語の rejected 診断ではない。

## 主要定理と量化範囲

全て新規 `CommonRoleComputedSourceAllocation` 内。既存の定理・型・意味論の変更なし。

1. `encode_bound`: 任意 src/input/name と support 所属について、計算 index は support の長さ未満。補助。
2. `decode_encode`: 同じ量化範囲で、その index の元の support 要素は元の名前と等しい。補助・identity の復元。
3. `encode_safe`: 任意 src/input の計算写像について、support 内の任意 a,b の像が等しければ a=b。補助・衝突回避を caller の前提から除く。
4. `checked_allocation`: 任意 src/input で cycle85 のチェック付き名前変更が計算した組を必ず返す。補助・実行検査との接続。
5. `allocated_derives`: 任意 env/roles/src/input/name/head に対して、割当て後の encode(name) の独立導出と元の name の独立導出が iff。健全性・完全性。query 所属前提なし。
6. `allocated_models`: 任意 env/roles/src/input の割当て後と前の Models が iff。健全性・完全性。valuation は存在量化の内部で構成する。
7. `allocated_readiness`: 任意 env/roles/wf/awf/src/input で、再検査・再割当て・再飽和した readiness Bool が等しい。健全性・完全性の観察保存。solver 成功前提なし。
8. `support_rename`: 任意写像 f と src/input で、名前変更後の support list が元の support.map f と等しい。順序・重複も含めた補助。
9. `allocated_name_bound`: 任意 src/input で、出力source/inputのsupport中の全名前が元の計算capacity未満。補助・有限領域の閉包。
10. `encode_rename`: 任意 f/src/input と有限 CollisionFree、supported name に対し、名前変更後に計算した encode(f name) が元の encode(name) と等しい。補助・canonical identity。
11. `allocate_rename`: 任意 f/src/input と有限 CollisionFree に対し、名前変更後と前の allocate のsource/inputの組が等しい。表現の健全性・完全性。global injectivity 不要。
12. `allocate_idempotent`: 任意 src/input の allocate に再び allocate を施しても同じ組。補助・再実行は新しい名前を作らない。

主型性、任意言語式の型付け iff、動的生成子の停止、辞書の観察同値は証明していない。private な list/index/congruence/composition の証明補助も、新たな仮定を隠していない。

## 検証

最終 source に対して以下は全て exit 0。

```text
cd lean
ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake build Yulang.CommonRoleComputedSourceAllocation --wfail
✔ [295/295] Built Yulang.CommonRoleComputedSourceAllocation (1.6s)
Build completed successfully (295 jobs).
ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang86/boundary-check.lean
exit 0
```

境界検査は33 examples。空・重複・非常に大きい名前・unused query・input-only capture防止・全Natでは非単射のmod10・安全でないcollapse・矛盾・不正member・bool/unit・非整列の兄弟・順序と重複の保持・任意入力の一般定理の利用を検査した。成功期待値の変更なし。

12公開定理のtrust=0公理出力全文:

```text
'Yulang.CommonRoleComputedSourceAllocation.encode_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleComputedSourceAllocation.decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleComputedSourceAllocation.encode_safe' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleComputedSourceAllocation.checked_allocation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleComputedSourceAllocation.allocated_derives' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleComputedSourceAllocation.allocated_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleComputedSourceAllocation.allocated_readiness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleComputedSourceAllocation.support_rename' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleComputedSourceAllocation.allocated_name_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleComputedSourceAllocation.encode_rename' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleComputedSourceAllocation.allocate_rename' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleComputedSourceAllocation.allocate_idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`python3 tools/boundary-input-inventory.py --check` (exit 0):

```text
PASS: inventory matches source hashes, imports, and ledger mentions.
CommonRole import scope=253; Main=93; Audit=253; ledger mentioned=126. Mention counts are not audit completion counts.
```

`bash tools/verify-lean.sh . origin/integration/m1-final --no-build` (exit 0):

```text
verify-lean: . @ 64684c388 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

`git diff --check`もexit 0。未commitの時点のdiff gateはFAILだったのでcommit後に再実行した。最初のLean試行はdependent indexのrewriteとlist flatMapの簡約を直した。境界検査の初回は不要なInhabited要求を生む`[0]!`をOptionの射影に直した。失敗した試行はPASSと数えない。

公理はpropext / Classical.choice / Quot.soundのみ。ローカルでは全体lake build、全Audit、AxiomGate、全体verifyを実行していない。上記gateのPASSはdiff-only。全体の検証は監督役が担当する。

## 公開sourceのCI

source `b45db64e6fa75d2957a91d20a497683afa4ae5cb` の以下は15:10 UTCの再取得で両方completed/success。

- Core CI: https://github.com/momota1029/yulang/actions/runs/42841264069
- Lean inference kernel: https://github.com/momota1029/yulang/actions/runs/42841264302

これは公開sourceそのもののCIで、最終report/heartbeat commitのCIとは区別する。source公開後にLeanコードを変えていない。境界検査を29から33 casesへ増やし再実行した。

## Yulang2との照合と設計判断

開始時にwork/dots-auditを取得し、x-oracleのC3-PARENT（左右両順とgeneric成功）とC3-PARENT-NEG（missing child拒否）を再読。spec/06-roles.md §6.3の関連等式と兄弟連言も読み直した。数値名の割当ては表現の問題なので、新たなYulang2の規則として扱わない。新規Yulang2実機run、Rust parserからの適合、宣言sourceのloweringの意味保存は未実行/未証明。

`Roles.Impl.constraints : List Goal` はgrouped receiver/output annotationsを持たない。今回の割当ては、それを復元するものでもinvocation共有を決めるものでもない。新規質問ノート0件。既存Q1/Q2、cycle23/24は未決。

## 受け入れ条件と残りの橋

I-4のsource identityで、caller mapを計算で置き換える部分目標を閉じた。I-13のW節とinventoryを更新。I-13全モジュール監査は未完で、元のcycle72期限超過が解消したとは主張しない。

B4主定理への主要橋は5本:
1. `source_boundary_adequate`: 既存有限sourceの計算割当ては今回閉じた。宣言/式からsource/inputを抽出し忠実性を示す橋は残る。
2. `generated_work_closed`: 動的where子の生成・登録を計算source領域へ接続する橋が残る。
3. `saturate_terminates_and_closes`: 一般Paterson/K2 driverの停止と意味的閉包が残る。
4. `saturated_frontier_exact`: 独立な最終四方向分類が残る。
5. `resolve_dictionary_order_sound`: Bool保存・canonicalな数値名は辞書の観察同値ではない。

次の候補は、(1) grouped where関連等式と元のsource注釈を保持する権威ある宣言carrierを確認し、独立な抽出判断を作ること、(2) 確定した注釈/式からnamed scalar inputを導出すること、(3) その実際のlowering出力を今回の計算割当てへ渡してsource boundaryを閉じること。数値名前変更だけの派生補題を増やす段階ではない。

## 復旧、公開、資源、時刻

- 開始2026-11-10T14:56:27Z。live integration/workはともに8ee411da。latest standing orders/inboxのACTIVE・上限なしを確認し、integrationを既存作業treeへmergeした。先行cycle85はcompletedでreportあり、残存writer/buildなし。追加clone/cacheコピーなし。
- 初回心拍のref更新は、treeがheartbeatだけだという誤った危険判定で拒否された。拒否された操作は実行されていない。read-onlyで2314 entriesの非truncated treeと、親との差がheartbeat一件だけで削除0件のcompareを取得した。この新しい証拠の後に同じ非force更新を一度だけ再試行し成功。9a93291eのlive refも確認した。未解決の承認待ち・不確定writeなし。
- 約12分の中間公開b45db64eで、8 source/doc pathsと心拍を公開した。個別blob→SHAだけのtree、live treeをbaseとして保持、live parentに対しforce=false/expected-headで更新。公開前compareでも削除0件。
- 公開source treeは`736ec5e0c0b450773796d498089cbb825f58f6d7`、2316 entries、非truncated、変更9 pathsのSHA全一致。tree全体がlocal HEADと一致し、再fetch後のgit diffも空。
- 最終report/heartbeatも同じ方法で公開・再取得する。成果物は合計10 paths。integration等への書込みなし。
- 空き容量は開始と15:09時点とも48G / 63G（使用13G）。使用量の枠は不明。ローカル検証ログは../cache/yulang86。再実行用検査全文は下記。

報告作成時刻: 2026-11-10T15:11:49Z。経過15.4分。部分目標、focused検証、source公開照合、exact-source CIは完了。残りは最終report公開照合。時間を埋めるための補題は追加しない。

## 再実行用の境界検査全文

```lean
import Yulang.CommonRoleComputedSourceAllocation
open Yulang CommonRoleNamedSourceEntry CommonRoleNamedSourceRenaming
open CommonRoleAssociatedClauseExtraction (Clause Source)
open CommonRoleComputedSourceAllocation
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Cycle86BoundaryCheck

def roles := Roles.AssocExamples.requiredRoles
def env := Roles.AssocExamples.singletonEnv Roles.AssocExamples.boxImpl
theorem wf : Roles.WellFormed env.cores := Roles.AssocExamples.box_paterson
theorem awf : Roles.AssocWellFormed env roles := Roles.AssocExamples.box_assoc_wellFormed
def goal : Roles.Goal := Roles.AssocExamples.index
  (Roles.AssocExamples.box (.var 0)) Roles.Examples.int
def bare : Clause := ⟨7, goal, []⟩
def associated : Clause := ⟨3, goal, [⟨0, 7⟩]⟩
def src : Source := [associated, bare]
def input : Assumptions := [(3, .str)]
def mod10 (n : Nat) : Nat := n % 10

-- Duplicated support retains one identity and permits unused capacity positions.
example : CommonRoleFiniteSourceRenaming.support src input = [3, 7, 3, 7, 3] := by decide
example : encode src input 3 = 0 := by decide
example : encode src input 7 = 1 := by decide
example : encode src input 999 = 5 := by decide
example : allocate src input = ([⟨0, goal, [⟨0, 1⟩]⟩, ⟨1, goal, []⟩], [(0, .str)]) := by decide
example : allocate (allocate src input).1 (allocate src input).2 = allocate src input := by decide
example : allocate [] [] = ([], []) := by decide
example : allocate [] [(1000000, .str), (1000000, .int), (7, .bool)] =
    ([], [(0, .str), (0, .int), (2, .bool)]) := by decide
example : encode [] [] 17 = 0 := by decide

-- A globally noninjective map is enough when safe on the actual support.
example : allocate (renameSource mod10 src) (renameInput mod10 input) = allocate src input := by decide
example : allocate (renameSource (fun n => n + 100) src)
    (renameInput (fun n => n + 100) input) = allocate src input := by decide
example : allocate (renameSource (fun _ => 0) src)
    (renameInput (fun _ => 0) input) ≠ allocate src input := by decide

-- Input-only names cannot be captured by compaction.
example : allocate [bare] [(17, .str)] = ([⟨0, goal, []⟩], [(1, .str)]) := by decide
example : runSource env roles wf (allocate [bare] [(17, .str)]).1
    (allocate [bare] [(17, .str)]).2 = false := by decide +kernel
example : runSource env roles wf (allocate src input).1 (allocate src input).2 = true := by decide +kernel
example : runSource env roles wf (allocate src []).1 (allocate src []).2 = false := by decide +kernel
example : runSource env roles wf (allocate [bare] [(7, .str), (7, .int)]).1
    (allocate [bare] [(7, .str), (7, .int)]).2 = false := by decide +kernel
example : runSource env roles wf (allocate [{associated with equations := [⟨99, 7⟩]}] input).1
    (allocate [{associated with equations := [⟨99, 7⟩]}] input).2 = false := by decide +kernel

-- Inherited fragment boundaries are preserved, not silently strengthened.
example : runSource env roles wf (allocate [] [(7, .str), (7, .int)]).1
    (allocate [] [(7, .str), (7, .int)]).2 = true := by decide +kernel
example : runSource env roles wf (allocate [bare] [(7, .bool)]).1
    (allocate [bare] [(7, .bool)]).2 = false := by decide +kernel
example : runSource env roles wf (allocate [bare] [(7, .unit)]).1
    (allocate [bare] [(7, .unit)]).2 = false := by decide +kernel
example : allocate [] [(7, .str), (17, .str)] ≠
    allocate [] (renameInput mod10 [(7, .str), (17, .str)]) := by decide

-- Canonicality does not sort siblings or drop duplicate occurrences.
example : allocate [bare, associated] input ≠ allocate src input := by decide
example : (allocate [bare, bare] [(7, .str)]).1.length = 2 := by decide
example : runSource env roles wf (allocate [bare, associated] input).1
    (allocate [bare, associated] input).2 = true := by decide +kernel
example : ((allocate src input).1.head?).map (·.goal) = some goal := by decide
example : ((allocate src input).1.flatMap (·.equations)).map (·.name) = [0] := by decide

-- General use: neither successful solving nor a chosen encoding is assumed.
example (source : Source) (assumptions : Assumptions) :
    runSource env roles wf (allocate source assumptions).1 (allocate source assumptions).2 =
      runSource env roles wf source assumptions :=
  allocated_readiness env roles wf awf source assumptions
example (source : Source) (assumptions : Assumptions) :
    Models env roles (allocate source assumptions).1 (allocate source assumptions).2 ↔
      Models env roles source assumptions := allocated_models env roles source assumptions
example (source : Source) (assumptions : Assumptions) (name : Nat) (head : Inference.Base) :
    Derives env roles (allocate source assumptions).1 (allocate source assumptions).2
      (encode source assumptions name) head ↔ Derives env roles source assumptions name head :=
  allocated_derives env roles source assumptions name head
example (source : Source) (assumptions : Assumptions) (f : Nat → Nat)
    (safe : CommonRoleFiniteSourceRenaming.CollisionFree f source assumptions) :
    allocate (renameSource f source) (renameInput f assumptions) = allocate source assumptions :=
  allocate_rename f source assumptions safe
example (source : Source) (assumptions : Assumptions) :
    allocate (allocate source assumptions).1 (allocate source assumptions).2 = allocate source assumptions :=
  allocate_idempotent source assumptions

-- Even unsupported queries reflect exactly for this computed allocator.
example : ¬ Derives env roles (allocate [bare] [(7, .str)]).1
    (allocate [bare] [(7, .str)]).2 (encode [bare] [(7, .str)] 17) .str := by
  rw [allocated_derives]
  intro derived
  have supported := CommonRoleFiniteSourceRenaming.derives_supported env roles [bare] [(7, .str)] 17 .str derived
  have absent : 17 ∉ CommonRoleFiniteSourceRenaming.support [bare] [(7, .str)] := by decide
  exact absent supported

end Cycle86BoundaryCheck
#print axioms Yulang.CommonRoleComputedSourceAllocation.encode_bound
#print axioms Yulang.CommonRoleComputedSourceAllocation.decode_encode
#print axioms Yulang.CommonRoleComputedSourceAllocation.encode_safe
#print axioms Yulang.CommonRoleComputedSourceAllocation.checked_allocation
#print axioms Yulang.CommonRoleComputedSourceAllocation.allocated_derives
#print axioms Yulang.CommonRoleComputedSourceAllocation.allocated_models
#print axioms Yulang.CommonRoleComputedSourceAllocation.allocated_readiness
#print axioms Yulang.CommonRoleComputedSourceAllocation.support_rename
#print axioms Yulang.CommonRoleComputedSourceAllocation.allocated_name_bound
#print axioms Yulang.CommonRoleComputedSourceAllocation.encode_rename
#print axioms Yulang.CommonRoleComputedSourceAllocation.allocate_rename
#print axioms Yulang.CommonRoleComputedSourceAllocation.allocate_idempotent
```
