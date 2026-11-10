# dots cycle 90 — 区間 where の再帰的な仕事領域と元sourceへの割当

## 結果と部分目標

**既存の有限Form/linear interval capture断片で、実where宣言から再帰的な潜在仕事領域を計算し、独立Reachとのiff、実prepare childに対する閉包、元rootのcanonical source ownerとgraph snapshot保存を閉じた。**

新規 `CommonRoleIntervalWorkClosure` は289行、20公開定理。callerが有限visit列、fuel、仕事領域、owner列を渡す形ではない。実際の宣言checkerと両endpointのPaterson減少に基づく全再帰である。根・子の成功やordinary stateのmodelの存在を仮定せず、任意の有限registryと任意の区間goalを扱う。

部分目標は閉じた。ただし**endpoint構文が固定された断片の潜在仕事領域**であり、ordinary stateの絞り込み後に別の構造がmaterializeされる一般飽和ではない。全B4主定理は未達で、主要橋は5本のまま。

## 正確な範囲と入力

- `Edge` はregistry所属、既存の独立 `Accepts`、元requirements所属からchildを導く。`Reach` はその有限経路。実closureの出力を判断の定義に戻していない。
- `children` は全宣言を個別にinspectし、accepted branchの全where子を保持する。複数の候補を同じordinary stateへ無条件に連言するsolverではない。候補guard・選択・4分類は付けていない。
- 既存のregistry全体の `scan` はoutside宣言が一つでもあると全体がnoneになる。今回のclosureは他のaccepted branchを残し、outsideを `boundaries` に別に列挙する。**registry全体scanの成功と同値ではない。**
- `compute` のsomeは、宣言checkerが全registryで通って有限仕事領域を返したことだけを意味する。全scanがsupportedであるとは言わない。`boundaries`は別の入口であり、computeの戻り値には含まれない。
- 宣言checkerは公開compute内で計算する。補助closure/domainのChecked前提は消えていないが、外側の `compute_reach_exact` はCheckedを結果側に置く。無関係でもchecker不合格の宣言があればcomputeはnoneになる。
- 元rootのsource tableは両endpointの元syntaxから取る。各occurrenceは実locateでその最初のcanonical ownerへ戻る。同じ型の値であることはsource同一性ではない。順序・重複を保持する。
- 任意graphのsnapshot保存は証明するが、そのgraphがordinary stateを正しく表すことは証明しない。prepareのslots・old demands・bindingSourceは元入口の入力のまま。closure生成自体にはこの3入力は要らない。
- `CommonRoleWhereSourceModels.run` のcaptureはdeclaration/goalから決まり、old demandsを読んで構造をmaterializeし直す処理ではない。そのため、今回をstate-dependent飽和と呼ばない。

## 追加定理と日本語の主張

全て `Yulang.CommonRoleIntervalWorkClosure`。registryは任意有限列、goalは任意の既存区間Goal。Checkedを使う箇所を明記する。「側」はM1全体でなく今回の局所対応への効き方。

1. `children_exact`: 任意registry/parent/childで実children所属と独立Edgeがiff。**健全性・完全性**。
2. `outside_exact`: 任意registry/goal/declarationでoutside所属とregistry所属＋実inspectのnoneがiff。**健全性・完全性**。
3. `edge_decreases`: 任意Checked registryと任意Edgeで、両endpoint合計サイズが真に小さくなる。**停止性の補助**。
4. `edge_sources`: 任意Edgeで、childの全ambient endpoint名はparentの元source tableに属する。Checkedやmodelの前提は不要。**source健全性**。
5. `closure_complete`: 任意Checked registryと独立Reachで、到達先が計算closureに属する。**完全性**。
6. `closure_sound`: 任意Checked registry/root/targetで、計算closure所属から独立Reachを得る。**健全性**。
7. `closure_exact`: 上の二方向のiff。**健全性・完全性**。
8. `reach_trans`: 任意の接続可能な二Reachが合成できる。**補助**。
9. `generated_closed`: 任意Checked registry、root closure memberからの任意Edgeのchildも同じclosureに属する。**生成閉包**。
10. `reach_sources`: 任意Reachで全target endpoint名が元rootに属する。**source健全性**。
11. `domain_included`: 任意Checked registry/rootで計算domainの全endpoint名が元rootに属する。**source健全性**。
12. `domain_owners`: 任意Checked registry/rootで、実locateが返すowner列が存在し、全occurrenceを順序通り復元し、各ownerはcanonical。model・source mapの前提はない。**割当補助**。
13. `prepared_child_closed`: 任意Checked registry、closure member goal、registry member declaration、任意slots/old/bindingSource、実prepareのreturned resultと任意actual childで、そのchildがroot closureに属する。**実生成に対する健全性・閉包**。実行成功は局所転送の前提で、全source成功を主張しない。
14. `boundaries_exact`: 任意Checked registry/root/goal/declarationで、計算boundaries所属と独立Reach＋registry所属＋inspect noneがiff。**健全性・完全性**。
15. `compute_exact`: 任意registry/root/出力列で、computeのsomeとChecked証明＋正確なclosure列が存在することがiff。**実行正確性**。
16. `compute_reach_exact`: 任意registry/root/targetで、computeが返すある列にtargetが属することとChecked＋独立Reachがiff。callerのWF/fuel前提はない。**外側の健全性・完全性**。
17. `domain_allocation`: 任意Checked registry/rootで計算owner列があり、全domain occurrenceについて新rootが元ownerのretainと一致し、任意cyclic graph/role/visible列の全snapshotを保存する。**割当健全性**。
18. `domain_name_exact`: 任意Checked registry/root/nameで、domain所属と元root table所属がiff。root自体もdomainに入る。**source範囲の正確性**。この名前集合の有限性だけで構造的仕事の有限性を主張しない。
19. `reach_registry_ext`: 同じdeclaration membershipを持つ任意2registryでReachを転送する。**順序補助**。
20. `closure_registry_ext`: 任意Checkedな2registryが同じmembershipなら、任意root/goalのclosure所属はiff。**仕事集合の順序独立**。列や辞書の同値ではない。

主型性・全B4の4分類・dictionary observational equivalenceを新たに証明した定理はない。既存Lean定義・定理は変更していない。Yulang/Audit import、全20定理のAudit登録、README、台帳AA節、coverage表、設計ノートとINDEXを更新した。

## 検証

最終production Leanに対して以下は全てexit 0。

```text
cd lean
ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake build Yulang.CommonRoleIntervalWorkClosure --wfail
✔ [306/306] Built Yulang.CommonRoleIntervalWorkClosure (1.1s)
Build completed successfully (306 jobs).
ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang90/boundary-check.lean
exit 0 (37 examples; no diagnostic output)
ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang90/axioms.lean
'Yulang.CommonRoleIntervalWorkClosure.children_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleIntervalWorkClosure.outside_exact' depends on axioms: [propext]
'Yulang.CommonRoleIntervalWorkClosure.edge_decreases' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleIntervalWorkClosure.edge_sources' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleIntervalWorkClosure.closure_complete' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleIntervalWorkClosure.closure_sound' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleIntervalWorkClosure.closure_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleIntervalWorkClosure.reach_trans' depends on axioms: [propext]
'Yulang.CommonRoleIntervalWorkClosure.generated_closed' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleIntervalWorkClosure.reach_sources' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleIntervalWorkClosure.domain_included' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleIntervalWorkClosure.domain_owners' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleIntervalWorkClosure.prepared_child_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleIntervalWorkClosure.boundaries_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleIntervalWorkClosure.compute_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleIntervalWorkClosure.compute_reach_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleIntervalWorkClosure.domain_allocation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleIntervalWorkClosure.domain_name_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleIntervalWorkClosure.reach_registry_ext' depends on axioms: [propext]
'Yulang.CommonRoleIntervalWorkClosure.closure_registry_ext' depends on axioms: [propext, Quot.sound]
```

37 examples: 深さ20、異なる両endpointのsource名、重複候補、registry逆順、元source ownerの復元、空registry、wrong role/arity、inconsistent endpoint syntax、normalization後のcapture、無関係な不正宣言、nonlinear/join headのoutside、scan全体がnoneでも残す実accepted descendants、外側一般定理と実prepare転送の使用。元の期待値は変えていない。

```text
python3 tools/boundary-input-inventory.py --check
PASS: inventory matches source hashes, imports, and ledger mentions.
CommonRole import scope=257; Main=93; Audit=257; ledger mentioned=130. Mention counts are not audit completion counts.
bash tools/verify-lean.sh . origin/integration/m1-final --no-build
verify-lean: . @ 6d0651b06 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

`git diff --check`もexit 0。これはローカルdiff-only gateで、全体verifyのPASSではない。ローカル全体lake build、全Audit、AxiomGate、全体verifyは指示に従い実行していない。新20定理の公理はpropext/Classical.choice/Quot.soundの範囲。

## 公開sourceとCI

source commit: `18dde3f997ab2ad43ff41822222c2ba02b100457`。

- Core CI: completed / success — https://github.com/momota1029/yulang/actions/runs/42861602486
- Lean inference kernel: completed / success — https://github.com/momota1029/yulang/actions/runs/42861602498

exact-source SHAを指定して確認した。Leanのproof jobは、full build --wfail、全Audit trust=0、source/value/regular/record等の実行例の各stepがsuccessだった。ローカルで実行したとは記載しない。このsource公開後にproduction Leanを変えていない。最終report/heartbeatのCIとは区別する。

source tree `e05cab5320bb9cde63e0216ddd60ca1d0afe4de9` は2,328 entries、非truncated。9変更pathsのblob SHA一致、全treeはlocal checkpoint `e76bee5cb` と一致。明示tracking ref付きgit fetch後のlocal/remote tree差分も空だった。

## 独立レビューと実機

読み取り専用レビューは重大な欠陥を見つけなかった。独立Edge/Reach、両endpointのPaterson停止、実prepareへの接続、source ownerと任意graph snapshotを確認した。既存registry-wide scanとの区別、およびcomputeのsomeが全scan supportedを意味しない点を指摘したため、上の境界説明と3件の再実行済み回帰検査を追加した。レビュー自身はビルドしておらず、ローカル検証の独立再実行とは数えない。

新定義前にspec 6.3と `work/dots-audit:notes/audit/x-oracle.md` のC3-PARENT/C3-PARENT-NEGを読んだ。両兄弟順とchild欠如の過去の実機結果を参照した。今回のinterval closureのYulang2新規実機runは未実施。過去oracleは今回の完全性や全区間飽和の証拠ではない。

新規質問ノート0件。未回答の意味論を選ばず、既存capture/Patersonと明示されたfragmentを使った。I-13台帳AA節を追加したが、全モジュールの意味監査完了や期限超過の解消は主張しない。

## 残る主要橋と次の候補

B4主定理への主要橋は5本のまま。
1. `source_boundary_adequate`: 実parser/declからscope・grouped clause・associated annotationを導く一般橋。
2. `generated_work_closed`: 今回は固定interval syntaxの実where閉包とsource割当まで。state-dependent materialization後の一般childを同じ有限template領域へ入れる橋。
3. `saturate_terminates_and_closes`: 状態の絞り込み・再生成・候補guardを含むPaterson/K2 driver。今回の構造的DFS停止だけでは完成しない。
4. `saturated_frontier_exact`: 独立な未完成diagnostic treeと全言語の4分類。
5. `resolve_dictionary_order_sound`: 正準source obligation順に沿うdictionaryの観察同値。

次の候補は2本:
- `interval_materialized_child_all_states`: 既存int-only/unaryの `CommonRoleSourceTemplateClosure.actual_child_all_states` に相当する一般Form interval/source-template橋。元sourceのownerを保持し、実state materializationから全future-stateの生成childを含める。carrierの翻訳を先に定義し、任意visit列の入力で置換しない。
- `guarded_interval_work_models_exact`: 今回の潜在仕事を候補guardとordinary model保存へ結ぶ。複数candidateの制約を無条件に連言しない。root/childの選択と未完成診断treeを保つ。

この2候補を閉じても5主要橋全体の完成とは限らない。具体的な残り本数は上の名前つき5橋で報告する。

## 復旧、時刻、資源、公開

- 作業開始のdate記録は2026-11-10T16:57:30Z。初期integration/work liveはbead7fff2。ACTIVE、上限なし、standing orders/inboxを再読。cycle89 completed heartbeatとreportあり、前writer/buildなし。既存workspaceにintegrationをmergeして再開し、clone/cacheを増やしていない。
- 開始heartbeat 061d2c95、source checkpoint 18dde3f9、検証中heartbeat ef4d206aをwork/dots-mainだけへ公開。heartbeatの本文時刻は実UTCから生成した。
- 個別blobとSHA-only treeで公開し、live treeをbaseに全体tree一致後、force=false/expected-headでrefを更新。承認拒否・結果不確定なし。integration/main等へは書いていない。
- 最初のheartbeat file patchは同一pathの複数operationで拒否され、何も変更されなかった。修正後の通常writeを使用。最初のscratch検査はreserved identifier `at` と未指定Checked metavariableで失敗したため、名前/明示引数を直し再実行した。production Leanは初回と最終focused buildとも通った。
- 最初のlocal manifest readは出力上限でtruncatedとなりJSON parse失敗。外部write前だった。個別fileを短いreadに分け、完全な内容と全blob SHAを検証してからuploadした。外部のuploadを分割して別fileにしたのではない。
- 変更pathsはsource/doc8、heartbeat、最終reportの計10。最終design補足/report/heartbeatも公開して照合する。未公開production Leanはない。
- 空きは開始・終了前とも48G/63G（使用13G）。使用量の枠は不明。ログは../cache/yulang90。

報告作成時刻: 2026-11-10T17:11:20Z。経過13.8分。指定終了期限17:22:19Z。部分目標が閉じた後、検証・独立レビュー・報告を行い、時間を埋める補題は追加していない。

## 再実行用の境界検査全文

```lean
import Yulang.CommonRoleIntervalWorkClosure
open Yulang
open CommonRoleCaptureNormalization (Form)
open CommonRoleStablePaterson (Declaration)
open CommonRoleIntervalPaterson (Goal)
open CommonRoleIntervalWorkClosure
namespace Cycle90BoundaryCheck
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def recursive : Declaration := ⟨0, 10, [.tick (.var 0)], [(0, [.var 0])]⟩
def terminal : Declaration := ⟨0, 11, [.var 0], []⟩
def registry := [recursive, terminal]
theorem checked : Checked registry := List.all_eq_true.mp (by decide +kernel)
def mkGoal (low up : Form) : Goal := ⟨0, [(low, up)]⟩
def root := mkGoal (.tick (.tick (.var 7))) (.tick (.tick (.var 8)))
def middle := mkGoal (.tick (.var 7)) (.tick (.var 8))
def leaf := mkGoal (.var 7) (.var 8)

example : closure registry checked root = [root, middle, leaf] := by decide +kernel
example : compute registry root = some [root, middle, leaf] := by decide +kernel
example : children registry root = [middle] := by decide +kernel
example : outside registry root = [] := by decide +kernel
example : outside registry leaf = [recursive] := by decide +kernel
example : boundaries registry checked root = [(leaf, recursive)] := by decide +kernel
example : domain registry checked root = [7, 8, 7, 8, 7, 8] := by decide +kernel
example : (CommonRoleWhereSourceAllocation.locate [7, 8] (domain registry checked root)).map
    (List.map Fin.val) = some [0, 1, 0, 1, 0, 1] := by decide +kernel
example : CommonRoleWhereSourceAllocation.locate [] (domain registry checked root) = none := by decide +kernel
example : Reach registry root leaf := (closure_exact registry checked root leaf).mp (by decide +kernel)
example : compute [] root = some [root] := by decide +kernel
example : compute registry (mkGoal .int .int) = some [mkGoal .int .int] := by decide +kernel
example : outside registry (mkGoal .int .int) = [] := by decide +kernel
example : outside registry (mkGoal .int (.tick .int)) = [recursive] := by decide +kernel
example : compute registry (mkGoal .int (.tick .int)) = some [mkGoal .int (.tick .int)] := by decide +kernel
example : compute registry (mkGoal (.tick .int) (.tick (.tick .int))) =
    some [mkGoal (.tick .int) (.tick (.tick .int)), mkGoal .int (.tick .int)] := by decide +kernel
example : compute registry (mkGoal (.join (.tick .int) (.tick .int)) (.tick .int)) =
    some [mkGoal (.join (.tick .int) (.tick .int)) (.tick .int), mkGoal .int .int] := by decide +kernel
example : compute registry ⟨99, root.arguments⟩ = some [⟨99, root.arguments⟩] := by decide +kernel
example : outside registry ⟨99, root.arguments⟩ = [] := by decide +kernel
example : compute registry ⟨0, []⟩ = some [⟨0, []⟩] := by decide +kernel

def repeated := [recursive, recursive, terminal]
theorem repeatedChecked : Checked repeated := List.all_eq_true.mp (by decide +kernel)
example : closure repeated repeatedChecked root = [root, middle, leaf, leaf, middle, leaf, leaf] := by decide +kernel
example : boundaries repeated repeatedChecked root =
    [(leaf, recursive), (leaf, recursive), (leaf, recursive), (leaf, recursive),
     (leaf, recursive), (leaf, recursive), (leaf, recursive), (leaf, recursive)] := by decide +kernel
example : compute [terminal, recursive] root = some [root, middle, leaf] := by decide +kernel

def growing : Declaration := ⟨0, 12, [.var 0], [(0, [.tick (.var 0)])]⟩
example : compute [growing] root = none := by decide +kernel
example : compute (registry ++ [growing]) root = none := by decide +kernel

def nonlinear : Declaration := ⟨0, 13, [.pair (.var 0) (.var 0)], []⟩
def nonlinearGoal := mkGoal (.pair .int .int) (.pair .int .int)
example : compute [nonlinear] nonlinearGoal = some [nonlinearGoal] := by decide +kernel
example : outside [nonlinear] nonlinearGoal = [nonlinear] := by decide +kernel

def joined : Declaration := ⟨0, 14, [.join (.var 0) (.var 1)], []⟩
example : outside [joined] (mkGoal .int .int) = [joined] := by decide +kernel
example : compute [joined] (mkGoal .int .int) = some [mkGoal .int .int] := by decide +kernel

def tower : Nat → Form → Form
  | 0, f => f
  | n+1, f => .tick (tower n f)
example : (compute registry (mkGoal (tower 20 (.var 700000)) (tower 20 (.var 8)))).map List.length =
    some 21 := by decide +kernel
example : (compute registry (mkGoal (tower 20 .int) (tower 20 .int))).map List.length =
    some 21 := by decide +kernel
example (ds : List Declaration) (g t : Goal) :
    (∃ goals, compute ds g = some goals ∧ t ∈ goals) ↔ Checked ds ∧ Reach ds g t :=
  compute_reach_exact ds g t
example (ds : List Declaration) (wf : Checked ds) (g : Goal) (n : Nat) :
    n ∈ domain ds wf g ↔ n ∈ CommonRoleWhereSourceAllocation.parentTable g :=
  domain_name_exact ds wf g n
example (ds : List Declaration) (wf : Checked ds) (root goal : Goal)
    (member : goal ∈ closure ds wf root) (d : Declaration) (present : d ∈ ds)
    (slots : Nat → α) (old : List (CommonRoleSourceIntervalBatches.Demand α))
    (src : Nat → Nat) (result : CommonRoleWhereSourceAllocation.Prepared α goal)
    (returned : CommonRoleWhereSourceAllocation.prepare slots old d goal src = some (some result))
    (target : Goal) (child : target ∈ result.candidate.children) :
    target ∈ closure ds wf root := prepared_child_closed ds wf root goal member d present
      slots old src result returned target child
-- The registry-wide scanner and this potential-work enumerator intentionally differ.
def mixed := [recursive, joined]
theorem mixedChecked : Checked mixed := List.all_eq_true.mp (by decide +kernel)
example : CommonRoleIntervalCandidates.scan root mixed = none := by decide +kernel
example : compute mixed root = some [root, middle, leaf] := by decide +kernel
example : boundaries mixed mixedChecked root =
    [(root, joined), (middle, joined), (leaf, recursive), (leaf, joined)] := by decide +kernel
end Cycle90BoundaryCheck
```
