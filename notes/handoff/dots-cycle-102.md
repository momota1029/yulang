# dots cycle 102 — ordinary専用変数を含む構造的mixed閉包

## 部分目標と結果

**有限な構造的occurrence列に、ordinary専用変数のslotを加えたallocationを計算し、
実mixed閉包の全モデルを単一のsource型valuationへ対応づけた。部分目標は閉じた。**
専用変数に架空の関連型occurrenceを作らない。専用変数から始まるseed、その変数を
中継するordinary相互辺、元occurrenceと専用slotの同名共有も、一つの一般定理で扱う。

新規CommonRoleAmbientMixedSourceは256行、14公開定理。
source commit `12cac3cf93ddb8eacd8cc9197b76ab7163a9e98e`、tree
`67678f799712d2d1a7566ed901b6e47d6cbaa392`。成果物8path、最新integrationから
引き継いだ監督役のgap analysis 1path、heartbeat 1pathの計10pathを公開。
取得した全10blobがlocalと一致。local source commit `653ccd072` と、取得した
remoteの木全体のdiffも空。新しい言語意味論の選択0件、質問ノート0件。
T1c全体、外側resolve_exact、X13〜X16の外側入口、B4の5橋は未完成。

## 定理の主張・量化子・位置づけ

以下はすべてYulang.CommonRoleAmbientMixedSource。
pは任意の有限structural Program、extraは任意の有限なscope解決済みsource名列。
tableは既存のoccurrence table ++ extra。sはその長さの任意のStateで、既存の
child/width/row文法証明を持つ。env/rolesは任意の既存registry、wfはcore WellFormed、
awfはAssocWellFormed。成功・整合性・モデル存在・fuel・計算済みgraph mapは前提でない。

1. name_embed: 任意p/extraと元tableのslotを、計算したprefixへ埋め込んでもsource名は同じ。補助。
2. receiver_source: 任意p/extra/occurrence indexについて、計算したreceiver slotの名は元occurrenceのreceiver名。補助。
3. output_source: 同じ任意入力で、計算したoutput slotの名は元output名。補助。
4. prepared_evidence: 任意p/extra/s/slot/baseで、物理的共有の追加前後の明示的scalar evidenceは同値。補助。一般の意味的帰結ではない。
5. prepared_linked: 任意p/extra/s/2slotで、共有追加後の相互辺 iff 元sの相互辺、またはsource名が同じ。補助。
6. allocated_to_named: 任意env/roles/p/extra/s/factのallocated mixed導出は、元source名上の独立Derivesへ移る。局所健全性。wf/awf不要。
7. named_to_allocated: 同じ任意入力の独立Derivesは、そのsource名を持つすべてのslotでallocated導出になる。局所完全性。wf/awf不要。
8. allocated_named_exact: 任意のallocated factについて6と7のiff。局所健全性・完全性。
9. named_support: 任意の独立Derivesの名前は、実計算tableのslotに現れる。空program、専用変数だけのprogramにも成り立つ。補助。
10. run_evidence_exact: 任意env/roles/wf/awf/p/extra/s/slot/baseで、実出力のscalar evidence iff そのsource名の独立Derives。局所健全性・完全性。
11. run_source_exact: 任意env/roles/wf/awf/p/extra/sと任意assignment vで、vが実出力の全atomを満たす iff 元sを満たし、全slotの型成分を因数分解する単一source valuationが存在し、それが全独立Derivesのscalar等式を満たす。局所健全性・完全性。
12. solver_source_exact: 同じ任意入力で、実ordinary solverが受理 iff 11のassignment/source valuationが存在する。局所健全性・完全性。
13. capacity: 任意env/roles/wf/p/extra/sで、飽和の異なるscalar fact数は4 * (2 * p.length + extra.length)以下。awf・整合性不要。補助・有限進捗。
14. checked_source_exact: さらに任意rawと既存checkがpを返す結果について、pのeraseがrawそのもので、rawはscope/arity/関連型名検査を満たし、11のiffが成り立つ。局所健全性・完全性。raw検査はextraの由来やsの整合性を保証しない。

独立Derivesは、元stateのseed、元stateの相互辺、pのメンバーに対する構造的
Materializesと独立role/associated宣言導出からなる。associatedの規則に実resolverや
cacheは入らない。名前の等式は同じ判断として扱う。この結果は全言語の
Typing/inferの健全性・完全性・主型性の三つ組ではない。主型性の完成も主張しない。

## 受け入れ条件と境界

cycle101で残っていた「ordinary専用変数がoccurrence tableの外にある」制限を、
有限のscope解決済み入力について取り除いた。別の専用変数を中継したassociatedと
ordinaryの交互閉包が、最初から最後まで実計算で到達する。

一方、extraの名前列・pの有限選択・元grammar-valid state・registryは依然入力。
実parser/declからのlowering、invocation同一性、動的fresh slot/where child生成、
一般Form、一般schedulerのfairness、最終四分類、辞書の観察同値は未達。
一般のordinary意味的帰結をすべてcache化するものではない。seed無し同名slotの
split boundsは実solverが矛盾を検出できても、explicit scalar cacheは空でよい。
一方向辺を相互辺に変えない。int/str以外のassociated materializationも広げていない。
extraの並び替えによるslot reindexingの一般定理は未証明。empty-extraの一般的な
旧入口同値も未証明で、今回はその具体的な検査だけを含む。

## 検証

最終production moduleで以下はすべてexit 0。全体local lake build、全Audit、全AxiomGate、
全verify-leanは指示に従い未実行。focusedやdiff-onlyを全体PASSとは呼ばない。

```text
cd lean; ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake build Yulang.CommonRoleAmbientMixedSource --wfail
✔ [358/358] Built Yulang.CommonRoleAmbientMixedSource (1.5s)
Build completed successfully (358 jobs).
exit 0
```

```text
cd lean; ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang102/boundary-check.lean
exit 0
```

```text
cd lean; ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang102/axioms.lean
'Yulang.CommonRoleAmbientMixedSource.name_embed' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleAmbientMixedSource.receiver_source' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleAmbientMixedSource.output_source' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleAmbientMixedSource.prepared_evidence' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleAmbientMixedSource.prepared_linked' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleAmbientMixedSource.allocated_to_named' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleAmbientMixedSource.named_to_allocated' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleAmbientMixedSource.allocated_named_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleAmbientMixedSource.named_support' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleAmbientMixedSource.run_evidence_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleAmbientMixedSource.run_source_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleAmbientMixedSource.solver_source_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleAmbientMixedSource.capacity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleAmbientMixedSource.checked_source_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

```text
python3 tools/boundary-input-inventory.py --check
PASS: inventory matches source hashes, imports, and ledger mentions.
CommonRole import scope=270; Main=93; Audit=270; ledger mentioned=143. Mention counts are not audit completion counts.
exit 0
```

```text
bash tools/verify-lean.sh . origin/integration/m1-final --no-build
verify-lean: . @ e17d586aa (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
exit 0
```

32 executable guards、3 kernel examples、no_seed補題を検査した。
2つのassociated occurrenceと5つの専用slotで、専用slot 5から始まり、関連型出力を
別の専用slot 25経由で次のreceiverへ運び、最後の専用slot 50まで届く。無関係な99は
未知のまま。同名20の専用slotも共有する。関連型が初めて作る矛盾、seed無し同名
split bounds、unsupported bool、空program、専用変数だけのprogram、empty-extraを含む。
同名の専用slotでもeffect成分は異なってよいmodelをkernelで確認した。
14定理の公理はpropext / Classical.choice / Quot.soundのみ。
production module SHA256: `2ecf9dd72b784928929199fc888da81a175f179d8341a19db1f5fffac8472173`。
このサイクルで独立reviewerは使っていない。

初回focused buildはprefix lookupの定義展開と暗黙引数、不要simp警告を直して成功。
回帰ではeffect成分の具体的な不一致を示すFin numeralの還元とDecidableを直した。
初回diff gateは未commit、次は先頭でないAudit import位置で失敗し、許可された先頭への
移動後にPASS。期待値を実出力に合わせる変更はしていない。
git diff --check / git diff --cached --checkも成功。

## Yulang2・specとの照合

新しい定義を書く前にspec6.3の関連型が普通の変数である規則、associated等式、
兄弟の安定待ちと順序独立を再読した。audit x-oracleのX13〜X16とC3-PARENTも確認。
C3-PARENTはwhereの左右入れ替えの実機受理で、この新しいallocation自体の検査ではない。
新しいYulang2実行はない。旧実装を新しい言語意味論の権威にはしていない。

## 復旧・公開・運用

開始2026-11-10T22:57:26Z。integrationは7e1d5494、workはdfe28a9a。
最新standing orders/inboxを再読し、ACTIVE・上限なし・I-11の25分・全体検証禁止を確認。
前cycle101はcompletedでreportあり。保持workspaceでintegrationをmergeし、前cycleの
Lean/Lake/Git processと他writerが無いことを確認。復旧不要。
監督役の2026-11-11 B4 gap analysisを取り込み、公開時にもそのpathを保った。

開始heartbeatは2f51641d。source公開は23:07:15Z、開始10分より前。source heartbeatの
updatedは準備時刻。10分heartbeatはf676a3a1で別途公開した。
個別blobを作りSHAを照合し、SHAのみtreeでlive work treeを保持した。
sourceはlive workを第一parent、integrationを追加parentとして、expected-head付き非force
ref更新で公開。全10blobと木全体を取得・照合。integrationへの書込みはない。
ツール出力の大きなJSONが上限で切れたため、ローカル読み取りを150000文字ずつに分割して
からblobを作成した。公開の拒否・承認待ち・未確定書込みの再試行はない。

開始・終了時の空きは47G。clone増設、cacheコピー、データ削除なし。使用量の枠は不明。
ログは../cache/yulang102。異なる公開pathは最終reportを含め11。

## B4に残る5橋と、このサイクルの位置

1. source_boundary_adequate: 有限scope解決済み入力のordinary専用slotを内部計算へ移した。
   実parser/declからscope・annotation・invocation・元state・extraを作る橋は未完成。
2. generated_work_closed: 固定有限tableでassociated/ordinaryが混在する閉包の守備範囲は広がった。
   実where/associated生成とfresh allocatorの閉包は未完成。
3. saturate_terminates_and_closes: 既存の有限Horn閉包を使用。新しい仕事/辺/slotを生成する
   一般schedulerの停止・fairnessは未完成。
4. saturated_frontier_exact: 実飽和後の独立な最終4分類への接続は未完成。
5. resolve_dictionary_order_sound: 正準source義務順の辞書構成と観察同値は未完成。

監督役のgap analysisのうち、橋1のallocation入力境界を一つ狭めた。
一般driver・Form・4分類・K2・辞書という大きな未完成パッケージの完了数は変わらない。
次候補は(a) ordinary loweringからextraと元stateを計算する接続、
(b) table全体のreindexingとモデル対応、(c) checked sourceから実生成childへの閉包。

## 再実行可能な境界回帰

```lean
import Yulang.CommonRoleAmbientMixedSource
open Yulang
open CommonRoleSettledConstraints (State)
open CommonRoleCandidateStateFrontier (extend)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All Atom)
open Roles.AssocExamples
namespace Cycle102
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
set_option synthInstance.maxSize 2048
open CommonRoleStructuralAssociatedTemplates (Program)
open CommonRoleAmbientMixedSource

def template : CommonRoleStructuralAssociatedTemplates.Template :=
  ⟨index (box (.var 0)) Roles.Examples.int,by decide⟩
def p : Program := [⟨10,20,0,template⟩,⟨30,40,0,template⟩]
def extras : List Nat := [5,25,50,20,99]
instance : NeZero (table p extras).length := ⟨by decide⟩
#guard table p extras = [10,20,30,40,5,25,50,20,99]
#guard (source p extras).occurrences.length = 2
#guard (source p extras).identity 7 = 20
#guard (source p extras).occurrences[0].receiver.val = 0

def links : List (Atom (Fin (table p extras).length)) :=
  [.tyLe (.var 4) (.var 0),.tyLe (.var 0) (.var 4),
   .tyLe (.var 1) (.var 5),.tyLe (.var 5) (.var 1),
   .tyLe (.var 5) (.var 2),.tyLe (.var 2) (.var 5),
   .tyLe (.var 3) (.var 6),.tyLe (.var 6) (.var 3)]
def edges : State (table p extras).length where
  atoms := links
  child := by intro a h; simp only [links,List.mem_cons,List.not_mem_nil,or_false] at h; rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
  width := by intro a b h tail ht; simp only [links,List.mem_cons,List.not_mem_nil,or_false] at h; rcases h with h | h | h | h | h | h | h | h <;> cases h <;> cases ht
  rows := by intro a h; simp only [links,List.mem_cons,List.not_mem_nil,or_false] at h; rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial

def initial := extend edges 4 .str
def finish (s : State (table p extras).length) := run (singletonEnv boxImpl) requiredRoles box_paterson p extras s
def cache (s : State (table p extras).length) :=
  CommonRoleMixedEvidenceClosure.saturate (singletonEnv boxImpl) requiredRoles box_paterson
    (source p extras) (prepared p extras s)
#guard (cache initial).length = 8
#guard CommonRoleOrdinaryKnownness.detect (finish initial).atoms 0 = some .str
#guard CommonRoleOrdinaryKnownness.detect (finish initial).atoms 1 = some .str
#guard CommonRoleOrdinaryKnownness.detect (finish initial).atoms 2 = some .str
#guard CommonRoleOrdinaryKnownness.detect (finish initial).atoms 3 = some .str
#guard CommonRoleOrdinaryKnownness.detect (finish initial).atoms 4 = some .str
#guard CommonRoleOrdinaryKnownness.detect (finish initial).atoms 5 = some .str
#guard CommonRoleOrdinaryKnownness.detect (finish initial).atoms 6 = some .str
#guard CommonRoleOrdinaryKnownness.detect (finish initial).atoms 7 = some .str
#guard CommonRoleOrdinaryKnownness.detect (finish initial).atoms 8 = none
#guard CommonRoleOpenPropagation.consistent (finish initial)
#guard (cache edges).length = 0
#guard CommonRoleOpenPropagation.consistent (finish edges)
#guard (cache (finish initial)).length = 8
#guard CommonRoleOpenPropagation.consistent (extend initial 6 .int)
#guard !CommonRoleOpenPropagation.consistent (finish (extend initial 6 .int))
#guard (cache (extend edges 4 .bool)).length = 2
#guard CommonRoleOrdinaryKnownness.detect (finish (extend edges 4 .bool)).atoms 1 = none

-- Physical sharing connects original and extra slots even without any scalar seed.
def bounds : List (Atom (Fin (table p extras).length)) :=
  [.tyLe (.base .int) (.var 1),.tyLe (.var 7) (.base .str)]
def unseeded : State (table p extras).length where
  atoms := bounds
  child := by intro a h; simp only [bounds,List.mem_cons,List.not_mem_nil,or_false] at h; rcases h with rfl | rfl <;> trivial
  width := by intro a b h tail ht; simp only [bounds,List.mem_cons,List.not_mem_nil,or_false] at h; rcases h with h | h <;> cases h <;> cases ht
  rows := by intro a h; simp only [bounds,List.mem_cons,List.not_mem_nil,or_false] at h; rcases h with rfl | rfl <;> trivial
#guard CommonRoleOpenPropagation.consistent unseeded
#guard !CommonRoleOpenPropagation.consistent (finish unseeded)
#guard (cache unseeded).length = 0

-- No artificial associated occurrence is needed for ordinary-only names.
def onlyNames : List Nat := [7,7,9]
instance : NeZero (table [] onlyNames).length := ⟨by decide⟩
def ordinary := extend (State.empty : State (table [] onlyNames).length) 0 .unit
#guard (source [] onlyNames).occurrences = []
#guard CommonRoleOrdinaryKnownness.detect
  (run (singletonEnv boxImpl) requiredRoles box_paterson [] onlyNames ordinary).atoms 1 = some .unit
#guard CommonRoleOrdinaryKnownness.detect
  (run (singletonEnv boxImpl) requiredRoles box_paterson [] onlyNames ordinary).atoms 2 = none
#guard CommonRoleOpenPropagation.consistent
  (run (singletonEnv boxImpl) requiredRoles box_paterson [] onlyNames ordinary)
#guard (run (singletonEnv boxImpl) requiredRoles box_paterson [] [] State.empty).atoms = []

-- The empty-extra case retains cycle101's concrete behavior.
instance : NeZero (table p []).length := ⟨by decide⟩
#guard CommonRoleOrdinaryKnownness.detect
  (run (singletonEnv boxImpl) requiredRoles box_paterson p [] (extend State.empty 0 .str)).atoms 1 = some .str
#guard CommonRoleOrdinaryKnownness.detect
  (run (singletonEnv boxImpl) requiredRoles box_paterson p [] (extend State.empty 0 .str)).atoms 2 = none

example (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (p : Program) (extra : List Nat) (s : State (table p extra).length)
    (v : Fin (table p extra).length → Comp Common.model) :
    All Common.model v (run env roles wf p extra s).atoms ↔
      All Common.model v s.atoms ∧ ∃ values, CommonRoleSourceDescent.Factors (table p extra) v values ∧
        ∀ a b, Derives env roles p extra s a b → Common.Equivalent (values a) (.base b) :=
  run_source_exact env roles wf awf p extra s v

theorem no_seed (p : Program) (extra : List Nat) (a : Nat) (b : Inference.Base)
    (h : Derives (singletonEnv boxImpl) requiredRoles p extra State.empty a b) : False := by
  induction h with
  | initial evidence => simp [CommonRoleOrdinaryKnownness.Evidence,State.empty] at evidence
  | transfer _ _ ih => exact ih
  | associated _ _ _ _ ih => exact ih

def differentRows (i : Fin (table [] onlyNames).length) : Comp Common.model :=
  (.base .int, fun _ => i.val = 0)
example : All Common.model differentRows
    (run (singletonEnv boxImpl) requiredRoles box_paterson [] onlyNames State.empty).atoms := by
  apply (run_source_exact (singletonEnv boxImpl) requiredRoles box_paterson
    box_assoc_wellFormed [] onlyNames State.empty differentRows).mpr
  refine ⟨?_,fun _ => .base .int,?_,?_⟩
  · intro atom member; cases member
  · intro slot; exact Common.equivalent_refl _
  · intro a b derived; exact False.elim (no_seed [] onlyNames a b derived)
example : (differentRows 0).2 ≠ (differentRows 1).2 := by
  intro equal
  have first : (differentRows 0).2 (0,[]) := by change (0 : Nat) = 0; rfl
  have second : ¬ (differentRows 1).2 (0,[]) := by change ¬ (1 : Nat) = 0; decide
  exact second (equal ▸ first)
end Cycle102
```

## Exact-source CI と最終公開

source 12cac3cf93ddb8eacd8cc9197b76ab7163a9e98e の両CIは
2026-11-10T23:09:39Zの確認でcompleted/success。
- Core CI: https://github.com/momota1029/yulang/actions/runs/42920639449
- Lean inference kernel: https://github.com/momota1029/yulang/actions/runs/42920639322

source公開後にproduction Lean変更なし。最終公開はreportとcompleted heartbeatだけ。
最終notes-only commitのCIと、上記exact-source CIおよびLean blob不変を区別する。
最終ref/tree/blobを取得して照合後、親へ完了を報告する。

最終report準備: 2026-11-10T23:10:19.635209Z、所要約12.9分。
部分目標を閉じ、時間を埋めるだけの補題は追加しなかった。
