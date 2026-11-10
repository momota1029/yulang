# dots cycle 103 — 名前つきordinary制約からのmixed閉包

## 部分目標と結果

**有限な名前つきordinary制約列から、extraの名前領域と文法証明つき初期Stateを
計算し、構造的associated programの実mixed閉包を独立なsourceモデルへ接続した。
部分目標は閉じた。** callerはextra・slot map・初期Stateを渡さない。
元の単方向制約を保ち、両向きscalar seedと相互辺は独立な導出規則へ対応する。
制約の並べ替え・重複でallocationが変わってもordinary整合性は変わらない。

新規 `CommonRoleNamedOrdinaryInputs` は292行、13公開定理。
最終source commit `e6a0f2b8614709494983928668d92c9520cf8579`、tree
`767770b4ef1d9814f63b22940e4a3681a0fe94b8`。
第一source checkpoint `4d884b728212929c6a36c92c280fcf56ad6877c4` は途中公開。
8個のsource pathを公開し、取得したsource treeとローカルのsourceは一致する。
T1c全体・外側resolve_exact・X13〜X16の外側入口・B4の5橋は未完成。
新しい言語意味論の選択0件、質問ノート0件。

## 定理の主張・量化子・位置づけ

以下はすべてYulang.CommonRoleNamedOrdinaryInputs。
pは任意の有限な構造的Program、inputは任意の有限な名前つきsubtype制約列。
Termは既存scalar Baseまたはscope解決済みNat名。tableはpの既存occurrence tableと、
inputの全変数名を重複除去したextraを連結したもの。env/rolesは任意の既存registry。
実行にwf : Roles.WellFormed env.cores、正確性にawf : Roles.AssocWellFormed env rolesを
明示する。成功、モデル存在、整合性、fuel、slot map、初期Stateは前提でない。
モデルを述べるv/valuesは全称の量化変数、または結論内の存在変数。

1. mem_inequality（補助、健全性/完全性）: 任意のallocated Term a/bについて、
   そのordinary atomが生成されるiff、名前へ写した元の不等式がinputにある。
2. initial_evidence（補助、両側）: 任意slot/baseについて、初期stateのpaired evidenceは、
   元inputの同名variableとbaseの両向き制約がそろうことと同値。
3. initial_linked（補助、両側）: 任意slot i/jについて、初期stateの相互辺は、
   元inputのその二名の両向きvariable制約がそろうことと同値。
4. allocated_to_named（健全性側）: 任意名/baseの既存allocated導出は、元inputのseed、
   相互辺、独立な構造的associated Stepだけからなる名前上のDerivesを与える。
5. named_to_allocated（完全性側）: 任意の上記Derivesは、計算済みstate上のallocated
   導出へ戻る。ordinary専用名もinputから必ず割り当てられる。
6. derives_exact（両側）: 上記二つの導出のiff。p/inputや導出長に固定の上限は置かない。
7. initial_models（両側）: 任意v/valuesとsource型factorizationの下で、初期stateを
   vが満たすiff、valuesが元の名前つき不等式をすべて満たす。
8. run_evidence_exact（両側）: 任意slot/baseについて、実mixed閉包出力のpaired
   evidenceは、そのsource名に対する独立Derivesと同値。
9. run_source_exact（両側）: 任意vが実出力を満たすiff、vが一つのsource型valuationへ
   因数分解でき、そのvaluationが元inputの不等式と全Derivesのscalar等式を満たす。
   effect行は同一視しない。
10. solver_source_exact（両側）: 実ordinary solverの整合性trueは、上記元不等式と
    全独立導出を満たすsource型valuationが存在することと同値。vはcaller入力から消えた。
11. derives_congr（補助、両側）: 任意left/right inputが同じmembershipを持てば、
    任意名/baseの独立Derivesは一致する。
12. models_congr（両側）: 同じmembershipを持つ任意left/rightの独立Modelsは同値。
13. solver_congr（両側）: 同じmembershipを持つ任意left/rightを実行して得るordinary
    整合性trueは同値。allocationの並びとslot数の一致は前提にしない。

この断片の健全性/完全性への部品であり、全言語の主型性は主張しない。
拒否の一部は既存ordinary不等式の不整合で説明するが、言語全体の拒否分類は未接続。

## 明示した限界とreview

Derivesは**直接paired evidenceと相互辺**の閉包で、一般ordinary entailmentではない。
例えばint <= a、a <= c、c <= intは全ordinaryモデルでa/cをintに固定するが、直接
scalar seed pairが無いためDerivesは増えずassociated生成は起動しない。この境界も検査した。
ordinary整合性はすべてのrole要求の解決成功ではない。未seed・unsupported scalar・
曖昧なassociated要求は等式を生成しない場合がある。

独立のread-only reviewerがsource、依存する定義、設計ノートを読み、blockingな
数学的不一致なしと報告。独立OrdinaryModelsとDerives、solverの逆向き構成、
congruenceの入力境界、型だけのsource共有を確認した。reviewerの助言で上記境界を
docstring・README・設計・報告に明記した。reviewerはビルド/公理監査を実行していない。
その後のextra重複除去の差分もreviewし、名前や元の制約を失わないことを確認した。

## 実行回帰と性能上の修正

最終sourceで36個の実行guard、4個のkernel example、no_seed補題が通る。
2つのassociated occurrenceとordinary専用名を含むchainで、5のstr seedから10、
associated出力20、ordinary専用25、receiver30、associated出力40、ordinary専用50へ
情報が流れる。99はallocation外。逆順・重複入力でも同じ終端evidenceを得る。

同じchainに50=intを加え、元stateは整合するがassociated閉包後は矛盾することを検査。
seed無しのint<=7<=str矛盾、単方向辺で情報を同値転送しないこと、unsupported bool、
ordinary専用program、空入力、slotゼロのbase同士の不整合、上記int三角形を含む。
同名7のreceiver/output/extraの3slotで、型は共有しつつeffect行が異なるモデルも確認。

初版はinput中の名前の出現ごとにextra slotを作った。22-slotのchain evidenceは通るが、
そのordinary整合性checkを含む回帰は180秒でtimeout（exit124）。切り分けの実行も
上限で停止した。大きな整合性checkを除いた35guardの限定版は通ったが、それだけを
最終成功には数えなかった。
原因は不要な同名extra slotの複製によるordinary問題の膨張。extraをeraseDupsで
重複除去し、元inputの不等式はそのまま保持した。同じchainは11-slotとなり、
元の大きな整合性・遅延矛盾checkを戻した最終36guardが通った。
期待する言語挙動を変えていない。allocation列と長さの期待値だけを設計に沿って変更し、
一般のsource意味保存定理を再buildした。一般的な性能保証は主張しない。

## 検証

全体lake build、全Audit、全体verify-leanのbuildはstanding ordersに従いローカルでは
実行していない。以下はfocused結果とdiff-only gateである。

```text
cd lean; ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake build Yulang.CommonRoleNamedOrdinaryInputs --wfail
✔ [359/359] Built Yulang.CommonRoleNamedOrdinaryInputs (1.6s)
Build completed successfully (359 jobs).
exit 0
```

```text
cd lean; ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang103/boundary-dedup.lean
exit 0
```

```text
cd lean; ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang103/axioms.lean
'Yulang.CommonRoleNamedOrdinaryInputs.mem_inequality' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleNamedOrdinaryInputs.initial_evidence' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleNamedOrdinaryInputs.initial_linked' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleNamedOrdinaryInputs.allocated_to_named' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleNamedOrdinaryInputs.named_to_allocated' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleNamedOrdinaryInputs.derives_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleNamedOrdinaryInputs.initial_models' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleNamedOrdinaryInputs.run_evidence_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleNamedOrdinaryInputs.run_source_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleNamedOrdinaryInputs.solver_source_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleNamedOrdinaryInputs.derives_congr' depends on axioms: [propext]
'Yulang.CommonRoleNamedOrdinaryInputs.models_congr' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleNamedOrdinaryInputs.solver_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

```text
python3 tools/boundary-input-inventory.py --check
PASS: inventory matches source hashes, imports, and ledger mentions.
CommonRole import scope=271; Main=93; Audit=271; ledger mentioned=144. Mention counts are not audit completion counts.
exit 0
```

```text
bash tools/verify-lean.sh . origin/integration/m1-final --no-build
verify-lean: . @ 03022b847 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
exit 0
```

13定理の公理はpropext / Classical.choice / Quot.soundのみ。
production module SHA256: `764c04d580888b52e538441f68abe5e90ef7f0519e91576ff1a2777613ae492b`。
git diff --check / staged diff checkも成功。初回focused buildから証明は通り、
重複除去後も再buildと公理監査が通った。未検証の大きな入力での計算量は残る。

## Yulang2・specとの照合

新しい定義の前にspec6.3の「関連型の変数は普通の型変数」「等式は先に束縛しない」
を再読し、既存audit x-oracleのX13〜X16とC3-PARENTを照合した。
これらはsourceでの関連制約・共有・兄弟の例であり、本allocationそのものの実機oracle
ではない。新しいYulang2実行はない。旧実装を意味論の権威として扱っていない。

## 復旧・公開・運用

開始2026-11-10T23:26:13Z。integration/workは双方8b4ba57f。
最新standing orders/inboxをremoteから読み、ACTIVE・上限なし・I-11の25分上限・
全体検証禁止を確認。cycle102はcompletedでreportがあり、保持workspaceと報告を再読。
前cycleのLean/Lake/Git processと他writerなし。保持cloneにintegrationをmergeした。
復旧不要。作業開始・終了の空きは47G、clone増設・cacheコピー・データ削除なし。

開始heartbeat e63eb0e8、10分直前heartbeat49d8e149。最初の成果物checkpoint4d884b72を
23:37頃に公開し、重複除去後のsource e6a0f2b8を23:42より前に公開した。
各blobを個別uploadしSHAを照合、live treeをbaseにSHA-only treeを作り、
expected-head付きnonforceでwork/dots-mainだけを更新。integrationへの書込みなし。
8 source pathを取得して一致を確認し、remote heartbeatを取り込んだlocal tree全体も一致。
Gitのwork枝fetchはFETCH_HEADを更新する設定だったため、staleなremote-tracking refではなく
取得したFETCH_HEADのcommit/treeを確認した。未確定のwrite再試行や拒否はない。

使用量の枠は不明。ログは../cache/yulang103。公開した異なるpathは最終reportとheartbeatを
含め10。最終source以降のLean変更はない。最終公開はreportとcompleted heartbeatだけ。

## B4に残る5橋と次候補

1. source_boundary_adequate: named ordinary inputからextraと初期Stateを計算する範囲は
   閉じた。実parser/一般式/宣言からこのinput、scope、template、invocationを導く橋は未完成。
2. generated_work_closed: 固定有限領域のassociated/ordinary交互閉包を使う。実whereから
   新childを生成しfresh allocationへ閉じる橋は未完成。
3. saturate_terminates_and_closes: 既存有限Horn閉包の停止を使用。一般Form、仕事/辺/slotを
   増やすscheduler、fairness、plateau後の新情報の一般停止は未完成。
4. saturated_frontier_exact: 実飽和から独立な最終四分類への接続は未完成。
5. resolve_dictionary_order_sound: 正準source義務順の辞書構成・観察同値は未完成。

監督役のgap analysisの大きな未完パッケージの完成数は変わらない。
次候補: (a) checked scalar expression入力から今回のnamed inequalitiesへの橋、
(b) 実associated clause抽出とordinary inputを同じ外側入口で検査する接続、
(c) generated childのsource領域閉包。一般ordinary knownnessとexplicit-evidenceを
混同せず、未完成の橋を仮定に押し出して完成扱いにしない。

## 再実行可能な境界回帰

```lean
import Yulang.CommonRoleNamedOrdinaryInputs
open Yulang
open Roles.AssocExamples
open CommonRoleNamedOrdinaryInputs
open CommonRoleStructuralAssociatedTemplates (Program)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)
namespace Cycle103
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
set_option synthInstance.maxSize 4096

def template : CommonRoleStructuralAssociatedTemplates.Template :=
  ⟨index (box (.var 0)) Roles.Examples.int,by decide⟩
def p : Program := [⟨10,20,0,template⟩,⟨30,40,0,template⟩]
def input : Input :=
  [(.var 5,.base .str),(.base .str,.var 5),
   (.var 5,.var 10),(.var 10,.var 5),
   (.var 20,.var 25),(.var 25,.var 20),
   (.var 25,.var 30),(.var 30,.var 25),
   (.var 40,.var 50),(.var 50,.var 40)]
def finish (p : Program) (xs : Input) := run (singletonEnv boxImpl) requiredRoles box_paterson p xs
def observed (p : Program) (xs : Input) (a : Nat) : Option Inference.Base :=
  (CommonRoleSourceDescent.representative (table p xs) a).bind fun i =>
    CommonRoleOrdinaryKnownness.detect (finish p xs).atoms i
#guard extra input = [5,10,20,25,30,40,50]
#guard (table p input).length = 11
#guard observed p input 5 = some .str
#guard observed p input 10 = some .str
#guard observed p input 20 = some .str
#guard observed p input 25 = some .str
#guard observed p input 30 = some .str
#guard observed p input 40 = some .str
#guard observed p input 50 = some .str
#guard observed p input 99 = none
#guard CommonRoleOpenPropagation.consistent (finish p input)
#guard observed p input.reverse 50 = some .str
#guard observed p (input ++ input) 50 = some .str

def conflict : Input := input ++ [(.var 50,.base .int),(.base .int,.var 50)]
#guard CommonRoleOpenPropagation.consistent (initial p conflict)
#guard !CommonRoleOpenPropagation.consistent (finish p conflict)

def split : Input := [(.base .int,.var 7),(.var 7,.base .str)]
#guard observed [] split 7 = none
#guard !CommonRoleOpenPropagation.consistent (finish [] split)

def directed : Input := [(.var 5,.base .str),(.base .str,.var 5),(.var 5,.var 10)]
#guard observed p directed 5 = some .str
#guard observed p directed 10 = none
#guard observed p directed 20 = none
#guard CommonRoleOpenPropagation.consistent (finish p directed)

def boolInput : Input := [(.var 10,.base .bool),(.base .bool,.var 10)]
#guard observed p boolInput 10 = some .bool
#guard observed p boolInput 20 = none

def ordinaryOnly : Input := [(.var 7,.base .unit),(.base .unit,.var 7),(.var 7,.var 9),(.var 9,.var 7)]
#guard observed [] ordinaryOnly 7 = some .unit
#guard observed [] ordinaryOnly 9 = some .unit
#guard CommonRoleOpenPropagation.consistent (finish [] ordinaryOnly)
#guard (table [] []).length = 0
#guard (finish [] []).atoms = []
#guard CommonRoleOpenPropagation.consistent (finish [] [])
#guard (table [] [(.base .int,.base .str)]).length = 0
#guard !CommonRoleOpenPropagation.consistent (finish [] [(.base .int,.base .str)])
#guard CommonRoleOpenPropagation.consistent (finish [] [(.base .int,.base .int)])

-- Transitive semantic equality is outside the explicit-evidence detector.
def triangle : Input := [(.base .int,.var 10),(.var 10,.var 30),(.var 30,.base .int)]
#guard CommonRoleOpenPropagation.consistent (finish p triangle)
#guard observed p triangle 10 = none
#guard observed p triangle 30 = none
#guard observed p triangle 20 = none

example (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (p : Program) (xs : Input) :
    CommonRoleOpenPropagation.consistent (run env roles wf p xs) = true ↔
      ∃ values : Nat → Common.Ty, OrdinaryModels xs values ∧
        ∀ a b, Derives env roles p xs a b → Common.Equivalent (values a) (.base b) :=
  solver_source_exact env roles wf awf p xs

example (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (p : Program) (xs : Input) :
    CommonRoleOpenPropagation.consistent (run env roles wf p xs) = true ↔
      CommonRoleOpenPropagation.consistent (run env roles wf p (xs.reverse ++ xs)) = true := by
  apply solver_congr env roles wf awf p xs (xs.reverse ++ xs)
  intro q; simp

-- A source name still identifies only the type component, never effect rows.
def dupProgram : Program := [⟨7,7,0,template⟩]
def duplicate : Input := [(.var 7,.var 7)]
instance : NeZero (table dupProgram duplicate).length := ⟨by decide⟩
def differentRows (i : Fin (table dupProgram duplicate).length) : Comp Common.model :=
  (.base .int,fun _ => i.val = 0)
theorem no_seed (a : Nat) (b : Inference.Base)
    (h : Derives (singletonEnv boxImpl) requiredRoles dupProgram duplicate a b) : False := by
  induction h with
  | initial h _ => simp [duplicate] at h
  | transfer _ _ _ ih => exact ih
  | associated q _ _ _ ih => exact ih
example : All Common.model differentRows (finish dupProgram duplicate).atoms := by
  apply (run_source_exact (singletonEnv boxImpl) requiredRoles box_paterson
    box_assoc_wellFormed dupProgram duplicate differentRows).mpr
  refine ⟨fun _ => .base .int,(fun _ => Common.equivalent_refl _),?_,?_⟩
  · intro q h
    simp only [duplicate,List.mem_cons,List.not_mem_nil,or_false] at h
    subst q; exact Common.subtype_refl _
  · intro a b h; exact False.elim (no_seed a b h)
example : (differentRows 0).2 ≠ (differentRows 1).2 := by
  intro eq
  have h : (differentRows 0).2 (0,[]) := by change (0 : Nat) = 0; rfl
  have no : ¬ (differentRows 1).2 (0,[]) := by change ¬ (1 : Nat) = 0; decide
  exact no (eq ▸ h)
end Cycle103
```

## Exact-source CI と最終公開

最終source e6a0f2b8614709494983928668d92c9520cf8579 の両CIは
2026-11-10T23:44:18.131493+00:00 の確認でcompleted/success。
- Lean inference kernel: https://github.com/momota1029/yulang/actions/runs/42925483232
- Core CI: https://github.com/momota1029/yulang/actions/runs/42925483087

source公開後にproduction Lean変更なし。最終notes-only commitのCIと、上記exact-source CI、
および同じLean blobを保持することを区別する。最終ref/tree/blob取得の照合後に親へ完了報告。

最終report準備: 2026-11-10T23:44:18.131493+00:00、所要約18.1分。
部分目標を閉じ、時間を埋めるだけの補題は追加しなかった。
