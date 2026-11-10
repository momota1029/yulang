# dots cycle 87 — 明示した scalar 注釈からの入力生成

## 結果と部分目標

**既存の literal 式と明示された scalar 注釈の有限断片について、入力の検査、named facts の生成、canonical な名前割当て、role readiness をつなぎ、元の binding と source clause の独立判断との iff を証明した。**

caller は ordinary atoms、State、named assumptions、slot/map、package、fuel、model、solver 成功を渡さない。値は既存 `Inference.Expr`、その意味は既存 `Core.PresenceGeneration.Typing Common.model` を使う。新規 `CommonRoleAnnotatedLiteralInputs` は173行、公開8定理。

重要な境界は、literal の型付けだけから scalar の等式は導けないこと。`int` literal は `int | str` という広い型にも型付けできるが、その型は `int` と等価ではない。この反例を形式化し、明示した scalar 注釈の上界と literal の下界を合わせたときだけ、既存の exact scalar seed へ接続した。反例だけで終わらず、この修正した入口の健全性・完全性まで閉じた。

これは bridge 1 の狭い入力側の部分目標。一般の宣言/式からの lowering、主型性、全言語の型付け iff、B4 の完成ではない。主要橋は5本のまま。

## 量化範囲と残った入力

- 任意の有限 binding list と grouped source を量化する。固定 Parent 例だけの iff ではない。
- Binding は scope-resolved な名前、既存 Expr、明示 scalar annotation を持つ。literal が annotation と一致することを全件検査する。非literal は、言語として型が付く場合も、この入口では unsupported な断片外。false を言語の rejected と読まない。
- 注釈なしの式はこの carrier に入れていない。暗黙の上界、推測した注釈、role の一意性から exact seed を作っていない。
- `lower` は順序と重複を保持する。名前は引き続き scope-resolved source identity。数値割当てはcycle86から計算する。invocation を共有する規則は決めていない。
- source-only な model domain はcycle83から継承する。空 source と無関係な同名 input の矛盾だけなら true になる。これは全 binding の大域的整合性を検査する入口ではない。各 binding 自体の literal/annotation 不一致は source に無関係でも false。
- bool/unit は入力の正しい literal tag として検査できるが、role receiver の first-order 符号化は既存のint/strだけ。新しい role 意味論を足していない。
- env/roles と core/associated registry のwf/awf、grouped source、source名、明示注釈が残る。parser、値payload、浮動小数点、非literal inference、生成childは範囲外。

## 主要定理と側

全て `CommonRoleAnnotatedLiteralInputs`。既存Leanの定義・定理は変更していない。

1. `binding_meaning_exact`: 任意binding b、そのvalueがannotationのliteralである証拠、任意Common.Ty valueについて、既存literal typingとannotationの上界が、valueとannotationの等価性にiff。健全性・完全性。
2. `literal_check_exact`: 任意name/literal/annotation scalar pairで、singletonの構文検査が通ることと、既存typingとannotationを満たすvalueの存在がiff。健全性・完全性。非literal checkerの完全性ではない。
3. `literal_does_not_force_scalar`: int literalはint/str unionにも型付けでき、そのunionはintと等価ではない。補助・反例。literalだけで上界を捏造できない。
4. `lower_exact`: 任意有限bindingsとValid、任意name/headについて、計算したfact listへの所属と元bindingの独立Seedがiff。健全性・完全性。
5. `derives_exact`: 任意env/roles/src/bindings、Valid、name/headについて、lowerしたfactsからの既存導出と元binding/clauseの新しい独立導出がiff。健全性・完全性。
6. `models_exact`: 同じ任意入力とValidで、既存named modelの存在と元binding/clauseの独立Modelsがiff。健全性・完全性。モデルは実行入力ではない。
7. `models_bindings`: 任意の上記入力、独立factsを満たすvalues、元bindingsのmember b、そのnameのsource-domain所属について、実際のliteral typingとannotation意味が成立。健全性。source所属を省いていない。
8. `run_exact`: 任意env/roles/wf/awf/src/bindingsで、実行trueと、Valid bindings・ValidSource・独立Models・全元role clauseを解消する独立Derivesがiff。健全性・完全性。成功の前提、caller atoms、map、model、fuelなし。

## 検証

最終sourceに対して以下はexit 0。

```text
cd lean
ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake build Yulang.CommonRoleAnnotatedLiteralInputs --wfail
✔ [296/296] Built Yulang.CommonRoleAnnotatedLiteralInputs (1.3s)
Build completed successfully (296 jobs).
ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang87/boundary-check.lean
exit 0
```

境界検査は31 examples。全4scalar tag、annotation不一致、無関係な名前、非常に大きい名前、共有名の矛盾、source外だけの矛盾、重複、兄弟逆順、不正member/arity、empty入力、一般定理の利用、実際に型が付く非literalを断片外として扱う境界を検査した。期待値は変えていない。

8公開定理のtrust=0公理出力全文:

```text
'Yulang.CommonRoleAnnotatedLiteralInputs.binding_meaning_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleAnnotatedLiteralInputs.literal_check_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleAnnotatedLiteralInputs.literal_does_not_force_scalar' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleAnnotatedLiteralInputs.lower_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleAnnotatedLiteralInputs.derives_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleAnnotatedLiteralInputs.models_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleAnnotatedLiteralInputs.models_bindings' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleAnnotatedLiteralInputs.run_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
```

```text
python3 tools/boundary-input-inventory.py --check
PASS: inventory matches source hashes, imports, and ledger mentions.
CommonRole import scope=254; Main=93; Audit=254; ledger mentioned=127. Mention counts are not audit completion counts.
bash tools/verify-lean.sh . origin/integration/m1-final --no-build
verify-lean: . @ 46d2e08ba (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

`git diff --check`もexit 0。初回試行ではCommon.modelと旧Inference.Modelの型が違う点を修正し、同じExprを扱う既存presence-aware typingへ接続した。その後、namespaceとconjunction proofの構成を修正した。失敗した試行をPASSと数えない。最終focused buildはwarningなし。

ローカル全体lake build、全Audit、AxiomGate、全体verifyは指示どおり実行していない。上記gateのPASSはdiff-only。公理はpropext/Quot.soundのみが7定理、run_exactにClassical.choiceが加わる。新公理なし。

## 公開sourceのCI

source `88ba4627e7005aa97b5945907d0c50ec0b7df624` の再取得結果:
- Core CI: completed / success; https://github.com/momota1029/yulang/actions/runs/42846756757
- Lean inference kernel: completed / success; https://github.com/momota1029/yulang/actions/runs/42846757000

最終report/heartbeat commitのCIとは区別する。source公開後にproduction Leanは変更していない。scratch境界検査だけ27件から31件へ増やして再実行した。

## 仕様とYulang2の照合

`spec/03-expressions.md` 3.1のliteral、`spec/04-types.md` 4.2の明示value annotationを読み直した。4.2は推論結果≤注釈を検査し公開値型をannotationとする。effectは素通りする。今回のliteralはpureな断片で、annotationでeffect rowを固定する規則を足していない。

`work/dots-audit`を取得し、x-oracleのC3-ACCEPT-01（int/textの値）とC3-PARENT（左右両順、generic成功）、C3-PARENT-NEG（child欠如）を参照。これらは素材であり、今回のlowering定理を旧実機で証明したものではない。新規Yulang2実機run、Rust parserからの忠実性は未実行/未証明。

新規質問ノート0件。今回の注釈の扱いはspec4.2から取り、invocation共有や非linear headの判断は既存質問のまま。意味論の未決を勝手に解消していない。

## 受け入れ条件と残りの橋

I-4のsource boundaryで、明示scalar注釈つきliteralからの入力生成を閉じた。I-13のX節とinventoryを更新。I-13全モジュール監査は未完。過去の期限超過が解消したとは主張しない。

B4主定理への主要橋は5本:
1. `source_boundary_adequate`: このliteral/annotation入力断片は閉じた。宣言/式からgrouped sourceとscope-resolved名を導く橋、非literalの入力推論は残る。
2. `generated_work_closed`: 動的where子の生成・登録を計算source領域へ接続する橋が残る。
3. `saturate_terminates_and_closes`: 一般Paterson/K2 driverの停止と意味的閉包が残る。
4. `saturated_frontier_exact`: 独立な最終分類が残る。
5. `resolve_dictionary_order_sound`: Bool readinessの保存は辞書の観察同値ではない。

次の候補は、(1) parser/宣言carrierにおける明示annotationとscope名の保存、(2) 非literalではpaired equalityを仮定せずordinary区間を保持するinput lowering、(3) grouped where注釈を保つ宣言carrierから実sourceを生成すること。単なる数値名前変更の派生補題には戻らない。

## 復旧、公開、資源、時刻

- 開始2026-11-10T15:29:19Z。live integration/workはともにc9b0c6d4。standing ordersとinboxのACTIVE・上限なしを読み直した。前回cycle86のcompleted heartbeat/reportあり、前writer/buildなし。既存workspaceへintegrationをmergeし、clone/cacheを増やしていない。
- 起動heartbeatは7c919110として公開し、API refを確認。10分前後のsource checkpointは88ba4627。heartbeatは準備時刻15:37:00Zで更新、公開は15:40 UTC。公開中も作業を停止していない。
- 個別blobをアップロードし、全既存treeをbaseとしてSHAのみの変更treeを作成。親との差を確認後、work/dots-mainだけにforce=false/expected-headで公開した。初回manifest表示はローカルoutput truncationでJSON parseが失敗したが、外部write前。manifestを小さくし、既存大fileはchunk読取りで完全contentを復元して個別blobのSHAを確認した。外部writeの拒否・不確定結果なし。
- 公開source treeは`5167d63a5fe5af4de28150e7e210195cd4c97d1e`。2319 entries、非truncated、9変更pathsのSHA全一致、tree全体もlocal27344ff9bのtreeと一致。API refも88ba4627を返す。直後のgit transport fetchは旧c9b0c6d4を返したため、git trackingとの差が空とは主張しない。APIによるtree照合を公開確認の根拠にした。
- source/doc8 pathsとheartbeat、最終reportを合わせて計10 paths。integrationなど他branchは変更していない。最終report/heartbeatも同じ方法で公開後に照合する。
- 空きは開始時・15:40時点とも48G/63G（使用13G）。使用量の枠は不明。検証ログは../cache/yulang87。

報告作成時刻: 2026-11-10T15:42:34Z。経過13.3分。指示された終了期限は15:52:19Z。時間を埋めるための補題は追加しない。

## 再実行用の境界検査全文

```lean
import Yulang.CommonRoleAnnotatedLiteralInputs
open Yulang
open CommonRoleAnnotatedLiteralInputs
open CommonRoleAssociatedClauseExtraction (Clause Source)
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Cycle87BoundaryCheck

def roles := Roles.AssocExamples.requiredRoles
def env := Roles.AssocExamples.singletonEnv Roles.AssocExamples.boxImpl
theorem wf : Roles.WellFormed env.cores := Roles.AssocExamples.box_paterson
theorem awf : Roles.AssocWellFormed env roles := Roles.AssocExamples.box_assoc_wellFormed
def goal : Roles.Goal := Roles.AssocExamples.index
  (Roles.AssocExamples.box (.var 0)) Roles.Examples.int
def bare : Clause := ⟨7, goal, []⟩
def associated : Clause := ⟨3, goal, [⟨0, 7⟩]⟩
def src : Source := [associated, bare]
def input : Bindings := [⟨3, .lit .str, .str⟩]

example : Valid input := by decide
example : Valid [⟨3, .lit .int, .int⟩] := by decide
example : Valid [⟨3, .lit .bool, .bool⟩] := by decide
example : Valid [⟨3, .lit .unit, .unit⟩] := by decide
example : ¬ Valid [⟨3, .lit .unit, .bool⟩] := by decide
example : lower input = [(3, .str)] := rfl
example : run env roles wf src input = true := by decide +kernel
example : run env roles wf [bare, associated] input = true := by decide +kernel
example : run env roles wf src [] = false := by decide +kernel
example : run env roles wf src [⟨3, .lit .int, .str⟩] = false := by decide +kernel
example : run env roles wf [bare] [⟨7, .lit .str, .str⟩] = true := by decide +kernel
example : run env roles wf [bare] [⟨17, .lit .str, .str⟩] = false := by decide +kernel
example : run env roles wf [bare] [⟨7, .lit .bool, .bool⟩] = false := by decide +kernel
example : run env roles wf [bare] [⟨7, .lit .unit, .unit⟩] = false := by decide +kernel
example : run env roles wf [] [] = true := by decide +kernel
example : run env roles wf [] [⟨7, .lit .str, .int⟩] = false := by decide +kernel
example : run env roles wf [bare] [⟨7, .lit .str, .str⟩, ⟨7, .lit .int, .int⟩] = false := by decide +kernel
-- The inherited source-domain model ignores unrelated input contradictions.
example : run env roles wf [] [⟨7, .lit .str, .str⟩, ⟨7, .lit .int, .int⟩] = true := by decide +kernel
example : run env roles wf src (input ++ input) = true := by decide +kernel
example : lower (input ++ input) = [(3, .str), (3, .str)] := rfl
example : run env roles wf [{associated with equations := [⟨99, 7⟩]}] input = false := by decide +kernel
example : run env roles wf [{bare with goal := ⟨goal.role, []⟩}]
    [⟨7, .lit .str, .str⟩] = false := by decide +kernel
example : run env roles wf [⟨1000000, goal, []⟩]
    [⟨1000000, .lit .str, .str⟩] = true := by decide +kernel

-- This well-typed nonliteral is outside the checker's fragment, not rejected by the language.
def nonliteral : Inference.Expr := .letE (.lit .str) (.lit .str)
example : Core.PresenceGeneration.Typing Common.model [] nonliteral
    (Core.PresenceGeneration.Comp.pure Common.model (.base .str)) := by
  apply Core.PresenceGeneration.Typing.letComputed
    (a := Core.PresenceGeneration.Comp.pure Common.model (.base .str))
    (b := Core.PresenceGeneration.Comp.pure Common.model (.base .str))
  · exact .lit ⟨Common.subtype_refl _, Common.rowLe_refl _⟩
  · exact .lit ⟨Common.subtype_refl _, Common.rowLe_refl _⟩
  · exact ⟨Common.subtype_refl _, fun _ h => h.elim id id⟩
example : run env roles wf [bare] [⟨7, nonliteral, .str⟩] = false := by decide +kernel

-- All four literal tags and every annotation pair are covered by the general theorem.
example (n : Nat) (lit ann : Inference.Base) :
    Valid [⟨n, .lit lit, ann⟩] ↔ ∃ value, BindingMeaning ⟨n, .lit lit, ann⟩ value :=
  literal_check_exact n lit ann
example : ¬ ∃ value, BindingMeaning ⟨7, .lit .int, .str⟩ value := by
  rw [← literal_check_exact]
  decide
example (b : Binding) (literal : b.value = .lit b.annotation) (value : Common.Ty) :
    BindingMeaning b value ↔ Common.Equivalent value (.base b.annotation) :=
  binding_meaning_exact b literal value
example (source : Source) (bindings : Bindings) :
    run env roles wf source bindings = true ↔ Valid bindings ∧
      CommonRoleSourceRoleObligations.ValidSource roles source ∧ Models env roles source bindings ∧
      ∀ c ∈ source, ∃ head, Derives env roles source bindings c.receiver head ∧
        CommonRoleSourceRoleObligations.Discharges env.cores (fun _ => head) c :=
  run_exact env roles wf awf source bindings
example (source : Source) (bindings : Bindings) (valid : Valid bindings)
    (name : Nat) (head : Inference.Base) :
    CommonRoleNamedSourceEntry.Derives env roles source (lower bindings) name head ↔
      Derives env roles source bindings name head := derives_exact env roles source bindings valid name head
example : Core.PresenceGeneration.Typing Common.model [] (.lit .int)
    (Core.PresenceGeneration.Comp.pure Common.model (.union (.base .int) (.base .str))) ∧
    ¬ Common.Equivalent (.union (.base .int) (.base .str)) (.base .int) :=
  literal_does_not_force_scalar
end Cycle87BoundaryCheck
#print axioms Yulang.CommonRoleAnnotatedLiteralInputs.binding_meaning_exact
#print axioms Yulang.CommonRoleAnnotatedLiteralInputs.literal_check_exact
#print axioms Yulang.CommonRoleAnnotatedLiteralInputs.literal_does_not_force_scalar
#print axioms Yulang.CommonRoleAnnotatedLiteralInputs.lower_exact
#print axioms Yulang.CommonRoleAnnotatedLiteralInputs.derives_exact
#print axioms Yulang.CommonRoleAnnotatedLiteralInputs.models_exact
#print axioms Yulang.CommonRoleAnnotatedLiteralInputs.models_bindings
#print axioms Yulang.CommonRoleAnnotatedLiteralInputs.run_exact
```
