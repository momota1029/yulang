# dots cycle 88 — let と変数を含む scalar 入力の導出

## 結果と部分目標

**明示scalar注釈を持つ既存literal・変数・let式の有限断片について、入力検査からcanonical割当てとrole readinessまでをつなぎ、元の式とsource clauseの独立判断とのiffを閉じた。**

cycle87のliteralだけの入口を、閉じたlet式・入れ子・外側変数・shadowing・捕捉した値へ拡張した。新規`CommonRoleScalarExpressionInputs`は237行、公開12定理（補助1本を含む）。ordinary atoms、State、slot/map、package、fuel、model、solver成功をcallerへ戻していない。

重要なのは、scalarタグを計算する実行版を型付けの正本にしていない点。独立な`Evaluates`を定義し、既存`Core.PresenceGeneration.Typing Common.model`の**両方のlet規則**から下界を証明した。value letで捕捉されるpolymorphic bindingも、computed letのmonomorphic bindingも扱う。逆向きには、計算したscalar以上の任意の値型で実際の型付けを構成する。明示注釈の上界と合わせた時だけscalarの等価性を得る。

これはbridge 1の入力側の部分目標。scalarタグを扱う判断であり、payloadの実行意味論、全言語の推論・主型性、一般宣言lowering、B4完成ではない。主要橋は5本のまま。

## 量化範囲と境界

- 任意の有限binding listとgrouped source、任意の既存Exprを入口で量化する。固定例のiffではない。literal/variable/let以外は計算結果noneとなる断片外であり、言語の拒否ではない。
- 各public bindingの式は空のscalar contextから検査する。let内のde Bruijn変数は既存Exprのもの。free variable、範囲外index、unsupportedな未使用RHSも成功しない。letのRHSを飛ばしていない。
- 各bindingの明示scalar注釈と計算結果の一致を検査する。注釈なし、union注釈、一般effectful式、関数やbranchなどの一般推論は範囲外。literalやletの型付けだけから上界を捏造しない。
- `infer_exact`は実行版と独立なscalar判断の健全性・完全性。`annotation_exact`は独立なsupported evaluationを前提とし、その断片の中で既存型付けと注釈にモデルが存在することを検査と結ぶ。全Exprに対する型検査の完全性ではない。
- `LowerEnv`は証明の中の関係で、実行時のcaller入力ではない。`evaluates_lower`は任意の対応する既存環境と任意のtypingを量化し、`evaluates_typed`はcanonicalな単相環境を計算して証拠を作る。
- 元bindingsの順序と重複を保存する。scope-resolvedなbinding名、grouped source、registryとwf/awfは引き続き入力。invocation identity、非linear head、where変数の意味を決めていない。
- modelのdomainは既存のsource名だけ。空sourceに無関係な同名inputの矛盾があってもtrueとなる。大域的な全binding整合性検査ではない。ただし各binding単体の不正な式/注釈はsourceに無関係でもfalse。
- 全4scalar tagの入力検査を扱うが、role receiverの既存first-order符号化はint/strのみ。bool/unitに新しいrole規則を足していない。

## 主要定理と役割

全て`CommonRoleScalarExpressionInputs`。既存Lean定義・定理は変更していない。

1. `infer_exact`: 任意scalar context・Expr・scalarについて、実行版がそのscalarを返すことと独立`Evaluates`がiff。健全性・完全性。
2. `lowerEnv_cons`: 任意のcontext対応とhead bindingの下界から、拡張環境の対応を得る。補助。
3. `evaluates_lower`: 任意`Evaluates heads e head`、任意既存環境Γ、そのLowerEnv、任意結果computationとtypingについて、scalar headが結果値型の下界となる。健全性。
4. `evaluates_typed`: 任意`Evaluates heads e head`と、head以上の任意Common値型について、計算したcanonicalEnvでpureな既存typingを構成する。完全性側の構成。
5. `annotation_exact`: 任意閉じた独立supported evaluationと任意scalar注釈について、実行版の一致と、既存typing＋注釈上界を満たす値型の存在がiff。断片内の健全性・完全性。
6. `meaning_exact`: 任意閉じた独立evaluationで得られた注釈と任意値型について、既存typing＋注釈上界とscalar等価性がiff。健全性・完全性。
7. `valid_exact`: 任意binding listで、全件実行検査と全元bindingの独立evaluationがiff。健全性・完全性。
8. `lower_exact`: 任意bindingsとValid、任意name/headで、抽出factsへの所属と元式の独立Seedがiff。健全性・完全性。
9. `derives_exact`: 任意env/roles/source/bindingsとValid、任意name/headで、抽出後の導出と元式・元clauseの独立導出がiff。健全性・完全性。
10. `models_exact`: 同じ任意入力とValidで、既存named modelの存在と元入力の独立modelの存在がiff。健全性・完全性。
11. `models_bindings`: 上記入力、任意の独立factsモデル、member binding、その名のsource-domain所属について、実際の式typingと注釈意味を得る。健全性。domain所属を落としていない。
12. `run_exact`: 任意env/roles/wf/awf/source/bindingsで、実行trueと、全元式の独立evaluation・ValidSource・独立Models・全元role clauseの独立dischargeがiff。成功仮定なしの有限断片の健全性・完全性。主型性ではない。

## 検証

最終production sourceに対して以下はexit 0。

```text
cd lean
ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake build Yulang.CommonRoleScalarExpressionInputs --wfail
✔ [297/297] Built Yulang.CommonRoleScalarExpressionInputs (1.3s)
Build completed successfully (297 jobs).
ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang88/boundary-check.lean
exit 0
```

境界検査は39 examples。入れ子let、shadowing、外側への参照、computed let、captured value let、全4scalar、注釈不一致、範囲外変数、未使用だが不正なRHS、unsupported lambda/pair/branch、より広いunionでの既存typing、兄弟逆順、重複、同名矛盾、source外だけの矛盾、不正associated member/arity、巨大な名前、空入力、一般定理の使用を検査した。元の期待値を変えていない。

12公開定理のtrust=0公理出力全文:

```text
'Yulang.CommonRoleScalarExpressionInputs.infer_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleScalarExpressionInputs.lowerEnv_cons' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleScalarExpressionInputs.evaluates_lower' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleScalarExpressionInputs.evaluates_typed' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleScalarExpressionInputs.annotation_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleScalarExpressionInputs.meaning_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleScalarExpressionInputs.valid_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleScalarExpressionInputs.lower_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleScalarExpressionInputs.derives_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleScalarExpressionInputs.models_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleScalarExpressionInputs.models_bindings' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleScalarExpressionInputs.run_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
```

```text
python3 tools/boundary-input-inventory.py --check
PASS: inventory matches source hashes, imports, and ledger mentions.
CommonRole import scope=255; Main=93; Audit=255; ledger mentioned=128. Mention counts are not audit completion counts.
bash tools/verify-lean.sh . origin/integration/m1-final --no-build
verify-lean: . @ 93e1f6bc4 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

`git diff --check`もexit 0。初回の型推論エラー（context indexのNat注釈、pure computationの明示、変数caseのhead）を修正した。build起動を一度repo rootから行いtoolchainが見つからなかったため、leanディレクトリからやり直した。scratch境界検査の型引数/constructor表記も修正して再実行した。失敗した試行をPASSと数えていない。最終focused buildはwarningなし。

ローカル全体lake build、全Audit、AxiomGate、全体verifyは指示どおり実行していない。上記gateはdiff-only。新定理の公理はpropext/Quot.sound、run_exactにClassical.choiceが加わる範囲。全言語の監査完了とは言わない。

## 公開sourceとCI

source commit: `a3f225e5b22a2aa6e2ff1b5fa0038dcf948a00d8`。

- Core CI: completed / success; https://github.com/momota1029/yulang/actions/runs/42851955707
- Lean inference kernel: completed / success; https://github.com/momota1029/yulang/actions/runs/42851955816

このexact-source SHAを指定して再取得した結果。最終report/heartbeat commitのCIと区別する。source公開後にproduction Leanは変更していない。scratch境界検査は35から39に増やして再実行した。

公開tree `81774a336c201896e16a7e9b4079e538a517d400`は2,322 entries、非truncated。全9変更pathsのblob SHAが一致し、tree全体もlocal checkpoint `2b53b3e82`と一致。API refはsource SHAを返し、明示tracking ref付きのgit fetch後にもtree差分は空だった。

## 仕様とYulang2の照合

`spec/03-expressions.md` 3.1と3.5、`spec/04-types.md` 4.2を読み、RHSからbodyへの順序と明示注釈の上界を確認した。新しいletの型付けを定めず、既存PresenceGenerationのvalue/computed両規則へ証明を接続した。effect行の固定を注釈から導いていない。

開始時にcycle87報告のYulang2照合記録を参照し、source公開後に`work/dots-audit`の`notes/audit/x-oracle.md`を直接再読した。C3-ACCEPT-01のpoly-value、C3-PARENTの両兄弟順とgeneric成功、C3-PARENT-NEGのchild欠如が関連素材。最新oracleの直接読取りは新定義の前ではなかった点を記録する。最初に誤ったhandoffパスを開いたが存在せず、auditパスで読み直した。

今回のlet/scalarタグ入口そのものをYulang2実機で新規実行してはいない。既存のoracle成功を今回の完全性証明や新実機runと数えない。Rust parserからExpr/annotationへの忠実性も未証明。新規質問ノート0件。既存の未決質問を解消していない。

## 受け入れ条件と残りの橋

I-4のsource boundaryで、非literalのうち既存let/variableを含む閉じたscalar入力断片を閉じた。I-13台帳Y節とinventoryを更新。全モジュール意味監査は未完で、過去の期限超過解消を主張しない。

B4主定理への主要橋は5本:
1. `source_boundary_adequate`: 今回の入力断片は閉じた。実宣言からgrouped clause・annotation・scope-resolved名を導く橋と一般式inferenceは残る。
2. `generated_work_closed`: 動的where childを計算source領域へ登録する橋が残る。
3. `saturate_terminates_and_closes`: 一般Paterson/K2 driverの停止と意味的閉包が残る。
4. `saturated_frontier_exact`: 独立な最終診断分類が残る。
5. `resolve_dictionary_order_sound`: readiness Boolの正しさは辞書の観察同値ではない。

次の候補は(1) grouped where注釈を失わない実宣言carrierからsource生成、(2) parserからbinding注釈とscope名を保存する具体lowering、(3) 実生成childを上記source入口へ登録すること。意味の薄い式constructor追加や名前変更だけで橋完了を数えない。

## 復旧、公開、資源、時刻

- 開始2026-11-10T15:58:17Z。live integration/workは7766d0e9。standing ordersと最新inboxのACTIVE・上限なしを読み直した。cycle87 completed heartbeat/reportあり、前writer/buildなし。既存workspaceへintegrationをmerge。clone/cacheを増やしていない。
- 初回heartbeat f2bfb450、途中heartbeat 71f79579、source checkpoint a3f225e5。途中heartbeatは16:06頃に準備し、個別blob upload中の16:09頃に先に公開。sourceは16:10頃に公開した。
- 個別blobのSHAを全件確認し、既存live treeをbaseにSHA-only treeを作り、全tree一致を確認してからwork/dots-mainだけをforce=false/expected-headで更新。外部writeの拒否・不確定結果なし。ローカルcontent読取りでPython構文とoutput truncationのエラーがあり、外部write前に小さいUTF-8 chunksへ変更した。
- source/doc8 paths、heartbeat、最終reportの合計10 paths。integrationなど他branchには書いていない。最終report/heartbeatも同じ方法で公開後照合する。
- 空きは開始時・16:11時点とも48G/63G（使用13G）。使用量の枠は不明。ログは../cache/yulang88。

報告作成時刻: 2026-11-10T16:14:52Z。経過16.6分。指定終了期限16:22:19Z。時間を埋めるための補題を足していない。

## 再実行用の境界検査全文

```lean
import Yulang.CommonRoleScalarExpressionInputs
open Yulang
open CommonRoleScalarExpressionInputs
open CommonRoleAssociatedClauseExtraction (Clause Source)
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Cycle88BoundaryCheck

def roles := Roles.AssocExamples.requiredRoles
def env := Roles.AssocExamples.singletonEnv Roles.AssocExamples.boxImpl
theorem wf : Roles.WellFormed env.cores := Roles.AssocExamples.box_paterson
theorem awf : Roles.AssocWellFormed env roles := Roles.AssocExamples.box_assoc_wellFormed
def goal : Roles.Goal := Roles.AssocExamples.index
  (Roles.AssocExamples.box (.var 0)) Roles.Examples.int
def bare : Clause := ⟨7, goal, []⟩
def associated : Clause := ⟨3, goal, [⟨0, 7⟩]⟩
def src : Source := [associated, bare]
def alias : Inference.Expr := .letE (.lit .str) (.var 0)
def shadow : Inference.Expr := .letE (.lit .int) (.letE (.lit .str) (.var 0))
def outer : Inference.Expr := .letE (.lit .str) (.letE (.lit .int) (.var 1))
def computed : Inference.Expr := .letE alias (.var 0)
def input : Bindings := [⟨3, outer, .str⟩]

example : infer [] alias = some .str := rfl
example : infer [] shadow = some .str := rfl
example : infer [] outer = some .str := rfl
example : infer [] computed = some .str := rfl
example : infer [] (.letE (.lit .int) (.var 1)) = none := rfl
example : infer [] (.letE (.var 0) (.lit .str)) = none := rfl
example : infer [] (.letE (.lam (.var 0)) (.lit .str)) = none := rfl
example : infer [] (.var 0) = none := rfl
example : infer [.int, .str] (.var 1) = some .str := rfl
example : infer [] (.lit .bool) = some .bool := rfl
example : infer [] (.lit .unit) = some .unit := rfl
example : infer [] (.pair (.lit .int) (.lit .str)) = none := rfl
example : infer [] (.branch (.lit .bool) (.lit .str) (.lit .str)) = none := rfl
example : Valid input := by decide
example : ¬ Valid [⟨3, alias, .int⟩] := by decide
example : Evaluates [] computed .str := (infer_exact _ _ _).mp rfl
example : Meaning computed .str (.base .str) :=
  (meaning_exact ((infer_exact _ _ _).mp rfl) _).mpr (Common.equivalent_refl _)
example : Core.PresenceGeneration.Typing Common.model [] alias
    (Core.PresenceGeneration.Comp.pure Common.model (.union (.base .str) (.base .int))) :=
  evaluates_typed ((infer_exact [] alias .str).mp rfl) _ (CommonBoundCoalescing.le_union_left _ _)
example : ¬ ∃ value, Meaning alias .int value := by
  rw [← annotation_exact ((infer_exact [] alias .str).mp rfl)]
  decide
example : run env roles wf src input = true := by decide +kernel
example : run env roles wf [bare, associated] input = true := by decide +kernel
example : run env roles wf src [] = false := by decide +kernel
example : run env roles wf src [⟨3, alias, .int⟩] = false := by decide +kernel
example : run env roles wf [bare] [⟨7, computed, .str⟩] = true := by decide +kernel
example : run env roles wf [bare] [⟨17, computed, .str⟩] = false := by decide +kernel
example : run env roles wf [bare] [⟨7, .lit .bool, .bool⟩] = false := by decide +kernel
example : run env roles wf [] [⟨7, .var 0, .str⟩] = false := by decide +kernel
example : run env roles wf [] [] = true := by decide +kernel
example : run env roles wf [bare] [⟨7, alias, .str⟩, ⟨7, .lit .int, .int⟩] = false := by decide +kernel
example : run env roles wf [] [⟨7, alias, .str⟩, ⟨7, .lit .int, .int⟩] = true := by decide +kernel
example : run env roles wf src (input ++ input) = true := by decide +kernel
example : run env roles wf [{associated with equations := [⟨99, 7⟩]}] input = false := by decide +kernel
example : run env roles wf [{bare with goal := ⟨goal.role, []⟩}]
    [⟨7, alias, .str⟩] = false := by decide +kernel
example : run env roles wf [⟨1000000, goal, []⟩]
    [⟨1000000, computed, .str⟩] = true := by decide +kernel
example (source : Source) (bindings : Bindings) :
    run env roles wf source bindings = true ↔
      (∀ b ∈ bindings, Evaluates [] b.value b.annotation) ∧
      CommonRoleSourceRoleObligations.ValidSource roles source ∧ Models env roles source bindings ∧
      ∀ c ∈ source, ∃ head, Derives env roles source bindings c.receiver head ∧
        CommonRoleSourceRoleObligations.Discharges env.cores (fun _ => head) c :=
  run_exact env roles wf awf source bindings

-- A let-bound variable is itself a value and captures the prior environment.
def captured : Inference.Expr := .letE (.lit .str) (.letE (.var 0) (.var 0))
example : infer [] captured = some .str := rfl
example : run env roles wf [bare] [⟨7, captured, .str⟩] = true := by decide +kernel
example : Core.PresenceGeneration.Typing Common.model [] alias
    (Core.PresenceGeneration.Comp.pure Common.model (.base .str)) := by
  apply Core.PresenceGeneration.Typing.letValue (by rfl)
    (a := (.base .str : Common.Ty))
  · exact .lit ⟨Common.subtype_refl _, Common.rowLe_refl _⟩
  · apply Core.PresenceGeneration.Typing.var (by rfl)
    exact .poly (.lit ⟨Common.subtype_refl _, Common.rowLe_refl _⟩) (Common.rowLe_refl _)
example (name : Nat) (literal annotation : Inference.Base) :
    Valid [⟨name, .lit literal, annotation⟩] ↔ literal = annotation := by
  simp [Valid, infer]
end Cycle88BoundaryCheck

-- Cycle88: independently checked scalar expression inputs.
#print axioms Yulang.CommonRoleScalarExpressionInputs.infer_exact
#print axioms Yulang.CommonRoleScalarExpressionInputs.lowerEnv_cons
#print axioms Yulang.CommonRoleScalarExpressionInputs.evaluates_lower
#print axioms Yulang.CommonRoleScalarExpressionInputs.evaluates_typed
#print axioms Yulang.CommonRoleScalarExpressionInputs.annotation_exact
#print axioms Yulang.CommonRoleScalarExpressionInputs.meaning_exact
#print axioms Yulang.CommonRoleScalarExpressionInputs.valid_exact
#print axioms Yulang.CommonRoleScalarExpressionInputs.lower_exact
#print axioms Yulang.CommonRoleScalarExpressionInputs.derives_exact
#print axioms Yulang.CommonRoleScalarExpressionInputs.models_exact
#print axioms Yulang.CommonRoleScalarExpressionInputs.models_bindings
#print axioms Yulang.CommonRoleScalarExpressionInputs.run_exact
```
