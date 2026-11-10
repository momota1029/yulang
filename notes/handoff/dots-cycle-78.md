# dots cycle 78 — 構造的な associated template の生成と公開復旧

## 結果

**有限 named associated program の任意 template 関数を、検査済みの first-order goal 構文から生成する部分目標を閉じた。**
新しい `CommonRoleStructuralAssociatedTemplates`（260行）は、独立な構造置換判断 `Fill/Fills` と
`Materializes` を持つ。元の source 名上の独立導出、返却 state の scalar Evidence、
全 ordinary model、実 ordinary solver の受理まで iff で接続した。

[復旧公開 ac2cbd47](https://github.com/momota1029/yulang/commit/ac2cbd479a8901f9614856533eac8a05cc1680ac)
の tree `201a842855caaabb12fb21ba207747f7f80951b0` は、検証済み local `87e0cc2a3` の tree と完全一致する。
再取得した recursive tree の 2290 entries と全変更9 pathの blob SHA を照合した。
本報告と crash 記録は後続の記録公開で、Lean sourceを変更しない。

B4 全体、動的 where、一般区間 knownness、四方向の分類、辞書順、全言語の主型性は未完。
B4 の主要橋は5本のまま。新しい言語意味の採用0、既存定理の変更0、新規質問0。

## 量化範囲、前提、定理の側

入力は任意の有限 `Program`、旧 ordinary state、core/associated registry。
各行は scope 解決済み receiver/output 名、関連名、`Template` を持つ。
`Template` は任意 role と有限引数列からなり、自由変数は0だけ。
構築子は任意の有限入れ子で、placeholder は0回以上現れてよい。
`check` が scope 証拠を計算し、生成関数は構造置換と既存 int/str encoding だけを使う。

- `fill_exact`, `fills_exact`（健全性・完全性）: 任意 payload、scope 内の term/list、結果について、独立 Fill/Fills iff 既存構造置換。
- `fill_ground`, `fills_ground`（補助）: 任意 ground payload を代入した term/list は閉じる。
- `check_accepts`, `checked_goal`（補助）: 任意 goal の受理 iff scope 条件。受理した template の goal は元 goal と等しい。
- `encode_ground`（補助）: 任意 head/payload について既存 encoding が成功すれば payload は閉じる。
- `materializes_exact`（健全性・完全性）: 任意 template/head/goal について、独立 Materializes iff 生成 goal の閉性 guard と生成結果の一致。
- `materializes_shape`（補助）: 任意 materialization は role と引数個数を保つ。
- `materializes_payload`（補助）: placeholder が使われる任意 template の materialization から、その位置に入った実際の encoded payload を既存 matcher で回収する。
- `step_exact`（健全性・完全性）: 任意 registry/行/head/result について、compiled Associated iff 構造 Materializes と独立 Resolves/AssocDerives による Step。
- `derives_exact`（健全性・完全性）: 任意 registry/有限 program/旧 state/名前/head の compiled NamedDerives iff 独立 Derives。ここまでは registry well-formedness 不要。
- `run_evidence_exact`（健全性・完全性）: 任意 env/roles と明示 core wf/associated awf、任意 program/state/slot/head に対して、返却 Evidence iff 対応 source 名の独立 Derives。
- `run_source_exact`（健全性・完全性）: 同じ入力と全 assignment v について、返却 model iff 元 state の model、source valuation への factorization、全独立 Derives の scalar 等式。
- `solver_source_exact`（健全性・完全性の solver 接続）: 同じ wf/awf と任意 program/state で、実 solver の consistent=true iff 上記を満たす assignment と source valuation が存在する。

成功、完成 frontier、source valuation、外部燃料は実行の前提ではない。
bool/unit は既存 encoding に無いので、この断片内で guard が止める。
これを言語全体の拒否規則としない。定数 skeleton と空 program も扱う。

## 設計、I-13、残る境界

保持した設計は `notes/design/2026-11-10-cycle78-structural-associated-templates.md`。
入力台帳 O 節へ新規入力と全15定理の依存を記録した。
任意関数 template はこの断片では構文から導けたが、実 parser から有限 occurrence list を
網羅的に生成すること、scope 名の正しさ、role 可視性と宣言 arity 検査、registry の
well-formedness 生成、一般 interval receiver、動的 where は外側に残る。
Q1/Q2 と cycle23/24 の既存質問を選ばず維持した。

inventory は CommonRole 245、Main 到達93、Audit 到達245、台帳言及118。
**言及数は全入力監査済み数ではない。I-13 は部分達成で、cycle72 の期限超過も残る。**

## 検証

元 cycle と復旧時の双方で focused build と scratch 境界検査が exit 0。
復旧時に実行したコマンド:

```text
cd lean
ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake build --wfail Yulang.CommonRoleStructuralAssociatedTemplates
Build completed successfully (287 jobs).
exit 0

ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang78/boundary-check.lean
exit 0
```

scratch は21 example と5 named theorem（既存 wf/awf の2 alias、unsupported、propagated、no_seed）。
単に26個の独立境界例とは数えない。検査対象は scope 外変数の拒否、nested/repeated placeholder、
int/str の構造生成、role/arity 保存、unsupported bool/unit、定数 goal からの不正 seed 防止、
共有名7を経由する2行の実飽和、空 seed、循環、空 program。
新規15定理の公理出力全文:

```text
'Yulang.CommonRoleStructuralAssociatedTemplates.fill_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralAssociatedTemplates.fills_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralAssociatedTemplates.fill_ground' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralAssociatedTemplates.fills_ground' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralAssociatedTemplates.check_accepts' depends on axioms: [propext]
'Yulang.CommonRoleStructuralAssociatedTemplates.checked_goal' does not depend on any axioms
'Yulang.CommonRoleStructuralAssociatedTemplates.encode_ground' depends on axioms: [propext]
'Yulang.CommonRoleStructuralAssociatedTemplates.materializes_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralAssociatedTemplates.materializes_shape' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralAssociatedTemplates.materializes_payload' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralAssociatedTemplates.step_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralAssociatedTemplates.derives_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralAssociatedTemplates.run_evidence_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleStructuralAssociatedTemplates.run_source_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleStructuralAssociatedTemplates.solver_source_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`python tools/boundary-input-inventory.py --check` は exit 0。
`git diff --check` と staged diff check は exit 0。
`bash tools/verify-lean.sh . origin/integration/m1-final --no-build` の全文（exit 0）:

```text
verify-lean: . @ 8fecaaa2a (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

全体 lake build、全 Audit/AxiomGate、build 付き verify-lean は指示どおり未実行。
source commit ac2cbd47 の Actions API は11:02 UTCごろの最初の照会で0 run。
これは CI 成功ではない。後続の CI 状態は公開後に別途確認する。

## Yulang2 との照合

復旧時に live `work/dots-audit`（55574b6052ef1534fd0fc36d6d3617ebede59a0e）の
`notes/audit/x-oracle.md` を読み直した。C3-PARENT の左右両順/generic function の
(11,22)、missing-child の拒否を spec6.3 の関連型と子義務の素材として参照する。
X13〜X16 は局所区間結果であり、今回の内部 structural template の直接 oracle ではない。
新しい Yulang2 実機実行、parser 実行、source-to-template adequacy 検査はしていない。
復旧では新しい証明や意味論は追加せず、保持されたソースを再検査した。

## 中断、復旧、公開、資源

- 元開始10:27:19 UTC、期限10:52:19 UTC。期限と10/20分心拍、20分成果公開を逸した。
- 最後の公開は startup 8f8f403c（API commit 時刻10:28:05）。その heartbeat の updated は
  10:29:08 で commit 時刻より先だった。復旧では UTC date から正確な時刻を生成した。
- 10:57の検査で元 writer は active だったので、一切書き込まず親へ通知。
  親がその writer を中断した後、10:57:34 UTCに復旧開始。
- 最初に live API ref/tree を読み、9変更 path のいずれも未公開、報告なしと確定した。
  clean local 8fecaaa2a、全 source/design/log は残っていた。失われた source は見つからない。
  中断の具体的な原因は不明。
- git fetch の cached tracking ref は cycle76 に留まったため、live API を正本にした。
  live integration ff5d5783 と startup heartbeat から base tree を再構成し、
  2bf19612b79338fadc52a8dc8028c54ec6844a7e と完全一致を確認。未変更 path を保全した。
- 8 source/notes blob の全 SHA を local と照合し、recovery heartbeat と合わせた9 pathを
  一つの tree/commit にまとめた。最初の ref update は接続切断で結果不明となった。
  live ref が旧8f8f403cのままと確認してから同じ expected-head/non-force 操作を1回再試行。
  success と live ac2cbd47 を確認し、tree/全9 blob を再取得して local と一致を確認した。
- 書き込み先は work/dots-main のみ。integration/main 等は変更していない。
- cache と一つの作業場を再利用し、削除、reset、履歴書き換え、worktree/cache 複製なし。
  復旧開始・source公開時の空きは48G（全63G、使用13G）。使用量枠は不明。
- 復旧は通常の cycle79 の証明作業と区別する。cycle79 はこの復旧の final 公開前には始めない。

## 残る B4 橋と次候補

主要橋は `source_boundary_adequate`、`generated_work_closed`、
`saturate_terminates_and_closes`、`saturated_frontier_exact`、
`resolve_dictionary_order_sound` の5本。
今回閉じたのは橋1内部の checked structural materialization と独立 source model の接続。

1. scope 解決済みの where/associated 構文から有限 Program を生成し、occurrence の出自と網羅性を示す。
2. role/name/宣言 arity/registry 可視性の検査を生成入口へ接続する。未決の invocation 同一性と非線形 head は先に決めない。
3. I-13 の未記載 module の入力監査を進め、言及数と全量監査を区別する。

## 再現用境界検査

```lean
import Yulang.CommonRoleStructuralAssociatedTemplates
open Yulang
open CommonRoleStructuralAssociatedTemplates
open CommonRoleSettledConstraints (State)
namespace Cycle78BoundaryCheck

def env := Roles.AssocExamples.singletonEnv Roles.AssocExamples.boxImpl
def roles := Roles.AssocExamples.requiredRoles
theorem wf : Roles.WellFormed env.cores := Roles.AssocExamples.box_paterson
theorem awf : Roles.AssocWellFormed env roles := Roles.AssocExamples.box_assoc_wellFormed

def goal : Roles.Goal := Roles.AssocExamples.index
  (Roles.AssocExamples.box (.var 0)) Roles.Examples.int

def template : Template := ⟨goal, by decide⟩
def program : Program := [⟨3, 7, 0, template⟩, ⟨7, 9, 0, template⟩]
def first : Fin (compile program).length := ⟨0, by decide⟩
def second : Fin (compile program).length := ⟨1, by decide⟩
def receiver := CommonRoleNamedAssociatedSourceModels.receiver (compile program) first
def output := CommonRoleNamedAssociatedSourceModels.output (compile program) second
def initial : State (table program).length :=
  CommonRoleCandidateStateFrontier.extend State.empty receiver .str

example : (check goal).isSome = true := by decide +kernel
example : (check ⟨0, [.var 1]⟩).isSome = false := by decide +kernel
example : (check ⟨0, [.app 20 [.var 0, .var 1]]⟩).isSome = false := by decide +kernel
example : generate template .str = Roles.AssocExamples.index
    (Roles.AssocExamples.box Roles.Examples.str) Roles.Examples.int := by decide +kernel
example : generate template .int = Roles.AssocExamples.index
    (Roles.AssocExamples.box Roles.Examples.int) Roles.Examples.int := by decide +kernel
example : Materializes template .str (generate template .str) :=
  (materializes_exact _ _ _).mpr ⟨by decide, rfl⟩
example : (generate template .str).role = goal.role ∧
    (generate template .str).args.length = goal.args.length :=
  materializes_shape _ _ _ ((materializes_exact _ _ _).mpr ⟨by decide, rfl⟩)
example : Roles.matchingSubst goal.args (generate template .str).args 0 = Roles.Examples.str :=
  by decide +kernel

-- Arbitrary nested application skeletons preserve repeated receiver occurrences.
def nested : Template := ⟨⟨23, [.app 8 [.var 0, .app 9 [.var 0]], .app 7 []]⟩, by decide⟩
example : generate nested .str =
    ⟨23, [.app 8 [.app 1 [], .app 9 [.app 1 []]], .app 7 []]⟩ := by decide +kernel
example : Materializes nested .str (generate nested .str) :=
  (materializes_exact _ _ _).mpr ⟨by decide, rfl⟩

-- Unsupported scalar inputs cannot resolve through even constant goal syntax.
theorem unsupported (t : Template) (head : Inference.Base)
    (blocked : CommonRoleOrdinaryKnownness.encode head = none) (g : Roles.Goal) :
    ¬ Materializes t head g := by
  rintro ⟨payload, encoded, _⟩
  rw [blocked] at encoded
  contradiction
example (g : Roles.Goal) : ¬ Materializes template .bool g := unsupported _ _ rfl _
example (g : Roles.Goal) : ¬ Materializes template .unit g := unsupported _ _ rfl _
def constant : Template := ⟨⟨5, []⟩, by decide⟩
example (g : Roles.Goal) : ¬ Materializes constant .bool g := unsupported _ _ rfl _
example : Roles.argsBound (generate constant .bool).args = 1 := rfl

example : table program = [3, 7, 7, 9] := by decide +kernel
example : (compile program).length = 2 := rfl

-- Actual finite saturation traverses both generated templates and shared name 7.
theorem propagated : CommonRoleOrdinaryKnownness.Evidence
    (run env roles wf program initial).atoms output .str := by
  apply (CommonRoleFiniteAssociatedStable.run_evidence env roles wf
    (CommonRoleNamedAssociatedSourceModels.source (compile program))
    (CommonRoleNamedAssociatedSourceModels.prepared (compile program) initial) output .str).mpr
  apply (CommonRoleFiniteAssociatedClosure.saturate_exact env roles wf _ _ (output, .str)).mp
  decide +kernel
example : Derives env roles program initial 9 .str :=
  (run_evidence_exact env roles wf awf program initial output .str).mp propagated

-- Empty seeds do not create facts, including cyclic programs and constant goals.
theorem no_seed (e : Roles.AssocEnv) (r : Roles.RoleDecls) (p : Program)
    (name : Nat) (head : Inference.Base) : ¬ Derives e r p State.empty name head := by
  intro h
  induction h with
  | initial seed =>
    obtain ⟨_, _, evidence⟩ := seed
    simp [CommonRoleOrdinaryKnownness.Evidence, State.empty] at evidence
  | associated _ _ _ _ ih => exact ih
example : ¬ Derives env roles program State.empty 9 .str := no_seed _ _ _ _ _
example : ¬ Derives env roles [⟨3, 3, 0, constant⟩] State.empty 3 .str := no_seed _ _ _ _ _
example : table ([] : Program) = [] := rfl
example : (run env roles wf [] State.empty).atoms = [] := by decide +kernel
end Cycle78BoundaryCheck
#print axioms Yulang.CommonRoleStructuralAssociatedTemplates.fill_exact
#print axioms Yulang.CommonRoleStructuralAssociatedTemplates.fills_exact
#print axioms Yulang.CommonRoleStructuralAssociatedTemplates.fill_ground
#print axioms Yulang.CommonRoleStructuralAssociatedTemplates.fills_ground
#print axioms Yulang.CommonRoleStructuralAssociatedTemplates.check_accepts
#print axioms Yulang.CommonRoleStructuralAssociatedTemplates.checked_goal
#print axioms Yulang.CommonRoleStructuralAssociatedTemplates.encode_ground
#print axioms Yulang.CommonRoleStructuralAssociatedTemplates.materializes_exact
#print axioms Yulang.CommonRoleStructuralAssociatedTemplates.materializes_shape
#print axioms Yulang.CommonRoleStructuralAssociatedTemplates.materializes_payload
#print axioms Yulang.CommonRoleStructuralAssociatedTemplates.step_exact
#print axioms Yulang.CommonRoleStructuralAssociatedTemplates.derives_exact
#print axioms Yulang.CommonRoleStructuralAssociatedTemplates.run_evidence_exact
#print axioms Yulang.CommonRoleStructuralAssociatedTemplates.run_source_exact
#print axioms Yulang.CommonRoleStructuralAssociatedTemplates.solver_source_exact
```

記録準備: 2026-11-10T11:03:40Z。元開始から 36.4 分、復旧開始から 6.1 分。元期限内の完了とは扱わない。
