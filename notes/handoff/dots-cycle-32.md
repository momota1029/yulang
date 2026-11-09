# Yulang Lean cycle32

通知07:27:19Z、実着手2026-11-09T07:33:58Z。起動遅延約6分39秒。最新integration/m1-final@7bee986b7とstanding orders/inboxを再取得。ACTIVE・上限なし、前回31 completedと報告を確認。統合版をmergeして同じ作業場を使用。開始心拍07:34:47Zを公開。

## 部分目標と結果
実ordinary atomsの有向変数辺に沿う上下scalar bound伝播を、有限停止・独立導出exactness・全モデル保存と既存materializerへ接続する。**この部分目標は達成**。8*n個の上下別factの有限宇宙を使い、上界は逆向き、下界は順向きに伝播。初期にscalar等式ペアが無くても上下を異なる経路から集める。

任意n/state/factについて飽和所属 iff 独立seed/transfer導出、任意assignmentについて正規化前後の全モデルiff。任意の入力モデルを明示前提に、int観測 iff 上下int導出、任意registry/root/tableの全順序付き診断treeの再正規化固定点も示す。整合性を証明せず仮定していることに注意。

## 定理34件
以下は全定理の型。暗黙のn、state、side、slot、baseも全称量化。健全性/完全性は独立の有向scalar導出に関してであり、任意意味的含意ではない。主型性は未証明。capacity/stopped/least/fixedpointは停止・閉包補助、grammar/列挙は補助。Checksは固定例で一般定理の回帰。

- facts_complete/facts_length: 全factが列挙され、長さ8*n。
- seedTest_exact/edge_exact: 実検査と元atom所属の同値。
- saturate_capacity/seed/transfer/rules_derived/exact/stopped/least: 内部容量、seed包含、辺伝播閉包、導出保存、独立導出とのiff、停止、任意seedを含み伝播閉な述語への最小性。
- derived_models: 任意導出factは任意入力モデルで成立。
- atom_in_equality/bounds_grammar/atom_injective: 出力atomの既存文法適合とfact符号化の単射性。
- normalize_models/bound/evidence/linked/derived: 全モデル保存、boundと導出のiff、等式Evidenceと上下導出のiff、元変数辺の不変性、再正規化導出の同値。
- saturate_fixedpoint/materializes_int: 再飽和所属不変、上下int導出と入力モデルから既存materializerがintを返す。
- Diagnosticのmaterialize_exact/endpoint_derived/endpoint_fixedpoint/candidate_fixedpoint/tree_fixedpoint/tree_derived: 入力モデルの下で上下int導出と観測のiff、二stateの上下int導出ペア同値から任意endpointの同値、再正規化に対するendpoint/candidate/全treeの固定点、さらに同じ所属を持つ二表の全tree等式。
- Checkのold_empty/upper_middle/lower_middle/middle_forced/consistent/middle_materialized: `int≤x≤y≤z≤int`で旧reciprocalエンジンの出力は空、新導出でyの上下を得て、任意モデルのyはint、実際に全intモデルが存在し、新normalize後はyをintと観測。

### CommonRoleDirectedBounds
```lean
theorem facts_complete (f : Fact n) : f ∈ facts n

theorem facts_length (n : Nat) : (facts n).length = n * 8

theorem seedTest_exact (s : State n) (f : Fact n) :
    seedTest s f = true ↔ atom f ∈ s.atoms

theorem edge_exact (s : State n) (side : Bool) (i j : Fin n) :
    edge s side i j = true ↔ Linked s side i j

theorem saturate_capacity (s : State n) : (saturate s).length ≤ n * 8

theorem saturate_seed (s : State n) (h : atom f ∈ s.atoms) : f ∈ saturate s

theorem saturate_transfer (s : State n) (h : Linked s side i j)
    (present : (side,j,b) ∈ saturate s) : (side,i,b) ∈ saturate s

theorem rules_derived (s : State n) :
    ∀ rule ∈ rules s, FiniteHorn.Valid (Derived s) rule

theorem saturate_exact (s : State n) (f : Fact n) :
    f ∈ saturate s ↔ Derived s f

theorem saturate_stopped (s : State n) :
    FiniteHorn.firstFresh (rules s) (saturate s) (facts n) = none

theorem derived_models (s : State n) (f : Fact n) (h : Derived s f)
    (a : Fin n → Comp Common.model) (models : All Common.model a s.atoms) :
    Atom.Holds Common.model a (atom f)

theorem saturate_least (s : State n) (P : Fact n → Prop)
    (seed : ∀ f, atom f ∈ s.atoms → P f)
    (transfer : ∀ side i j b, Linked s side i j → P (side,j,b) → P (side,i,b)) :
    ∀ f ∈ saturate s, P f

theorem atom_in_equality (f : Fact n) : atom f ∈
    CommonRoleCandidateStateFrontier.equality f.2.1 f.2.2

theorem bounds_grammar (fs : List (Fact n)) :
    PresenceGeneratedChildGrammar.GoodAtoms (fs.map atom) ∧
    PresenceGeneratedWidth.WidthAtoms (fs.map atom) ∧
    PresenceSourceConstraintSupport.GoodAtoms (fs.map atom)

theorem normalize_models (s : State n) (a : Fin n → Comp Common.model) :
    All Common.model a (normalize s).atoms ↔ All Common.model a s.atoms

theorem atom_injective : Function.Injective (atom : Fact n → Atom (Fin n))

theorem normalize_bound (s : State n) (f : Fact n) :
    atom f ∈ (normalize s).atoms ↔ Derived s f

theorem normalize_evidence (s : State n) (i : Fin n) (b : Inference.Base) :
    CommonRoleOrdinaryKnownness.Evidence (normalize s).atoms i b ↔
      Derived s (true,i,b) ∧ Derived s (false,i,b)

theorem normalize_linked (s : State n) (side : Bool) (i j : Fin n) :
    Linked (normalize s) side i j ↔ Linked s side i j

theorem normalize_derived (s : State n) (f : Fact n) :
    Derived (normalize s) f ↔ Derived s f

theorem saturate_fixedpoint (s : State n) (f : Fact n) :
    f ∈ saturate (normalize s) ↔ f ∈ saturate s

theorem materializes_int (s : State n) (i : Fin n)
    (hu : Derived s (true,i,.int)) (hl : Derived s (false,i,.int))
    (a : Fin n → Comp Common.model) (models : All Common.model a s.atoms) :
    CommonRoleOrdinaryKnownness.materialize (normalize s).atoms i = some Roles.Examples.int

```
### CommonRoleDirectedDiagnostic
```lean
theorem materialize_exact (s : State n) (i : Fin n)
    (a : Fin n → Comp Common.model) (models : All Common.model a s.atoms) :
    materialize (normalize s).atoms i = some Roles.Examples.int ↔ (Derived s (true,i,.int) ∧ Derived s (false,i,.int))

theorem endpoint_derived (s t : State n)
    (same : ∀ i, (Derived s (true,i,.int) ∧ Derived s (false,i,.int)) ↔ (Derived t (true,i,.int) ∧ Derived t (false,i,.int)))
    (a b : Fin n → Comp Common.model)
    (hs : All Common.model a s.atoms) (ht : All Common.model b t.atoms)
    (e : Endpoint n) : e.eval (normalize s) = e.eval (normalize t)

theorem endpoint_fixedpoint (s : State n) (a : Fin n → Comp Common.model)
    (hs : All Common.model a s.atoms) (e : Endpoint n) :
    e.eval (normalize (normalize s)) = e.eval (normalize s)

theorem candidate_fixedpoint (s : State n) (a : Fin n → Comp Common.model)
    (hs : All Common.model a s.atoms) (p : SourceRequest n) (d : Declaration) :
    Candidate (normalize (normalize s)) p d ↔ Candidate (normalize s) p d

theorem tree_fixedpoint (registry : Registry) (root : SourceRequest n)
    (table : CommonRoleGlobalChoices.Table registry root)
    (s : State n) (a : Fin n → Comp Common.model) (hs : All Common.model a s.atoms) :
    CommonRoleDiagnosticTree.diagnose registry root table (normalize (normalize s)) =
      CommonRoleDiagnosticTree.diagnose registry root table (normalize s)

theorem tree_derived (registry : Registry) (root : SourceRequest n)
    (left right : CommonRoleGlobalChoices.Table registry root)
    (tables : ∀ p, p ∈ left ↔ p ∈ right)
    (s t : State n) (same : ∀ i, (Derived s (true,i,.int) ∧ Derived s (false,i,.int)) ↔ (Derived t (true,i,.int) ∧ Derived t (false,i,.int)))
    (a b : Fin n → Comp Common.model)
    (hs : All Common.model a s.atoms) (ht : All Common.model b t.atoms) :
    CommonRoleDiagnosticTree.diagnose registry root left (normalize s) =
      CommonRoleDiagnosticTree.diagnose registry root right (normalize t)

```
### CommonRoleDirectedBoundsCheck
```lean
theorem old_empty : CommonRoleEvidenceSaturation.saturate sandwich = []

theorem upper_middle : Derived sandwich (true,1,.int)

theorem lower_middle : Derived sandwich (false,1,.int)

theorem middle_forced (a : Fin 3 → Comp Common.model)
    (models : All Common.model a sandwich.atoms) :
    Common.Equivalent (a 1).1 (.base .int)

theorem consistent : All Common.model
    (fun (_ : Fin 3) => Comp.pure Common.model (.base .int)) sandwich.atoms

theorem middle_materialized :
    CommonRoleOrdinaryKnownness.materialize (normalize sandwich).atoms 1 = some Roles.Examples.int

```

## B4と限界
主要5橋（source boundary、generated work、飽和停止/閉包、独立最終分類、辞書健全性/観察同値）は依然未完。今回は橋1/3内部のscalar断片。一般意味的含意、構造型、状態依存receiver/annotation生成、role feedback停止、解の存在・主型性・X13〜16外側PROVEDは未達。新normalizeを自己出力探索へ差替えたexactnessは今回未証明。固定点はfact所属と診断観測についてで、atomリスト構造等式でもrole生成の固定点でもない。endpointは既存のint-only、registry/source/tableは入力。
次: (1)有向normalizeを自己出力探索へ接続 (2)状態依存receiver生成 (3)role再生成を含む有限進捗尺度。意味論判断なし、質問ノートなし。

## Yulang2との照合
既存取得済みnotes/audit/y2-claims-role-boundaries-cycle-2.mdのROLE-MORE-001〜008を再読。最新audit再取得と新実機照合は未実行。この伝播はCommon部分型の推移律であり、新しいrole選択規則を決めていない。

## 検証
ELAN_HOME=/workspace/scratch/1d0b4aaa3394/dots-probe-elan、PATH設定。
`cd lean && lake build --wfail Yulang.CommonRoleDirectedBoundsCheck`: exit0、312 jobs。
`lake env lean --trust=0 /tmp/cycle32-audit.lean`: exit0、34定理、標準三公理のみ。
全体build・全Audit・verify-lean.shは常設指示どおり未実行。全体PASSではない。読取りレビュー問題なし、独立buildではない。空き開始19GB。使用量枠不明。

### 最終検証出力全文
~~~text
Build completed successfully (312 jobs).
'Yulang.CommonRoleDirectedBounds.facts_complete' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDirectedBounds.facts_length' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDirectedBounds.seedTest_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDirectedBounds.edge_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDirectedBounds.saturate_capacity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDirectedBounds.saturate_seed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDirectedBounds.saturate_transfer' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDirectedBounds.rules_derived' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDirectedBounds.saturate_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDirectedBounds.saturate_stopped' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDirectedBounds.derived_models' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDirectedBounds.saturate_least' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDirectedBounds.atom_in_equality' depends on axioms: [propext]
'Yulang.CommonRoleDirectedBounds.bounds_grammar' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDirectedBounds.normalize_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDirectedBounds.atom_injective' depends on axioms: [propext]
'Yulang.CommonRoleDirectedBounds.normalize_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDirectedBounds.normalize_evidence' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDirectedBounds.normalize_linked' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDirectedBounds.normalize_derived' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDirectedBounds.saturate_fixedpoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDirectedBounds.materializes_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDirectedDiagnostic.materialize_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDirectedDiagnostic.endpoint_derived' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDirectedDiagnostic.endpoint_fixedpoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDirectedDiagnostic.candidate_fixedpoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDirectedDiagnostic.tree_fixedpoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDirectedDiagnostic.tree_derived' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDirectedBoundsCheck.old_empty' depends on axioms: [propext]
'Yulang.CommonRoleDirectedBoundsCheck.upper_middle' depends on axioms: [propext]
'Yulang.CommonRoleDirectedBoundsCheck.lower_middle' depends on axioms: [propext]
'Yulang.CommonRoleDirectedBoundsCheck.middle_forced' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDirectedBoundsCheck.consistent' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDirectedBoundsCheck.middle_materialized' depends on axioms: [propext, Classical.choice, Quot.sound]
~~~

## 制限と公開
公開準備のexec transportが切断した。同じ環境へ再attachしてファイル保持を確認。read-onlyへ変わったため報告追記・local commitはsandbox審査を通す。Lean検証結果は切断前の完成版。全10変更ファイルを個別blob後、小さなSHA treeと非force expected-headでwork/dots-mainへ一括公開し、remote全treeを照合する。
