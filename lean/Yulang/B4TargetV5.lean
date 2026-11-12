import Yulang.B4TargetV3Functionality

/-!
# I-25: initial-state scoped B4 target
草稿の Σ = journal が空の初期状態。The abstract Initial predicate is
instantiated by empty-journal InitialSource at the concrete boundary.
The five conclusions and all other quantifiers are retained from V3.
No success, model, fuel or reachability proof is required by the executor.
-/
namespace Yulang.B4TargetV5
open CommonRoleOutermostResolver
open B4Target (Vocabulary Steps)
open B4TargetV3 (Executor Local Classify SameDiagnostic RejectReason)
universe u
variable {v : Vocabulary.{u}}

structure SourceBoundary (v : Vocabulary) extends B4Target.SourceBoundary v where
  Initial : v.Registry → v.Demand → v.State → Prop

instance : Coe (SourceBoundary v) (B4Target.SourceBoundary v) := ⟨SourceBoundary.toSourceBoundary⟩

/-- Reachability uses the actual Step relation for this saturation root. -/
def Reachable (b : SourceBoundary v) (r : v.Registry) (root : v.Demand) (s : v.State) : Prop :=
  ∃ initial, b.Initial r root initial ∧ Steps (b.Step r root) initial s

theorem reachable_initial (b : SourceBoundary v) (h : b.Initial r d s) : Reachable b r d s :=
  ⟨s, h, .refl⟩

theorem reachable_step (b : SourceBoundary v) (h : Reachable b r d s)
    (step : b.Step r d s t) : Reachable b r d t := by
  obtain ⟨initial, hi, trace⟩ := h
  exact ⟨initial, hi, .tail trace step⟩

theorem reachable_steps (b : SourceBoundary v) (h : Reachable b r d s)
    (trace : Steps (b.Step r d) s t) : Reachable b r d t := by
  induction trace with
  | refl => exact h
  | tail _ step ih => exact reachable_step b ih step

/-- (1)停止・存在・安定閉包・モデル減少。全checked registry、全初期state、全需要に対し、
実進行stepのAcc、返値への有限実到達、rootと全生成需要の安定、全modelの包含を要求。
Paterson/K2からこれを示す必要があり、任意のrankを前提に追加していない。 -/
def SaturationTotal (b : SourceBoundary v) (e : Executor v) : Prop :=
  ∀ (r : v.Registry), b.Checked r → ∀ (s : v.State) (d : v.Demand), b.Initial r d s →
    Acc (fun next current => b.Step r d current next) s ∧
    Steps (b.Step r d) s (e.run r s d).1 ∧
    b.Stable r (e.run r s d).1 d ∧
    (∀ child, b.Generated r (e.run r s d).1 d child →
      b.Stable r (e.run r s d).1 child) ∧
    (∀ model, b.Models (e.run r s d).1 model → b.Models s model)

/-- (2)健全性/完全性。任意のchecked registry、初期state、需要、診断treeについて、
実tree返値と独立Resolvesがiff。成功・Models・FrontierExact・Accは外部仮定にない。 -/
def Exact (b : SourceBoundary v) (e : Executor v) : Prop :=
  ∀ (r : v.Registry), b.Checked r → ∀ (s : v.State) (d : v.Demand) (tree : Tree), b.Initial r d s →
    ((e.run r s d).2 = tree ↔ Resolves (Local b r (e.run r s d).1) d tree)

/-- (3)順序独立。可視宣言/whereのみを並べ替えた任意のchecked registry同士で、
同じ初期state・需要の最終結果が独立な観察同値を満たす。辞書内容の同値は明示境界。 -/
def OrderIndependent (b : SourceBoundary v) (e : Executor v) : Prop :=
  ∀ (r r' : v.Registry), b.Checked r → b.Checked r' → b.Reorders r r' →
    ∀ (s : v.State) (d : v.Demand), b.Initial r d s →
      SameDiagnostic b.toSourceBoundary (e.run r s d).2 (e.run r' s d).2

/-- (4)辞書健全性。任意の最終モデルにおいて、selected辞書はroot headへの代入と
全where子を整合して証明する。Evidenceは実行版と独立にsourceから実装すべき境界。 -/
def DictionarySound (b : SourceBoundary v) (e : Executor v) : Prop :=
  ∀ (r : v.Registry), b.Checked r → ∀ (s : v.State) (d : v.Demand)
    (dictionary : Dictionary), b.Initial r d s →
    Classify b r (e.run r s d).1 d (.selected dictionary) →
    ∀ model, b.Models (e.run r s d).1 model →
      b.Evidence r (e.run r s d).1 model d dictionary

/-- (5)偽拒否なし。任意のchecked registry、初期state、需要について、実rejectedなら
草稿のroot K2・candidate K2・全候補消滅の少なくとも一つが最終状態で実際に成立。 -/
def NoFalseRejection (b : SourceBoundary v) (e : Executor v) : Prop :=
  ∀ (r : v.Registry), b.Checked r → ∀ (s : v.State) (d : v.Demand), b.Initial r d s →
    (e.run r s d).2 = .rejected → RejectReason b r (e.run r s d).1 d

/-- 未証明targetの5項。全B4の証明を表す定理定数ではない。
必要な具体sourceインスタンスを外部oracleで置換した成果を完成と称しない。 -/
def Statement (b : SourceBoundary v) (e : Executor v) : Prop :=
  SaturationTotal b e ∧ Exact b e ∧ OrderIndependent b e ∧
    DictionarySound b e ∧ NoFalseRejection b e


end Yulang.B4TargetV5
