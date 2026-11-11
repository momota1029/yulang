import Yulang.B4TargetV3Functionality

/-!
# Twelve local bridges to the revised B4 target

`B4Skeleton` and `B4SkeletonV2` remain historical target packages. Here treeExecution replaces its
impossible total completedReadback obligation. The other eleven obligations
retain their roles. No concrete general-source instance exists yet: 12/12
fields remain unfilled for that carrier, independently of fragment results.
-/
namespace Yulang.B4SkeletonV3
open CommonRoleOutermostResolver
open B4Target (Vocabulary SourceBoundary Steps)
open B4TargetV3
universe u
variable {v : Vocabulary.{u}}

abbrev B4Statement (b : SourceBoundary v) (e : Executor v) : Prop := Statement b e
abbrev Frontiers := B4Skeleton.Frontiers

/-- 全項を言い換えたフィールドはない。進行、局所判断、lossless tree execution、
局所的な順序の対応、head 一個の意味保存を別々の義務として持つ。
`canonicalLocalOrder` は source 義務 identity を保つ正準化の義務であり、
生の where リストの順序一致を既に証明したとは言わない。 -/
structure B4Bridges (b : SourceBoundary v) (e : Executor v) (frontiers : Frontiers v) : Prop where
  /-- 橋3、package1/2/4: Paterson/K2から実更新の下降を導く。 -/
  progress : ∀ r, b.Checked r → ∀ s d, Acc (fun next current => b.Step r d current next) s
  /-- 橋3、package1: 最終stateが実step列から得られる。 -/
  execution : ∀ r, b.Checked r → ∀ s d, Steps (b.Step r d) s (e.run r s d).1
  /-- 橋3、package1: 完了したdriverに新しいstepはない。 -/
  halted : ∀ r, b.Checked r → ∀ s d next, ¬ b.Step r d (e.run r s d).1 next
  /-- 橋2/3、package1/2: 停止がrootと全生成需要の意味的な安定を与える。 -/
  closure : ∀ r, b.Checked r → ∀ s d, (∀ next, ¬ b.Step r d s next) →
    b.Stable r s d ∧ ∀ child, b.Generated r s d child → b.Stable r s child
  /-- 橋1/2、package2/7: ordinaryと関連型の一段更新は全modelで健全。 -/
  stepModels : ∀ r, b.Checked r → ∀ d before after, b.Step r d before after →
    ∀ model, b.Models after model → b.Models before model
  /-- 橋1/4、package3/4/7: 一需要のfrontierと独立局所規則の対応。 -/
  frontierLocal : ∀ r, b.Checked r → ∀ s d f,
    (frontiers r s).frontier d = f ↔ Local b r s d f
  /-- 橋4、package3/4: protocolに任意の別判断を忍ばせない。 -/
  localIdentity : ∀ r s, (frontiers r s).Local = Local b r s
  /-- 橋2、package2/4: 一つの安定snapshotで全where再帰が下降する。 -/
  whereAccessible : ∀ r, b.Checked r → ∀ s d, Acc (Child (Local b r s)) d
  /-- 橋4、package3: 実入口を既存の独立再帰実装に分解する。全域readbackは要求しない。 -/
  treeExecution : ∀ r (_checked : b.Checked r) s d
    (exact : FrontierExact (frontiers r (e.run r s d).1))
    (accessible : Acc (Child (frontiers r (e.run r s d).1).Local) d),
    (e.run r s d).2 = resolve (frontiers r (e.run r s d).1) exact d accessible
  /-- 橋4/5、package5: 可視順とwhere順だけの変更を、同じsource義務の正準順で比較。 -/
  canonicalLocalOrder : ∀ r r', b.Checked r → b.Checked r' → b.Reorders r r' →
    ∀ s root d f, Local b r (e.run r s root).1 d f ↔ Local b r' (e.run r' s root).1 d f
  /-- 橋5、package5: 同一の正準辞書を観察同値とする最小の法則。 -/
  dictionaryRefl : ∀ dictionary, b.DictionaryEquivalent dictionary dictionary
  /-- 橋5、package6/7: 一つのheadと全where証拠のモデル上の結合。 -/
  evidenceNode : EvidenceNode b


/-- Assemble twelve strictly smaller implementation/local-rule obligations.
This conditional composition theorem is not a general-source B4 proof. -/
theorem b4_of_bridges (b : SourceBoundary v) (e : Executor v) (frontiers : Frontiers v)
    (bridges : B4Bridges b e frontiers) : B4Statement b e := by
  have exact (r : v.Registry) (checked : b.Checked r) (s : v.State) :
      FrontierExact (frontiers r s) := by
    intro d f
    rw [bridges.localIdentity]
    exact bridges.frontierLocal r checked s d f
  have accessible (r : v.Registry) (checked : b.Checked r) (s : v.State) (d : v.Demand) :
      Acc (Child (frontiers r s).Local) d := by
    rw [bridges.localIdentity]
    exact bridges.whereAccessible r checked s d
  have exactTree : Exact b e := by
    intro r checked s d tree
    rw [bridges.treeExecution r checked s d (exact r checked _) (accessible r checked _ d)]
    have rule := resolve_tree_exact_of_frontier_exact (frontiers r (e.run r s d).1)
      (exact r checked _) d (accessible r checked _ d) tree
    simpa only [bridges.localIdentity] using rule
  refine ⟨?_, exactTree, ?_, ?_, ?_⟩
  · intro r checked s d
    obtain ⟨stable, generated⟩ := bridges.closure r checked _ d (bridges.halted r checked s d)
    exact ⟨bridges.progress r checked s d, bridges.execution r checked s d, stable, generated,
      B4Skeleton.steps_models b r d (bridges.stepModels r checked d) (bridges.execution r checked s d)⟩
  · intro r r' checked checked' order s d
    have resolved := (exactTree r checked s d _).mp rfl
    have transported := B4Skeleton.resolves_transport
      (fun q f h => (bridges.canonicalLocalOrder r r' checked checked' order s d q f).mp h) resolved
    have same := (exactTree r' checked' s d _).mpr transported
    rw [same]
    exact same_diagnostic_refl b bridges.dictionaryRefl _
  · intro r checked s d dictionary derived model models
    exact dictionary_evidence b bridges.evidenceNode r checked _ model models dictionary d derived
  · intro r checked s d returned
    have resolved := (exactTree r checked s d .rejected).mp returned
    cases resolved with
    | rejected localRule => cases localRule with | rejected reason => exact reason

/-- Four-way exactness is only requested on Completed trees, not all returned trees. -/
theorem completed_of_bridges (b : SourceBoundary v) (e : Executor v) (frontiers : Frontiers v)
    (bridges : B4Bridges b e frontiers) (r : v.Registry) (checked : b.Checked r)
    (s : v.State) (d : v.Demand) (out : Result) :
    Completed (e.run r s d).2 out ↔ B4TargetV3.Classify b r (e.run r s d).1 d out :=
  completed_exact b e (b4_of_bridges b e frontiers bridges).2.1 r checked s d out

end Yulang.B4SkeletonV3
