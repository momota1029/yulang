import Yulang.B4TargetV3Functionality

/-!
# Thirteen local bridges with stable-scoped evidence

The V3 target is unchanged. Eleven non-evidence bridges are retained;
node evidence is now restricted to stable parents and children. A thirteenth
local bridge connects selected children to the root's Generated set. Closure,
not a hidden descendant-stability premise, then supplies every node's stability.
This is conditional composition, not a concrete general-source B4 instance.
-/
namespace Yulang.B4SkeletonV4
open CommonRoleOutermostResolver
open B4Target (Vocabulary SourceBoundary Steps SafeKnown Unique)
open B4TargetV3
universe u
variable {v : Vocabulary.{u}}

abbrev B4Statement (b : SourceBoundary v) (e : Executor v) : Prop := Statement b e
abbrev Frontiers := B4Skeleton.Frontiers

/-- Model evidence is required only once the selected parent and all its
immediate children are stable in this same snapshot. -/
def EvidenceNode (b : SourceBoundary v) : Prop :=
  ∀ (r : v.Registry), b.Checked r → ∀ (s : v.State) (model : v.Model),
    b.Models s model → ∀ (d : v.Demand) (key : Nat) (children : List v.Demand)
      (dictionaries : List Dictionary), b.Stable r s d →
    (∀ child, child ∈ children → b.Stable r s child) →
    SafeKnown b r s d → Unique b r s d key children →
    All₂ (fun child dictionary => b.Evidence r s model child dictionary) children dictionaries →
    b.Evidence r s model d (.node key dictionaries)

/-- One selected edge preserves membership in the saturation root's generated
closure. This is explicit because SourceBoundary imposes no law on Generated.
There is no recursive classification or dictionary-evidence premise here. -/
def GeneratedChildren (b : SourceBoundary v) : Prop :=
  ∀ (r : v.Registry), b.Checked r → ∀ (s : v.State) (root d : v.Demand)
    (key : Nat) (children : List v.Demand),
    (d = root ∨ b.Generated r s root d) → b.Stable r s d →
    SafeKnown b r s d → Unique b r s d key children →
    ∀ child, child ∈ children → b.Generated r s root child

/-- A useful sufficient decomposition: direct generation plus transitivity.
Both assumptions concern Generated, not evidence or recursive Classify. -/
theorem generatedChildren_of_direct_transitive (b : SourceBoundary v)
    (direct : ∀ r, b.Checked r → ∀ s d key children, b.Stable r s d →
      SafeKnown b r s d → Unique b r s d key children →
      ∀ child, child ∈ children → b.Generated r s d child)
    (transitive : ∀ r, b.Checked r → ∀ s root parent child,
      b.Generated r s root parent → b.Generated r s parent child →
      b.Generated r s root child) : GeneratedChildren b := by
  intro r checked s root d key children reached stable safe unique child member
  have edge := direct r checked s d key children stable safe unique child member
  cases reached with
  | inl same => simpa only [same] using edge
  | inr generated => exact transitive r checked s root d child generated edge

mutual
  /-- Every recursive node gets stability from the same saturation closure. -/
  theorem dictionary_evidence (b : SourceBoundary v) (node : EvidenceNode b)
      (generatedChildren : GeneratedChildren b)
      (r : v.Registry) (checked : b.Checked r) (s : v.State) (root : v.Demand)
      (rootStable : b.Stable r s root)
      (generatedStable : ∀ child, b.Generated r s root child → b.Stable r s child)
      (model : v.Model) (models : b.Models s model)
      (dictionary : Dictionary) (d : v.Demand)
      (reached : d = root ∨ b.Generated r s root d)
      (derived : Classify b r s d (.selected dictionary)) :
      b.Evidence r s model d dictionary := by
    have stable : b.Stable r s d := by
      rcases reached with same | generated
      · exact same ▸ rootStable
      · exact generatedStable d generated
    cases dictionary with
    | node key dictionaries =>
        cases derived with
        | selected safe unique children =>
            have childGenerated := generatedChildren r checked s root d key _ reached stable safe unique
            exact node r checked s model models d key _ dictionaries stable
              (fun child member => generatedStable child (childGenerated child member)) safe unique
              (dictionaries_evidence b node generatedChildren r checked s root rootStable
                generatedStable model models _ _
                (fun child member => Or.inr (childGenerated child member)) children)
  termination_by sizeOf dictionary

  theorem dictionaries_evidence (b : SourceBoundary v) (node : EvidenceNode b)
      (generatedChildren : GeneratedChildren b)
      (r : v.Registry) (checked : b.Checked r) (s : v.State) (root : v.Demand)
      (rootStable : b.Stable r s root)
      (generatedStable : ∀ child, b.Generated r s root child → b.Stable r s child)
      (model : v.Model) (models : b.Models s model)
      (dictionaries : List Dictionary) (demands : List v.Demand)
      (reached : ∀ child, child ∈ demands → child = root ∨ b.Generated r s root child)
      (derived : All₂ (fun d dictionary => Classify b r s d (.selected dictionary))
        demands dictionaries) :
      All₂ (fun d dictionary => b.Evidence r s model d dictionary) demands dictionaries := by
    cases derived with
    | nil => exact .nil
    | cons first rest =>
        exact .cons (dictionary_evidence b node generatedChildren r checked s root rootStable
          generatedStable model models _ _ (reached _ (by simp)) first)
          (dictionaries_evidence b node generatedChildren r checked s root rootStable
            generatedStable model models _ _ (fun child member => reached child (by simp [member])) rest)
  termination_by sizeOf dictionaries
end

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
  /-- Selected edges belong to the saturation root's genuine generated closure. -/
  generatedChildren : GeneratedChildren b


/-- Assemble thirteen strictly smaller implementation/local-rule obligations.
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
    obtain ⟨rootStable, generatedStable⟩ :=
      bridges.closure r checked _ d (bridges.halted r checked s d)
    exact dictionary_evidence b bridges.evidenceNode bridges.generatedChildren r checked _ d
      rootStable generatedStable model models dictionary d (Or.inl rfl) derived
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

end Yulang.B4SkeletonV4
