import Main

/-!
# B4 の五項へ至る局所的な橋の骨格

既存の `B4Target.Statement` を量化子も含めてそのまま使う。
このモジュールは source carrier の実装でも、一般 B4 の証明でもない。
下の全フィールドを満たす source インスタンスはまだない。
特に `completedReadback` は未完成の診断 tree の最終分類という未決境界を
露出させる。子の失敗を根の拒否へまとめる規則は追加しない。
-/
namespace Yulang.B4Skeleton
open CommonRoleOutermostResolver
open B4Target
universe u
variable {v : Vocabulary.{u}}

/-- 元の承認済み五項。新しい範囲制限や成功前提を足さない。 -/
abbrev B4Statement (b : SourceBoundary v) (e : Executor v) : Prop := Statement b e

/-- 一需要の独立判断。再帰的な子の解決や辞書の成立は含まない。 -/
inductive Local (b : SourceBoundary v) (r : v.Registry) (s : v.State) :
    v.Demand → Frontier v.Demand → Prop where
  | pending : b.RootPending r s d → Local b r s d .pending
  | rejected : RejectReason b r s d → Local b r s d .rejected
  | ambiguous : SafeKnown b r s d →
      b.Survivor r s d key₁ cs₁ → b.Survivor r s d key₂ cs₂ → key₁ ≠ key₂ →
      Local b r s d .ambiguous
  | selected : SafeKnown b r s d → Unique b r s d key children →
      Local b r s d (.selected key children)

/-- 全 where 子が辞書を持つ場合だけ selected を返す純粋な tree 読み戻し。
未完成親に対する新しい言語上の分類は定義しない。 -/
inductive Completed : Tree → Result → Prop where
  | pending : Completed .pending .pending
  | rejected : Completed .rejected .rejected
  | ambiguous : Completed .ambiguous .ambiguous
  | selected : All₂ (fun tree dictionary => Completed tree (.selected dictionary))
      trees dictionaries → Completed (.selected key trees) (.selected (.node key dictionaries))

mutual
  theorem completed_summary (tree : Tree) (outcome : Result)
      (done : Completed tree outcome) : Summarizes tree outcome := by
    cases done with
    | pending => exact .pending
    | rejected => exact .rejected
    | ambiguous => exact .ambiguous
    | selected all => exact .selected (completed_summaries _ _ all) (.selected rfl)
  termination_by sizeOf tree

  theorem completed_summaries (trees : List Tree) (dictionaries : List Dictionary)
      (done : All₂ (fun tree dictionary => Completed tree (.selected dictionary)) trees dictionaries) :
      All₂ Summarizes trees (dictionaries.map Result.selected) := by
    cases done with
    | nil => exact .nil
    | cons first rest => exact .cons (completed_summary _ _ first) (completed_summaries _ _ rest)
  termination_by sizeOf trees
end

theorem completed_unique (left : Completed tree first) (right : Completed tree last) : first = last :=
  ((classification_exact tree first).mpr (completed_summary _ _ left)).symm.trans
    ((classification_exact tree last).mpr (completed_summary _ _ right))

/-- 完成した親の各whereには、その同じ位置の完成辞書がある。 -/
theorem completed_child (done : Completed (.selected key trees) outcome)
    (child : Tree) (member : child ∈ trees) :
    ∃ dictionary, Completed child (.selected dictionary) := by
  cases done with
  | selected children =>
      induction children with
      | nil => cases member
      | @cons tree dictionary trees dictionaries first rest ih =>
          rcases List.mem_cons.mp member with same | member
          · subst child
            exact ⟨dictionary, first⟩
          · exact ih member

/-- 既に承認された「未完成treeを保持」の場合には、古い全域four-way readbackはない。
この阻害は言語の新しい拒否規則ではない。 -/
theorem rejected_child_has_no_completed_readback (key : Nat) (trees : List Tree)
    (rejected : Tree.rejected ∈ trees) (outcome : Result) :
    ¬ Completed (.selected key trees) outcome := by
  intro done
  obtain ⟨dictionary, complete⟩ := completed_child done .rejected rejected
  cases complete

/-- 新しい骨格とMainの既存targetは、全量化子を含めて定義的に同じ。 -/
theorem target_unchanged (b : SourceBoundary v) (e : Executor v) :
    B4Statement b e ↔ Yulang.Main.B4Statement b e := Iff.rfl

mutual
  theorem tree_classifies (b : SourceBoundary v) (r : v.Registry) (s : v.State)
      (tree : Tree) (d : v.Demand) (outcome : Result)
      (resolved : Resolves (Local b r s) d tree) (done : Completed tree outcome) :
      B4Target.Classify b r s d outcome := by
    cases resolved with
    | pending localRule => cases done; cases localRule with | pending h => exact .pending h
    | rejected localRule => cases done; cases localRule with | rejected h => exact .rejected h
    | ambiguous localRule =>
        cases done
        cases localRule with | ambiguous safe first last distinct => exact .ambiguous safe first last distinct
    | selected localRule children =>
        cases done with
        | selected doneChildren =>
            cases localRule with
            | selected safe unique =>
                exact .selected safe unique (children_classify b r s _ _ _ children doneChildren)
  termination_by sizeOf tree

  theorem children_classify (b : SourceBoundary v) (r : v.Registry) (s : v.State)
      (trees : List Tree) (demands : List v.Demand) (dictionaries : List Dictionary)
      (resolved : All₂ (Resolves (Local b r s)) demands trees)
      (done : All₂ (fun tree dictionary => Completed tree (.selected dictionary)) trees dictionaries) :
      All₂ (fun d dictionary => B4Target.Classify b r s d (.selected dictionary)) demands dictionaries := by
    cases resolved with
    | nil => cases done; exact .nil
    | cons first rest =>
        cases done with
        | cons firstDone restDone =>
            exact .cons (tree_classifies b r s _ _ _ first firstDone)
              (children_classify b r s _ _ _ rest restDone)
  termination_by sizeOf trees
end

mutual
  def render : Dictionary → Tree
    | .node key children => .selected key (renders children)
  def renders : List Dictionary → List Tree
    | [] => []
    | first :: rest => render first :: renders rest
end

mutual
  theorem render_resolves (b : SourceBoundary v) (r : v.Registry) (s : v.State)
      (dictionary : Dictionary) (d : v.Demand)
      (derived : B4Target.Classify b r s d (.selected dictionary)) :
      Resolves (Local b r s) d (render dictionary) := by
    cases dictionary with
    | node key dictionaries =>
        cases derived with
        | selected safe unique children =>
            exact .selected (.selected safe unique) (renders_resolve b r s _ _ children)
  termination_by sizeOf dictionary

  theorem renders_resolve (b : SourceBoundary v) (r : v.Registry) (s : v.State)
      (dictionaries : List Dictionary) (demands : List v.Demand)
      (derived : All₂ (fun d dictionary => B4Target.Classify b r s d (.selected dictionary))
        demands dictionaries) : All₂ (Resolves (Local b r s)) demands (renders dictionaries) := by
    cases derived with
    | nil => exact .nil
    | cons first rest => exact .cons (render_resolves b r s _ _ first) (renders_resolve b r s _ _ rest)
  termination_by sizeOf dictionaries
end

mutual
  theorem render_completed (dictionary : Dictionary) : Completed (render dictionary) (.selected dictionary) := by
    cases dictionary with
    | node key dictionaries => exact .selected (renders_completed dictionaries)
  termination_by sizeOf dictionary

  theorem renders_completed (dictionaries : List Dictionary) :
      All₂ (fun tree dictionary => Completed tree (.selected dictionary)) (renders dictionaries) dictionaries := by
    cases dictionaries with
    | nil => exact .nil
    | cons first rest => exact .cons (render_completed first) (renders_completed rest)
  termination_by sizeOf dictionaries
end

/-- 元の独立分類は、失敗を伝播しない完全な tree の判断を持つ。 -/
theorem classify_tree (derived : B4Target.Classify b r s d outcome) :
    ∃ tree, Resolves (Local b r s) d tree ∧ Completed tree outcome := by
  cases derived with
  | pending h => exact ⟨.pending, .pending (.pending h), .pending⟩
  | rejected h => exact ⟨.rejected, .rejected (.rejected h), .rejected⟩
  | ambiguous safe first last distinct =>
      exact ⟨.ambiguous, .ambiguous (.ambiguous safe first last distinct), .ambiguous⟩
  | @selected d key children dictionaries safe unique all =>
      exact ⟨render (.node key dictionaries),
        render_resolves _ _ _ _ _ (.selected safe unique all), render_completed _⟩

/-- 任意 source 境界についての有限木同値。実行関数の返値で分類を定義しない。 -/
theorem classify_tree_iff : B4Target.Classify b r s d outcome ↔
    ∃ tree, Resolves (Local b r s) d tree ∧ Completed tree outcome :=
  ⟨classify_tree, fun ⟨tree, resolved, done⟩ => tree_classifies _ _ _ tree _ _ resolved done⟩

/-- 一段の model 保存を有限 trace に持ち上げる。 -/
theorem steps_models (b : SourceBoundary v) (r : v.Registry) (d : v.Demand)
    (localRule : ∀ before after, b.Step r d before after →
      ∀ model, b.Models after model → b.Models before model)
    (trace : Steps (b.Step r d) before after) :
    ∀ model, b.Models after model → b.Models before model := by
  induction trace with
  | refl => exact fun _ h => h
  | tail previous step ih => exact fun model h => ih model (localRule _ _ step model h)

/-- 一つの head とその全 where の証拠を結合する、局所的な意味保存。 -/
def EvidenceNode (b : SourceBoundary v) : Prop :=
  ∀ (r : v.Registry), b.Checked r → ∀ (s : v.State) (model : v.Model),
    b.Models s model → ∀ (d : v.Demand) (key : Nat) (children : List v.Demand)
      (dictionaries : List Dictionary), SafeKnown b r s d → Unique b r s d key children →
    All₂ (fun child dictionary => b.Evidence r s model child dictionary) children dictionaries →
    b.Evidence r s model d (.node key dictionaries)

mutual
  theorem dictionary_evidence (b : SourceBoundary v) (node : EvidenceNode b)
      (r : v.Registry) (checked : b.Checked r) (s : v.State) (model : v.Model)
      (models : b.Models s model) (dictionary : Dictionary) (d : v.Demand)
      (derived : B4Target.Classify b r s d (.selected dictionary)) :
      b.Evidence r s model d dictionary := by
    cases dictionary with
    | node key dictionaries =>
        cases derived with
        | selected safe unique children =>
            exact node r checked s model models d key _ dictionaries safe unique
              (dictionaries_evidence b node r checked s model models _ _ children)
  termination_by sizeOf dictionary

  theorem dictionaries_evidence (b : SourceBoundary v) (node : EvidenceNode b)
      (r : v.Registry) (checked : b.Checked r) (s : v.State) (model : v.Model)
      (models : b.Models s model) (dictionaries : List Dictionary) (demands : List v.Demand)
      (derived : All₂ (fun d dictionary => B4Target.Classify b r s d (.selected dictionary))
        demands dictionaries) :
      All₂ (fun d dictionary => b.Evidence r s model d dictionary) demands dictionaries := by
    cases derived with
    | nil => exact .nil
    | cons first rest =>
        exact .cons (dictionary_evidence b node r checked s model models _ _ first)
          (dictionaries_evidence b node r checked s model models _ _ rest)
  termination_by sizeOf dictionaries
end

/- 任意の独立局所判断を、tree の形を変えずに移送する。 -/
mutual
  theorem resolves_transport {Request : Type u}
      {first last : Request → Frontier Request → Prop}
      (localMap : ∀ d f, first d f → last d f)
      {d : Request} {tree : Tree}
      (h : Resolves first d tree) : Resolves last d tree := by
    cases h with
    | pending h => exact .pending (localMap _ _ h)
    | rejected h => exact .rejected (localMap _ _ h)
    | ambiguous h => exact .ambiguous (localMap _ _ h)
    | selected h children =>
        exact .selected (localMap _ _ h) (resolves_children_transport localMap children)
  termination_by sizeOf tree

  theorem resolves_children_transport {Request : Type u}
      {first last : Request → Frontier Request → Prop}
      (localMap : ∀ d f, first d f → last d f)
      {demands : List Request} {trees : List Tree}
      (h : All₂ (Resolves first) demands trees) : All₂ (Resolves last) demands trees := by
    cases h with
    | nil => exact .nil
    | cons first rest => exact .cons (resolves_transport localMap first) (resolves_children_transport localMap rest)
  termination_by sizeOf trees
end

/-- 証明済みの局所核と未接続の実入口を区別するための、実 frontier データ。 -/
abbrev Frontiers (v : Vocabulary) := v.Registry → v.State → Protocol v.Demand

/-- 全項を言い換えたフィールドはない。進行、局所判断、pure readback、
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
  /-- 橋4、package3: 完全な辞書の読み戻し。未完成treeの最終方針が未接続。 -/
  completedReadback : ∀ r (_checked : b.Checked r) s d
    (exact : FrontierExact (frontiers r (e.run r s d).1))
    (accessible : Acc (Child (frontiers r (e.run r s d).1).Local) d),
    Completed (resolve (frontiers r (e.run r s d).1) exact d accessible) (e.run r s d).2
  /-- 橋4/5、package5: 可視順とwhere順だけの変更を、同じsource義務の正準順で比較。 -/
  canonicalLocalOrder : ∀ r r', b.Checked r → b.Checked r' → b.Reorders r r' →
    ∀ s root d f, Local b r (e.run r s root).1 d f ↔ Local b r' (e.run r' s root).1 d f
  /-- 橋5、package5: 同一の正準辞書を観察同値とする最小の法則。 -/
  dictionaryRefl : ∀ dictionary, b.DictionaryEquivalent dictionary dictionary
  /-- 橋5、package6/7: 一つのheadと全where証拠のモデル上の結合。 -/
  evidenceNode : EvidenceNode b

/-- B4Bridges の12義務を既存五項へ合成する。sourceインスタンスは未構成。 -/
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
  have outputTree (r : v.Registry) (checked : b.Checked r) (s : v.State) (d : v.Demand) :
      ∃ tree, Resolves (Local b r (e.run r s d).1) d tree ∧ Completed tree (e.run r s d).2 := by
    let tree := resolve (frontiers r (e.run r s d).1) (exact r checked _) d (accessible r checked _ d)
    refine ⟨tree, ?_, bridges.completedReadback r checked s d _ _⟩
    have result := (resolve_tree_exact_of_frontier_exact (frontiers r (e.run r s d).1)
      (exact r checked _) d (accessible r checked _ d) tree).mp rfl
    simpa only [bridges.localIdentity] using result
  have exactResult : Exact b e := by
    intro r checked s d outcome
    obtain ⟨tree, resolved, done⟩ := outputTree r checked s d
    constructor
    · intro same; subst outcome; exact tree_classifies b r _ tree d _ resolved done
    · intro derived
      obtain ⟨other, otherResolved, otherDone⟩ := classify_tree derived
      have sameTree : tree = other := by
        have first := (resolve_tree_exact_of_frontier_exact (frontiers r (e.run r s d).1)
          (exact r checked _) d (accessible r checked _ d) tree).mpr
            (by simpa only [bridges.localIdentity] using resolved)
        have last := (resolve_tree_exact_of_frontier_exact (frontiers r (e.run r s d).1)
          (exact r checked _) d (accessible r checked _ d) other).mpr
            (by simpa only [bridges.localIdentity] using otherResolved)
        exact first.symm.trans last
      subst other
      exact completed_unique done otherDone
  refine ⟨?_, exactResult, ?_, ?_, ?_⟩
  · intro r checked s d
    obtain ⟨stable, generated⟩ := bridges.closure r checked _ d (bridges.halted r checked s d)
    exact ⟨bridges.progress r checked s d, bridges.execution r checked s d, stable, generated,
      steps_models b r d (bridges.stepModels r checked d) (bridges.execution r checked s d)⟩
  · intro r r' checked checked' order s d
    obtain ⟨tree, resolved, done⟩ := outputTree r checked s d
    have transported := resolves_transport
      (fun q f h => (bridges.canonicalLocalOrder r r' checked checked' order s d q f).mp h) resolved
    have derived := tree_classifies b r' _ tree d _ transported done
    have same := (exactResult r' checked' s d _).mpr derived
    rw [same]
    cases (e.run r s d).2 <;> simp only [SameOutcome]
    exact bridges.dictionaryRefl _
  · intro r checked s d dictionary derived model models
    exact dictionary_evidence b bridges.evidenceNode r checked _ model models dictionary d derived
  · intro r checked s d returned
    have classified := (exactResult r checked s d .rejected).mp returned
    cases classified with | rejected reason => exact reason

/-- Root pending と根の拒否理由が同時成立するsnapshotを全域な正確分類へ
接続できない。source境界の排他性を隠さないための阻害定理。 -/
theorem pending_rejection_obstruction (b : SourceBoundary v) (e : Executor v)
    (r : v.Registry) (checked : b.Checked r) (s : v.State) (d : v.Demand)
    (pending : b.RootPending r (e.run r s d).1 d)
    (rejected : RejectReason b r (e.run r s d).1 d) : ¬ Exact b e := by
  intro exact
  have first := (exact r checked s d .pending).mpr (.pending pending)
  have last := (exact r checked s d .rejected).mpr (.rejected rejected)
  rw [first] at last
  cases last

/-- 未解決lowerと空のsurvivorが同時にある場合、旧targetの無条件な
「全候補なし」節がpendingとrejectedを重ねる。この問題はexecutorの変更では直らない。 -/
theorem pending_empty_survivors_obstruction (b : SourceBoundary v) (e : Executor v)
    (r : v.Registry) (checked : b.Checked r) (s : v.State) (d : v.Demand)
    (pending : b.RootPending r (e.run r s d).1 d)
    (empty : ∀ key children, ¬ b.Survivor r (e.run r s d).1 d key children) :
    ¬ B4Statement b e := by
  intro target
  exact pending_rejection_obstruction b e r checked s d pending (Or.inr (Or.inr empty)) target.2.1

/-- 上の二重分類があるsourceインスタンスでは、12義務をすべて満たす橋も存在しない。 -/
theorem bridges_obstructed_by_pending_empty (b : SourceBoundary v) (e : Executor v)
    (frontiers : Frontiers v) (r : v.Registry) (checked : b.Checked r)
    (s : v.State) (d : v.Demand)
    (pending : b.RootPending r (e.run r s d).1 d)
    (empty : ∀ key children, ¬ b.Survivor r (e.run r s d).1 d key children) :
    ¬ B4Bridges b e frontiers := by
  intro bridges
  exact pending_empty_survivors_obstruction b e r checked s d pending empty
    (b4_of_bridges b e frontiers bridges)

end Yulang.B4Skeleton
