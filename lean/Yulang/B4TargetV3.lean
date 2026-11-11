import Yulang.B4Skeleton

/-!
# I-19: inspection-pending and lossless B4 target

The old `B4Target.Statement` and `B4Skeleton` are retained as historical targets.
This revision retains V2 and additionally represents unfinished inspection.
All rejection reasons require not RootPending; empty survivors also require
not InspectionPending. Either K2 reason takes priority over inspection pending.
The executor returns the complete diagnostic Tree. Four-way Classify is only
the partial Completed projection; a failed child is never a root rejection.
All registry/state/demand/model quantifiers remain unrestricted as before.
This target schema does not implement the general source boundary.
-/
namespace Yulang.B4TargetV3
open CommonRoleOutermostResolver
open B4Target (Vocabulary SourceBoundary SafeKnown Unique Steps SameOutcome)
universe u
variable {v : Vocabulary.{u}}

/-- Inspection has started before any root rejection, including either K2 reason. -/
def RejectReason (b : SourceBoundary v) (r : v.Registry) (s : v.State)
    (d : v.Demand) : Prop :=
  ¬ b.RootPending r s d ∧ (b.RootK2 r s d ∨ b.CandidateK2 r s d ∨
    (¬ b.InspectionPending r s d ∧ ∀ key children, ¬ b.Survivor r s d key children))

abbrev Completed := B4Skeleton.Completed

/-- 独立な四方向分類。唯一候補の全where子がselectedの場合だけ有限辞書を構成。
未完成の親は診断treeとして保持し、四方向へ折り畳まない。`run`/solverの返値を定義に埋め込まない。 -/
inductive Classify (b : SourceBoundary v) (r : v.Registry) (s : v.State) :
    v.Demand → Result → Prop where
  | pending : b.RootPending r s d → Classify b r s d .pending
  | inspectionPending : ¬ b.RootPending r s d → b.InspectionPending r s d →
      ¬ b.RootK2 r s d → ¬ b.CandidateK2 r s d → Classify b r s d .pending
  | rejected : RejectReason b r s d → Classify b r s d .rejected
  | ambiguous : SafeKnown b r s d →
      b.Survivor r s d key₁ children₁ → b.Survivor r s d key₂ children₂ →
      key₁ ≠ key₂ → Classify b r s d .ambiguous
  | selected : SafeKnown b r s d → Unique b r s d key children →
      All₂ (fun child dictionary => Classify b r s child (.selected dictionary))
        children dictionaries →
      Classify b r s d (.selected (.node key dictionaries))

/-- 一需要の独立判断。再帰的な子の解決や辞書の成立は含まない。 -/
inductive Local (b : SourceBoundary v) (r : v.Registry) (s : v.State) :
    v.Demand → Frontier v.Demand → Prop where
  | pending : b.RootPending r s d → Local b r s d .pending
  | inspectionPending : ¬ b.RootPending r s d → b.InspectionPending r s d →
      ¬ b.RootK2 r s d → ¬ b.CandidateK2 r s d → Local b r s d .pending
  | rejected : RejectReason b r s d → Local b r s d .rejected
  | ambiguous : SafeKnown b r s d →
      b.Survivor r s d key₁ cs₁ → b.Survivor r s d key₂ cs₂ → key₁ ≠ key₂ →
      Local b r s d .ambiguous
  | selected : SafeKnown b r s d → Unique b r s d key children →
      Local b r s d (.selected key children)

mutual
  theorem tree_classifies (b : SourceBoundary v) (r : v.Registry) (s : v.State)
      (tree : Tree) (d : v.Demand) (outcome : Result)
      (resolved : Resolves (Local b r s) d tree) (done : Completed tree outcome) :
      Classify b r s d outcome := by
    cases resolved with
    | pending localRule =>
        cases done
        cases localRule with
        | pending h => exact .pending h
        | inspectionPending started pending root candidate =>
            exact .inspectionPending started pending root candidate
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
      All₂ (fun d dictionary => Classify b r s d (.selected dictionary)) demands dictionaries := by
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
      (derived : Classify b r s d (.selected dictionary)) :
      Resolves (Local b r s) d (render dictionary) := by
    cases dictionary with
    | node key dictionaries =>
        cases derived with
        | selected safe unique children =>
            exact .selected (.selected safe unique) (renders_resolve b r s _ _ children)
  termination_by sizeOf dictionary

  theorem renders_resolve (b : SourceBoundary v) (r : v.Registry) (s : v.State)
      (dictionaries : List Dictionary) (demands : List v.Demand)
      (derived : All₂ (fun d dictionary => Classify b r s d (.selected dictionary))
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
theorem classify_tree (derived : Classify b r s d outcome) :
    ∃ tree, Resolves (Local b r s) d tree ∧ Completed tree outcome := by
  cases derived with
  | pending h => exact ⟨.pending, .pending (.pending h), .pending⟩
  | inspectionPending started pending root candidate =>
      exact ⟨.pending, .pending (.inspectionPending started pending root candidate), .pending⟩
  | rejected h => exact ⟨.rejected, .rejected (.rejected h), .rejected⟩
  | ambiguous safe first last distinct =>
      exact ⟨.ambiguous, .ambiguous (.ambiguous safe first last distinct), .ambiguous⟩
  | @selected d key children dictionaries safe unique all =>
      exact ⟨render (.node key dictionaries),
        render_resolves _ _ _ _ _ (.selected safe unique all), render_completed _⟩

/-- 任意 source 境界についての有限木同値。実行関数の返値で分類を定義しない。 -/
theorem classify_tree_iff : Classify b r s d outcome ↔
    ∃ tree, Resolves (Local b r s) d tree ∧ Completed tree outcome :=
  ⟨classify_tree, fun ⟨tree, resolved, done⟩ => tree_classifies _ _ _ tree _ _ resolved done⟩

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
      (derived : Classify b r s d (.selected dictionary)) :
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
      (derived : All₂ (fun d dictionary => Classify b r s d (.selected dictionary))
        demands dictionaries) :
      All₂ (fun d dictionary => b.Evidence r s model d dictionary) demands dictionaries := by
    cases derived with
    | nil => exact .nil
    | cons first rest =>
        exact .cons (dictionary_evidence b node r checked s model models _ _ first)
          (dictionaries_evidence b node r checked s model models _ _ rest)
  termination_by sizeOf dictionaries
end


/-- Lossless structural equivalence: retain all tags, keys and child multiplicities;
only sibling order may change. This does not classify unfinished parents. -/
inductive DiagnosticPermutation : Tree → Tree → Prop where
  | pending : DiagnosticPermutation .pending .pending
  | rejected : DiagnosticPermutation .rejected .rejected
  | ambiguous : DiagnosticPermutation .ambiguous .ambiguous
  | selected : first.Perm middle → All₂ DiagnosticPermutation middle last →
      DiagnosticPermutation (.selected key first) (.selected key last)

mutual
  theorem diagnostic_refl (tree : Tree) : DiagnosticPermutation tree tree := by
    cases tree with
    | pending => exact .pending
    | rejected => exact .rejected
    | ambiguous => exact .ambiguous
    | selected key children => exact .selected (List.Perm.refl _) (diagnostics_refl children)
  termination_by sizeOf tree

  theorem diagnostics_refl (trees : List Tree) : All₂ DiagnosticPermutation trees trees := by
    cases trees with
    | nil => exact .nil
    | cons first rest => exact .cons (diagnostic_refl first) (diagnostics_refl rest)
  termination_by sizeOf trees
end

/-- Preserve incomplete diagnostics as well as the original completed-dictionary
observation boundary. Both directions are required. -/
def SameDiagnostic (b : SourceBoundary v) (first last : Tree) : Prop :=
  DiagnosticPermutation first last ∧
  (∀ out, Completed first out → ∃ other, Completed last other ∧ SameOutcome b out other) ∧
  (∀ out, Completed last out → ∃ other, Completed first other ∧ SameOutcome b other out)

theorem same_diagnostic_refl (b : SourceBoundary v)
    (dictRefl : ∀ dictionary, b.DictionaryEquivalent dictionary dictionary) (tree : Tree) :
    SameDiagnostic b tree tree := by
  have outcomeRefl (out : Result) : SameOutcome b out out := by
    cases out <;> simp only [SameOutcome]
    exact dictRefl _
  exact ⟨diagnostic_refl tree, fun out done => ⟨out, done, outcomeRefl out⟩,
    fun out done => ⟨out, done, outcomeRefl out⟩⟩

/-- The revised entry has no fuel, success, accessibility or model input premise. -/
structure Executor (v : Vocabulary) where
  run : v.Registry → v.State → v.Demand → v.State × Tree

/-- (1)停止・存在・安定閉包・モデル減少。全checked registry、全旧state、全需要に対し、
実進行stepのAcc、返値への有限実到達、rootと全生成需要の安定、全modelの包含を要求。
Paterson/K2からこれを示す必要があり、任意のrankを前提に追加していない。 -/
def SaturationTotal (b : SourceBoundary v) (e : Executor v) : Prop :=
  ∀ (r : v.Registry), b.Checked r → ∀ (s : v.State) (d : v.Demand),
    Acc (fun next current => b.Step r d current next) s ∧
    Steps (b.Step r d) s (e.run r s d).1 ∧
    b.Stable r (e.run r s d).1 d ∧
    (∀ child, b.Generated r (e.run r s d).1 d child →
      b.Stable r (e.run r s d).1 child) ∧
    (∀ model, b.Models (e.run r s d).1 model → b.Models s model)

/-- (2)健全性/完全性。任意のchecked registry、旧state、需要、診断treeについて、
実tree返値と独立Resolvesがiff。成功・Models・FrontierExact・Accは外部仮定にない。 -/
def Exact (b : SourceBoundary v) (e : Executor v) : Prop :=
  ∀ (r : v.Registry), b.Checked r → ∀ (s : v.State) (d : v.Demand) (tree : Tree),
    (e.run r s d).2 = tree ↔ Resolves (Local b r (e.run r s d).1) d tree

/-- (3)順序独立。可視宣言/whereのみを並べ替えた任意のchecked registry同士で、
同じ旧state・需要の最終結果が独立な観察同値を満たす。辞書内容の同値は明示境界。 -/
def OrderIndependent (b : SourceBoundary v) (e : Executor v) : Prop :=
  ∀ (r r' : v.Registry), b.Checked r → b.Checked r' → b.Reorders r r' →
    ∀ (s : v.State) (d : v.Demand),
      SameDiagnostic b (e.run r s d).2 (e.run r' s d).2

/-- (4)辞書健全性。任意の最終モデルにおいて、selected辞書はroot headへの代入と
全where子を整合して証明する。Evidenceは実行版と独立にsourceから実装すべき境界。 -/
def DictionarySound (b : SourceBoundary v) (e : Executor v) : Prop :=
  ∀ (r : v.Registry), b.Checked r → ∀ (s : v.State) (d : v.Demand)
    (dictionary : Dictionary),
    Classify b r (e.run r s d).1 d (.selected dictionary) →
    ∀ model, b.Models (e.run r s d).1 model →
      b.Evidence r (e.run r s d).1 model d dictionary

/-- (5)偽拒否なし。任意のchecked registry、旧state、需要について、実rejectedなら
草稿のroot K2・candidate K2・全候補消滅の少なくとも一つが最終状態で実際に成立。 -/
def NoFalseRejection (b : SourceBoundary v) (e : Executor v) : Prop :=
  ∀ (r : v.Registry), b.Checked r → ∀ (s : v.State) (d : v.Demand),
    (e.run r s d).2 = .rejected → RejectReason b r (e.run r s d).1 d

/-- 未証明targetの5項。全B4の証明を表す定理定数ではない。
必要な具体sourceインスタンスを外部oracleで置換した成果を完成と称しない。 -/
def Statement (b : SourceBoundary v) (e : Executor v) : Prop :=
  SaturationTotal b e ∧ Exact b e ∧ OrderIndependent b e ∧
    DictionarySound b e ∧ NoFalseRejection b e


end Yulang.B4TargetV3
