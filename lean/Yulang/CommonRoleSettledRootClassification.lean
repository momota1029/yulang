import Yulang.CommonRoleSettledResolver

/-!
# 安定 unary 断片の、根を変えない診断分類

独立な既存 `Resolves` を lossless な判断として使う。唯一候補の子が
非成功でも親を rejected に書き換えず、元の selected tree を保持する。
根の拒否と三つの仕様理由の iff を閉じる。一般区間の飽和や最終言語分類、
全言語の辞書健全性はこの断片の主張に含めない。
-/
namespace Yulang.CommonRoleSettledRootClassification
open CommonRoleOutermostResolver (Tree Frontier All₂ Resolves)
open CommonRoleSettledSyntax
open CommonRoleSettledFrontier

/-- 実行版を参照しない根の拒否理由。scanも独立なScan導出として与える。
候補検査の未解決を「候補なし」に読み替えない。 -/
inductive Rejection (visible : List Declaration) (q : Request n) : Prop where
  | rootK2 : q.lower = some t → t.Regular → Rejection visible q
  | candidateK2 : q.lower = some t → t ≠ .unknown → ¬ t.Regular →
      Scan q.state q.role t visible results → .blocked ∈ results → Rejection visible q
  | exhausted : q.lower = some t → t ≠ .unknown → ¬ t.Regular →
      Scan q.state q.role t visible results → .blocked ∉ results → .deferred ∉ results →
      hits results = [] → Rejection visible q

/-- 健全性/完全性: 一需要の独立な根の拒否 iff 仕様の三理由。 -/
theorem local_rejected_iff (visible : List Declaration) (q : Request n) :
    Local visible q .rejected ↔ Rejection visible q := by
  constructor
  · intro h
    cases h with
    | root_cycle lower regular => exact .rootK2 lower regular
    | ready lower known finite scanned decision =>
        cases decision with
        | k2 blocked => exact .candidateK2 lower known finite scanned blocked
        | empty noBlocked noDeferred empty =>
            exact .exhausted lower known finite scanned noBlocked noDeferred empty
  · intro h
    cases h with
    | rootK2 lower regular => exact .root_cycle lower regular
    | candidateK2 lower known finite scanned blocked =>
        exact .ready lower known finite scanned (.k2 blocked)
    | exhausted lower known finite scanned noBlocked noDeferred empty =>
        exact .ready lower known finite scanned (.empty noBlocked noDeferred empty)

/-- 四方向の独立な判断を、子結果を失わない木として保つ。
selectedは「候補が唯一」の意味であり、全子辞書の完成を自動的には主張しない。 -/
abbrev Classify (visible : List Declaration) (q : Request n) (tree : Tree) : Prop :=
  Resolves (Local visible) q tree

/-- 健全性/完全性: 全checked registry、全settled request、全診断treeの iff。
成功・fuel・辞書・外部のfrontier正確性を前提にしない。 -/
theorem resolve_exact (registry : Registry) (q : Request n) (tree : Tree) :
    CommonRoleSettledResolver.resolve registry q = tree ↔ Classify registry.declarations q tree :=
  CommonRoleSettledResolver.resolve_tree_exact registry q tree

/-- 根の拒否は子の拒否から生じない。根そのものの三理由と正確に同値。 -/
theorem rejected_exact (registry : Registry) (q : Request n) :
    CommonRoleSettledResolver.resolve registry q = .rejected ↔ Rejection registry.declarations q := by
  rw [resolve_exact]
  constructor
  · intro h
    cases h with | rejected localRule => exact (local_rejected_iff _ _).mp localRule
  · intro h
    exact .rejected ((local_rejected_iff _ _).mpr h)

/-- 独立な根の拒否理由があれば、候補数の曖昧性やwhere子の成否には依存しない。 -/
theorem rejected_ne_selected (registry : Registry) (q : Request n)
    (reason : Rejection registry.declarations q) (key : Nat) (trees : List Tree) :
    CommonRoleSettledResolver.resolve registry q ≠ .selected key trees := by
  rw [(rejected_exact registry q).mpr reason]
  intro h
  cases h

/-- 未解決のlowerを持つ需要の根には、拒否理由がない。 -/
theorem absent_not_rejected (visible : List Declaration) (q : Request n)
    (absent : q.lower = none) : ¬ Rejection visible q := by
  intro h
  cases h <;> rename_i lower <;> simp_all

/-- 補助: 全子要求を、順序も重複も保って実行する。 -/
theorem all_children (registry : Registry) (children : List (Request n)) :
    All₂ (Classify registry.declarations) children
      (children.map (CommonRoleSettledResolver.resolve registry)) := by
  induction children with
  | nil => exact .nil
  | cons child rest ih => exact .cons ((resolve_exact registry child _).mp rfl) ih

/-- 唯一候補なら全子treeを保持する。子がpending/ambiguous/rejectedであっても同じ式。 -/
theorem selected_retains_children (registry : Registry) (q : Request n)
    (key : Nat) (children : List (Request n))
    (selected : Local registry.declarations q (.selected key children)) :
    CommonRoleSettledResolver.resolve registry q =
      .selected key (children.map (CommonRoleSettledResolver.resolve registry)) := by
  apply (resolve_exact registry q _).mpr
  exact .selected selected (all_children registry children)

/-- 子の拒否は、その子の位置の診断として残る。親の三理由に混ぜない。 -/
theorem selected_child_rejection_retained (registry : Registry) (q : Request n)
    (key : Nat) (children : List (Request n))
    (selected : Local registry.declarations q (.selected key children))
    (child : Request n) (member : child ∈ children)
    (rejected : Rejection registry.declarations child) :
    ∃ trees, CommonRoleSettledResolver.resolve registry q = .selected key trees ∧
      Tree.rejected ∈ trees ∧ ¬ Rejection registry.declarations q := by
  refine ⟨children.map (CommonRoleSettledResolver.resolve registry),
    selected_retains_children registry q key children selected, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨child, member, (rejected_exact registry child).mpr rejected⟩
  · intro reason
    have first := (rejected_exact registry q).mpr reason
    have last := selected_retains_children registry q key children selected
    rw [first] at last
    cases last

/-- K2候補がある場合は、ほかのhitが複数でも根を拒否する。 -/
theorem candidate_k2_priority (registry : Registry) (q : Request n)
    (lower : q.lower = some t) (known : t ≠ .unknown) (finite : ¬ t.Regular)
    (scanned : Scan q.state q.role t registry.declarations results)
    (blocked : .blocked ∈ results) : CommonRoleSettledResolver.resolve registry q = .rejected :=
  (rejected_exact registry q).mpr (.candidateK2 lower known finite scanned blocked)

/-- settled診断の未解決理由。最終言語エラーの新規則ではない。
既存Localと同じく、lower欠如、lower未知、K2なしの検査未解決を区別する。 -/
inductive Pending (visible : List Declaration) (q : Request n) : Prop where
  | absent : q.lower = none → Pending visible q
  | unknown : q.lower = some .unknown → Pending visible q
  | inspection : q.lower = some t → t ≠ .unknown → ¬ t.Regular →
      Scan q.state q.role t visible results → .blocked ∉ results → .deferred ∈ results →
      Pending visible q

/-- 独立な曖昧理由。K2と未解決がなく、二つ以上の実hitが残る。 -/
inductive Ambiguous (visible : List Declaration) (q : Request n) : Prop where
  | survivors : q.lower = some t → t ≠ .unknown → ¬ t.Regular →
      Scan q.state q.role t visible results → .blocked ∉ results → .deferred ∉ results →
      2 ≤ (hits results).length → Ambiguous visible q

theorem local_pending_iff (visible : List Declaration) (q : Request n) :
    Local visible q .pending ↔ Pending visible q := by
  constructor
  · intro h
    cases h with
    | absent lower => exact .absent lower
    | unknown lower => exact .unknown lower
    | ready lower known finite scanned decision =>
        cases decision with
        | pending noBlocked deferred => exact .inspection lower known finite scanned noBlocked deferred
  · intro h
    cases h with
    | absent lower => exact .absent lower
    | unknown lower => exact .unknown lower
    | inspection lower known finite scanned noBlocked deferred =>
        exact .ready lower known finite scanned (.pending noBlocked deferred)

theorem local_ambiguous_iff (visible : List Declaration) (q : Request n) :
    Local visible q .ambiguous ↔ Ambiguous visible q := by
  constructor
  · intro h
    cases h with
    | ready lower known finite scanned decision =>
        cases decision with
        | ambiguous noBlocked noDeferred many =>
            exact .survivors lower known finite scanned noBlocked noDeferred many
  · intro h
    cases h with
    | survivors lower known finite scanned noBlocked noDeferred many =>
        exact .ready lower known finite scanned (.ambiguous noBlocked noDeferred many)

/-- 保留はrootの独立な理由と同値。子のpendingを親へ折り畳まない。 -/
theorem pending_exact (registry : Registry) (q : Request n) :
    CommonRoleSettledResolver.resolve registry q = .pending ↔ Pending registry.declarations q := by
  rw [resolve_exact]
  constructor
  · intro h
    cases h with | pending localRule => exact (local_pending_iff _ _).mp localRule
  · intro h
    exact .pending ((local_pending_iff _ _).mpr h)

/-- 曖昧はroot自身の複数survivorと同値。子のambiguousを親へ折り畳まない。 -/
theorem ambiguous_exact (registry : Registry) (q : Request n) :
    CommonRoleSettledResolver.resolve registry q = .ambiguous ↔ Ambiguous registry.declarations q := by
  rw [resolve_exact]
  constructor
  · intro h
    cases h with | ambiguous localRule => exact (local_ambiguous_iff _ _).mp localRule
  · intro h
    exact .ambiguous ((local_ambiguous_iff _ _).mpr h)

/-- selectedのidentityと全where列を独立判断が正確に回収する。
未完成の子を捨てる条件も、全子成功の前提も入れない。 -/
theorem selected_exact (registry : Registry) (q : Request n) (key : Nat) (trees : List Tree) :
    CommonRoleSettledResolver.resolve registry q = .selected key trees ↔
      ∃ children, Local registry.declarations q (.selected key children) ∧
        All₂ (Classify registry.declarations) children trees := by
  rw [resolve_exact]
  constructor
  · intro h
    cases h with | selected localRule children => exact ⟨_, localRule, children⟩
  · rintro ⟨children, localRule, all⟩
    exact .selected localRule all

/-- 任意のrequestで四つの根tagのどれかが成立し、selectedでは子treeを全て返す。
この全域性は失敗を親へ伝播する四方向summaryとは異なる。 -/
theorem total (registry : Registry) (q : Request n) :
    Pending registry.declarations q ∨ Rejection registry.declarations q ∨
      Ambiguous registry.declarations q ∨
      ∃ key trees, Classify registry.declarations q (.selected key trees) := by
  cases returned : CommonRoleSettledResolver.resolve registry q with
  | pending => exact .inl ((pending_exact _ _).mp returned)
  | rejected => exact .inr (.inl ((rejected_exact _ _).mp returned))
  | ambiguous => exact .inr (.inr (.inl ((ambiguous_exact _ _).mp returned)))
  | selected key trees => exact .inr (.inr (.inr ⟨key, trees, (resolve_exact _ _ _).mp returned⟩))

end Yulang.CommonRoleSettledRootClassification
