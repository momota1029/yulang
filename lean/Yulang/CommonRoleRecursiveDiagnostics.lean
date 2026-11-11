import Yulang.RoleConstraints

/-! Complete failure-preserving trees for the existing rigid role resolver.
Every unique-head child is constructed by Paterson recursion, without success,
fuel or an external work table. The compatibility status is the existing core
status, not a new source-language final classification. -/
namespace Yulang.CommonRoleRecursiveDiagnostics
open Roles

inductive Tree where
  | missing (goal : Goal)
  | overlap (goal : Goal) (heads : List Impl)
  | selected (goal : Goal) (head : Impl) (children : List Tree)
  deriving Repr

def Tree.goal : Tree → Goal
  | .missing g | .overlap g _ | .selected g _ _ => g

def Tree.children : Tree → List Tree
  | .selected _ _ cs => cs
  | _ => []

def Tree.status : Tree → Result
  | .missing _ => .noImpl
  | .overlap _ _ => .ambiguous
  | .selected _ _ cs => combine (cs.map Tree.status)

/-- Independent unique matching-head judgment. -/
def Unique (impls : List Impl) (g : Goal) (i : Impl) : Prop :=
  i ∈ impls ∧ Matches i g ∧ ∀ j ∈ impls, Matches j g → j = i

theorem unique_iff (impls : List Impl) (g : Goal) (i : Impl) :
    Unique impls g i ↔ candidates impls g = [i] := by
  constructor
  · rintro ⟨hi,hm,huniq⟩
    have mem : i ∈ candidates impls g := mem_candidates.mpr ⟨hi,hm⟩
    have all : ∀ j ∈ candidates impls g, j = i :=
      fun j hj => huniq j (mem_candidates.mp hj).1 (mem_candidates.mp hj).2
    have nd := candidates_nodup impls g
    cases h : candidates impls g with
    | nil => simp [h] at mem
    | cons j rest =>
      have ji := all j (by simp [h])
      subst j
      cases rest with
      | nil => rfl
      | cons k rest =>
        have ki := all k (by simp [h])
        subst k
        simp [h] at nd
  · intro h
    have hi := mem_candidates.mp (h ▸ List.mem_singleton_self i)
    refine ⟨hi.1,hi.2,?_⟩
    intro j hj hm
    have : j ∈ candidates impls g := mem_candidates.mpr ⟨hj,hm⟩
    simpa only [h,List.mem_singleton] using this

/-- No constructor inspects the builder or its compatibility status. -/
inductive Represents (impls : List Impl) : Goal → Tree → Prop where
  | missing (g : Goal) (absent : ∀ i ∈ impls, ¬ Matches i g) :
      Represents impls g (.missing g)
  | overlap (g : Goal) (heads : List Impl)
      (exactHeads : ∀ i, i ∈ heads ↔ i ∈ impls ∧ Matches i g)
      (distinctHeads : heads.Nodup) (multiple : 2 ≤ heads.length) :
      Represents impls g (.overlap g heads)
  | selected (g : Goal) (i : Impl) (cs : List Tree) (unique : Unique impls g i)
      (goals : cs.map Tree.goal = i.constraints.map (fun c => c.subst (matchingSubst i.head g.args)))
      (children : ∀ t ∈ cs, Represents impls t.goal t) :
      Represents impls g (.selected g i cs)

/-- All siblings are retained even if another sibling is missing or overlaps. -/
def diagnose (impls : List Impl) (wf : WellFormed impls) (g : Goal) : Tree :=
  match h : candidates impls g with
  | [] => .missing g
  | [i] =>
    have _matching : i ∈ impls ∧ Matches i g := mem_candidates.mp (h ▸ List.mem_singleton_self i)
    .selected g i (i.constraints.attach.map fun c =>
      diagnose impls wf (c.val.subst (matchingSubst i.head g.args)))
  | i :: j :: rest => .overlap g (i :: j :: rest)
termination_by argsSize g.args
decreasing_by
  simpa only [Goal.subst,matched_head _matching.2] using
    size_decreases (wf i _matching.1) c.property (matchingSubst i.head g.args)

theorem diagnose_goal (impls : List Impl) (wf : WellFormed impls) (g : Goal) :
    (diagnose impls wf g).goal = g := by
  rw [diagnose]; split <;> rfl

theorem diagnose_selected (impls : List Impl) (wf : WellFormed impls) (g : Goal)
    (i : Impl) (h : candidates impls g = [i]) :
    diagnose impls wf g = .selected g i
      (i.constraints.map fun c => diagnose impls wf (c.subst (matchingSubst i.head g.args))) := by
  rw [diagnose]; split <;> simp_all

theorem diagnose_missing (impls : List Impl) (wf : WellFormed impls) (g : Goal)
    (h : candidates impls g = []) : diagnose impls wf g = .missing g := by
  rw [diagnose]; split <;> simp_all

theorem diagnose_overlap (impls : List Impl) (wf : WellFormed impls) (g : Goal)
    (i j : Impl) (rest : List Impl) (h : candidates impls g = i :: j :: rest) :
    diagnose impls wf g = .overlap g (i :: j :: rest) := by
  rw [diagnose]; split <;> simp_all

theorem diagnose_status (impls : List Impl) (wf : WellFormed impls) (g : Goal) :
    (diagnose impls wf g).status = resolve impls wf g := by
  cases h : candidates impls g with
  | nil => rw [diagnose_missing impls wf g h,resolve_none impls wf g h]; simp only [Tree.status]
  | cons i rest =>
    cases rest with
    | nil =>
      rw [diagnose_selected impls wf g i h,resolve_one impls wf g i h]
      simp only [Tree.status,List.map_map]
      congr 1
      apply List.map_congr_left
      intro c hc
      exact diagnose_status impls wf _
    | cons j rest => rw [diagnose_overlap impls wf g i j rest h,resolve_many impls wf g i j rest h]; simp only [Tree.status]
termination_by argsSize g.args
decreasing_by
  have hm := mem_candidates.mp (h ▸ List.mem_singleton_self i)
  simpa only [Goal.subst,matched_head hm.2] using
    size_decreases (wf i hm.1) hc (matchingSubst i.head g.args)

theorem diagnose_represents (impls : List Impl) (wf : WellFormed impls) (g : Goal) :
    Represents impls g (diagnose impls wf g) := by
  cases h : candidates impls g with
  | nil =>
    rw [diagnose_missing impls wf g h]
    apply Represents.missing
    intro i hi hm
    have := mem_candidates.mpr ⟨hi,hm⟩
    simp [h] at this
  | cons i rest =>
    cases rest with
    | nil =>
      rw [diagnose_selected impls wf g i h]
      apply Represents.selected g i _ ((unique_iff impls g i).mpr h)
      · simp only [List.map_map,Function.comp_def,diagnose_goal]
      · intro t ht
        obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ht
        rw [diagnose_goal]
        exact diagnose_represents impls wf _
    | cons j rest =>
      rw [diagnose_overlap impls wf g i j rest h]
      apply Represents.overlap
      · intro k; rw [← h]; exact mem_candidates
      · rw [← h]; exact candidates_nodup impls g
      · simp
termination_by argsSize g.args
decreasing_by
  have hm := mem_candidates.mp (h ▸ List.mem_singleton_self i)
  simpa only [Goal.subst,matched_head hm.2] using
    size_decreases (wf i hm.1) hc (matchingSubst i.head g.args)

theorem diagnose_success_iff (impls : List Impl) (wf : WellFormed impls) (g : Goal) :
    (diagnose impls wf g).status = .resolved ↔ RoleConstraints.Resolves impls g := by
  rw [diagnose_status,RoleConstraints.resolve_exact]

/-- Every represented tree keeps the indexed root goal. -/
theorem represents_goal (impls : List Impl) (g : Goal) (t : Tree)
    (h : Represents impls g t) : t.goal = g := by cases h <;> rfl

/-- Exact recursive contents are independently checkable, including failures. -/
theorem represents_status (impls : List Impl) (wf : WellFormed impls)
    (g : Goal) (t : Tree) (h : Represents impls g t) :
    t.status = resolve impls wf g := by
  induction h with
  | missing g absent =>
    have empty : candidates impls g = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro i hi
      exact absent i (mem_candidates.mp hi).1 (mem_candidates.mp hi).2
    rw [Tree.status,resolve_none impls wf g empty]
  | overlap g heads exactHeads distinctHeads multiple =>
    have overlap : HeadOverlap impls g := by
      apply (head_overlap_iff impls g).mpr
      cases heads with
      | nil => simp at multiple
      | cons i rest =>
        cases rest with
        | nil => simp at multiple
        | cons j rest =>
          have hi := (exactHeads i).mp (by simp)
          have hj := (exactHeads j).mp (by simp)
          have ne : i ≠ j := by intro e; subst j; simp at distinctHeads
          exact ⟨i,hi.1,j,hj.1,ne,hi.2,hj.2⟩
    rw [Tree.status]
    exact ((resolve_ambiguous_iff impls wf g).mpr (.here overlap)).symm
  | selected g i cs unique goals children ih =>
    rw [Tree.status,resolve_one impls wf g i ((unique_iff impls g i).mp unique)]
    have statuses : cs.map Tree.status = cs.map (fun t => resolve impls wf t.goal) := by
      apply List.map_congr_left
      intro t ht
      exact ih t ht
    rw [statuses]
    have mapped := congrArg (List.map (resolve impls wf)) goals
    simpa only [List.map_map,Function.comp_def] using congrArg combine mapped

/-- Addressed lookup preserves sibling occurrence order and duplicates. -/
def Tree.follow (t : Tree) : List Nat → Option Tree
  | [] => some t
  | k :: rest => (t.children[k]?).bind (fun child => child.follow rest)

/-- Declaration-derived paths; missing or overlapping heads have no successor.
No successful-child premise appears on any edge. -/
inductive Path (impls : List Impl) : Goal → List Nat → Goal → Prop where
  | root (g : Goal) : Path impls g [] g
  | step {g target : Goal} {k : Nat} {rest : List Nat} (i : Impl) (c : Goal)
      (unique : Unique impls g i) (position : i.constraints[k]? = some c)
      (next : Path impls (c.subst (matchingSubst i.head g.args)) rest target) :
      Path impls g (k :: rest) target

theorem path_nil (impls : List Impl) (g target : Goal) :
    Path impls g [] target ↔ g = target := by
  constructor
  · intro h; cases h; rfl
  · intro h; subst target; exact .root g

theorem path_cons (impls : List Impl) (g target : Goal) (k : Nat) (rest : List Nat) :
    Path impls g (k :: rest) target ↔ ∃ i c, Unique impls g i ∧
      i.constraints[k]? = some c ∧
      Path impls (c.subst (matchingSubst i.head g.args)) rest target := by
  constructor
  · intro h; cases h with
    | step i c unique position next => exact ⟨i,c,unique,position,next⟩
  · rintro ⟨i,c,unique,position,next⟩; exact .step i c unique position next

/-- Full subtree equality for exactly the independently generated addresses.
This is stronger than a set of visited goals: sibling order and repetition stay. -/
theorem diagnose_follow_exact (impls : List Impl) (wf : WellFormed impls)
    (g : Goal) (path : List Nat) (t : Tree) :
    (diagnose impls wf g).follow path = some t ↔
      ∃ target, Path impls g path target ∧ diagnose impls wf target = t := by
  induction path generalizing g t with
  | nil => simp [Tree.follow,path_nil]
  | cons k rest ih =>
    cases h : candidates impls g with
    | nil =>
      rw [diagnose_missing impls wf g h]
      simp [Tree.follow,Tree.children,path_cons,unique_iff,h]
    | cons i more =>
      cases more with
      | cons j more =>
        rw [diagnose_overlap impls wf g i j more h]
        simp [Tree.follow,Tree.children,path_cons,unique_iff,h]
      | nil =>
        rw [diagnose_selected impls wf g i h]
        simp only [Tree.follow,Tree.children,List.getElem?_map]
        cases hc : i.constraints[k]? with
        | none =>
          simp [path_cons,unique_iff,h,hc]
        | some c =>
          simp only [Option.map_some,Option.bind_some,ih,path_cons]
          constructor
          · rintro ⟨target,next,same⟩
            exact ⟨target,⟨i,c,(unique_iff impls g i).mpr h,hc,next⟩,same⟩
          · rintro ⟨target,⟨j,d,unique,position,next⟩,same⟩
            have ji : j = i := by
              have hu := (unique_iff impls g j).mp unique
              simpa only [h,List.cons.injEq,and_true] using hu.symm
            subst j
            have dc : d = c := Option.some.inj (position.symm.trans hc)
            subst d
            exact ⟨target,next,same⟩

end Yulang.CommonRoleRecursiveDiagnostics
