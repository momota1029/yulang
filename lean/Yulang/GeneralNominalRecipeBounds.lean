import Yulang.GeneralNominalSharedEnumeration

/-! A recipe cannot grow beyond the actual schema's finite origin paths.
This bound is derived from schema membership, independently of any invocation
or source-refinement bound. -/
namespace Yulang.GeneralNominalRecipeBounds
open GeneralNominalOriginTerms GeneralNominalRecursiveInspection
open GeneralNominalMaterialization GeneralNominalSharedEnumeration

def level : Origin → Nat
  | .source _ => 0
  | .nominal parent _ _ | .structural parent _ _ => level parent + 1

theorem project_level (root : Origin) (test : Test) (index : Fin (arity test)) :
    level (project root test index) = level root + 1 := by
  cases test with
  | scalar _ => exact Fin.elim0 index
  | structural | nominal => rfl

def ceiling (body : Schema) : Nat :=
  body.tests.foldr (fun entry rest => max (level entry.1 + 1) rest) 0

theorem test_below (member : entry ∈ body.tests) : level entry.1 < ceiling body := by
  have general (entries : List (Origin × Test)) (member : entry ∈ entries) :
      level entry.1 + 1 ≤ entries.foldr (fun entry rest => max (level entry.1 + 1) rest) 0 := by
    induction entries with
    | nil => cases member
    | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact Nat.le_max_left ..
      · exact Nat.le_trans (ih member) (Nat.le_max_right ..)
  exact general body.tests member

theorem recipe_bounded (recipe : Recipe body root term) (fuel : Nat)
    (below : ∀ entry ∈ body.tests, level entry.1 < level root + fuel) :
    Bounded (body.variables.map Use.name) (body.tests.map Prod.snd) fuel term := by
  induction recipe generalizing fuel with
  | capture root name member => exact .leaf name fuel (List.mem_map.mpr ⟨_,member,rfl⟩)
  | node root test children present recipes ih =>
    have positive := below (root,test) present
    dsimp only at positive
    cases fuel with
    | zero => omega
    | succ fuel =>
      refine .node test children (List.mem_map.mpr ⟨_,present,rfl⟩) (fun index => ih index fuel ?_)
      intro entry member
      have bound := below entry member
      rw [project_level]
      omega

theorem recipe_enumerated (recipe : Recipe body root term) :
    term ∈ enumerate (body.variables.map Use.name) (body.tests.map Prod.snd) (ceiling body) :=
  bounded_enumerated (recipe_bounded recipe (ceiling body) (by
    intro entry member
    have bound := test_below member
    omega))

/-- A semantic recipe certificate contains no hidden unbounded syntax choice:
its expression already belongs to this explicit finite schema-derived list. -/
theorem substituted_bounded (recipe : Recipe body root term)
    (substitution : Nat → Expr α) (bounded : ∀ name ∈ body.variables.map Use.name,
      Bounded leaves (body.tests.map Prod.snd) extra (substitution name)) :
    Bounded leaves (body.tests.map Prod.snd) (ceiling body + extra) (term.bind substitution) :=
  bounded_bind (recipe_bounded recipe _ (by
    intro entry member
    have bound := test_below member
    omega)) substitution bounded

def weight : Expr α → Nat
  | .leaf _ => 1
  | .node _ children => 1 + (List.ofFn (fun index => weight (children index))).sum

def treeBound (branching : Nat) : Nat → Nat
  | 0 => 1
  | depth+1 => 1 + branching * treeBound branching depth

theorem treeBound_pos (branching depth : Nat) : 0 < treeBound branching depth := by
  cases depth <;> simp only [treeBound] <;> omega

theorem sum_ofFn_le (values : Fin count → Nat) (bound : Nat) (bounded : ∀ index, values index ≤ bound) :
    (List.ofFn values).sum ≤ count * bound := by
  induction count with
  | zero => simp
  | succ count ih =>
    rw [List.ofFn_succ,List.sum_cons,Nat.succ_mul]
    have rest := ih (fun index => values index.succ) (fun index => bounded index.succ)
    have first := bounded 0
    omega

theorem weight_bounded (bounded : Bounded leaves tests depth term)
    (arities : ∀ test ∈ tests, arity test ≤ branching) : weight term ≤ treeBound branching depth := by
  induction bounded with
  | leaf name depth member => exact treeBound_pos branching depth
  | node test children member bounded ih =>
    change 1 + _ ≤ 1 + branching * treeBound branching _
    have sum := sum_ofFn_le (fun index => weight (children index)) _ ih
    exact Nat.add_le_add_left (Nat.le_trans sum (Nat.mul_le_mul_right _ (arities test member))) 1

theorem weight_pos (term : Expr α) : 0 < weight term := by
  cases term <;> simp only [weight] <;> omega

theorem weight_depth (bounded : Bounded leaves tests depth term) :
    Bounded leaves tests (weight term) term := by
  have member_le_sum (values : List Nat) {value : Nat} (present : value ∈ values) : value ≤ values.sum := by
    induction values with
    | nil => cases present
    | cons head tail ih =>
      rcases List.mem_cons.mp present with rfl | present
      · simp only [List.sum_cons]; omega
      · have bound := ih present
        simp only [List.sum_cons]; omega
  induction bounded with
  | leaf name depth present => exact .leaf name _ present
  | node test children present bounded ih =>
    simpa only [weight,Nat.add_comm 1] using
      Bounded.node test children present (fun index => bounded_mono (ih index)
        (member_le_sum _ (List.mem_ofFn.mpr ⟨index,rfl⟩)))

theorem weight_bind (term : Expr α) (substitution : α → Expr β) (bound : Nat)
    (positive : 0 < bound) (bounded : ∀ name ∈ term.leaves, weight (substitution name) ≤ bound) :
    weight (term.bind substitution) ≤ weight term * bound := by
  induction term with
  | leaf name => simpa only [Expr.bind,weight,Nat.one_mul] using bounded name (by simp [Expr.leaves])
  | node test children ih =>
    have childrenBound (index : Fin (arity test)) :
        weight ((children index).bind substitution) ≤ weight (children index) * bound := by
      apply ih index
      intro name member
      apply bounded name
      simp only [Expr.leaves,List.mem_flatten,List.mem_ofFn]
      exact ⟨_,⟨index,rfl⟩,member⟩
    have sums (count : Nat) (first last : Fin count → Nat) (each : ∀ index, first index ≤ last index * bound) :
        (List.ofFn first).sum ≤ (List.ofFn last).sum * bound := by
      induction count with
      | zero => simp
      | succ count ih =>
        simp only [List.ofFn_succ,List.sum_cons,Nat.add_mul]
        have rest := ih (fun i => first i.succ) (fun i => last i.succ) (fun i => each i.succ)
        have head := each 0
        omega
    have sum := sums _ _ _ childrenBound
    simp only [Expr.bind,weight,Nat.add_mul,Nat.one_mul]
    omega

theorem recipe_weight (recipe : Recipe body root term)
    (arities : ∀ entry ∈ body.tests, arity entry.2 ≤ branching) :
    weight term ≤ treeBound branching (ceiling body) := by
  apply weight_bounded (recipe_bounded recipe _ ?_) ?_
  · intro entry member
    have bound := test_below member
    omega
  · intro test member
    obtain ⟨entry,present,rfl⟩ := List.mem_map.mp member
    exact arities entry present

end Yulang.GeneralNominalRecipeBounds
