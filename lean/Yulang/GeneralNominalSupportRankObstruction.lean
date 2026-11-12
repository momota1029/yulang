import Yulang.GeneralNominalSupportSiblings

/-! The union of all permitted external producers is not a support order,
even on two generated unresolved siblings in a formed state. This refutes
ranking every allowed edge. The sibling singleton supports here are redundant;
no necessary head support or infinite installation trace is claimed. -/
namespace Yulang.GeneralNominalSupportRankObstruction

open GeneralNominalSupportSiblings GeneralNominalSupport GeneralNominalSupportSteps
open GeneralNominalSaturationState GeneralSourceDictionaries
open GeneralDeclarationExamples (roles)
local instance : NeZero src.base.slots := ⟨by change 1+2 ≠ 0; omega⟩

private theorem alias_identity {first last : Nat} (related : Alias afterP.current first last) : first = last := by
  induction related with
  | refl => rfl
  | edge member => cases member
  | symm _ ih => exact ih.symm
  | trans _ _ one two => exact one.trans two

private theorem child_above (clause : GeneralDeclarations.Clause) (signature : clause.Signature roles) :
    root.identity < (GeneralNominalFeedbackSites.clauseChild pk clause signature).identity :=
  GeneralNominalIdentities.source_above_invocation src.seed
    (GeneralNominalAllocation.origin root.identity p.id 6 clause.id 0)

private theorem siblings_distinct : kidC.identity ≠ kidW.identity := by
  intro equal
  have same := (GeneralNominalIdentities.source_identity src.seed
    (GeneralNominalAllocation.origin root.identity p.id 6 cp.id 0)
    (GeneralNominalAllocation.origin root.identity p.id 6 wp.id 0)).mp equal
  have impossible : (100 : Nat) = 102 := congrArg (fun key => key.2.2.2.1) same
  cases impossible

theorem sibling_generated_identity (first last : Occurrence roles) (above : root.identity < first.identity)
    (reached : Generated afterP.current first last) : last.identity = first.identity := by
  induction reached with
  | root => rfl
  | child reached member ih =>
    change (_,_) ∈ [] ++ pk.children.map _ at member
    obtain ⟨child,_,equal⟩ := List.mem_map.mp member
    have parent := congrArg Prod.fst equal
    change root = _ at parent
    have impossible := (congrArg Occurrence.identity parent).trans ih
    omega
  | alias reached one two related ih => exact (alias_identity related).symm.trans ih

theorem siblings_external : External afterP.current kidC kidW ∧ External afterP.current kidW kidC := by
  constructor
  · right
    intro reached
    exact siblings_distinct (sibling_generated_identity kidW kidC (child_above wp sigW) reached)
  · right
    intro reached
    exact siblings_distinct (sibling_generated_identity kidC kidW (child_above cp sigC) reached).symm

theorem siblings_unresolved (focus : Occurrence roles) : ¬ Discharged afterP.current focus := by
  apply GeneralNominalSupportGrowth.no_leaves_no_discharge
  intro packet member
  have same : packet = pk := List.mem_singleton.mp member
  subst packet
  rw [p_children]
  simp

theorem sibling_heads_source_supported : Roots afterP [] kidC ∧ Roots afterP [] kidW ∧ Roots afterP [] kidP := by
  let descriptor := GeneralNominalOutputGrowthModels.descriptor 1 (1 : Fin src.base.slots) (Nat.le_refl _)
  have original : Head src 1 (.nominal 0 1) (.nominal src.base 1 descriptor) :=
    Head.nominal (snapshot := src) 1 descriptor rfl
  have current : Head afterP.current.context.state 1 (.nominal 0 1) (.nominal src.base 1 descriptor) :=
    Head.nominal (snapshot := afterP.current.context.state) (1 : Fin src.base.slots) descriptor rfl
  have ready : ReadyAt afterP [] 1 := source_ready afterP 1 _ _ _ original current []
  refine ⟨?_,?_,?_⟩
  · intro index
    rw [child_inputs.1 index]
    exact ready
  · intro index
    rw [child_inputs.2.1 index]
    exact ready
  · intro index
    rw [child_inputs.2.2 index]
    exact ready

/-- This relation includes every permitted producer, not only producers used
by a minimal explanation of a needed input head. -/
def Permitted (state : Tracked roles) (root producer focus : Occurrence roles) : Prop :=
  Generated state.current root producer ∧ Generated state.current root focus ∧
    ¬ Discharged state.current producer ∧ ¬ Discharged state.current focus ∧
      Admissible state focus [producer]

theorem sibling_cycle : Permitted afterP root kidC kidW ∧ Permitted afterP root kidW kidC := by
  refine ⟨⟨children_generated.1,children_generated.2.1,siblings_unresolved _,siblings_unresolved _,?_⟩,
    ⟨children_generated.2.1,children_generated.1,siblings_unresolved _,siblings_unresolved _,?_⟩⟩
  · intro producer member
    have same := List.mem_singleton.mp member
    subst producer
    exact siblings_external.2
  · intro producer member
    have same := List.mem_singleton.mp member
    subst producer
    exact siblings_external.1

theorem permitted_not_accessible : ¬ Acc (Permitted afterP root) kidC := by
  have impossible : ∀ focus, Acc (Permitted afterP root) focus → focus = kidC ∨ focus = kidW → False := by
    intro focus accessible
    induction accessible with
    | intro focus below ih =>
      rintro (rfl | rfl)
      · exact ih kidW sibling_cycle.2 (Or.inr rfl)
      · exact ih kidC sibling_cycle.1 (Or.inl rfl)
  exact fun accessible => impossible kidC accessible (Or.inl rfl)

theorem no_permitted_rank {Measure : Type u} (less : Measure → Measure → Prop)
    (wellFounded : WellFounded less) (rank : Occurrence roles → Measure) :
    ¬ (∀ producer focus, Permitted afterP root producer focus → less (rank producer) (rank focus)) := by
  intro decreases
  have lift : ∀ value, Acc less value → ∀ focus, rank focus = value → Acc (Permitted afterP root) focus := by
    intro value accessible
    induction accessible with
    | intro value below ih =>
      intro focus equal
      refine Acc.intro focus ?_
      intro producer edge
      exact ih (rank producer) (equal ▸ decreases producer focus edge) producer rfl
  exact permitted_not_accessible (lift (rank kidC) (wellFounded.apply _) kidC rfl)

end Yulang.GeneralNominalSupportRankObstruction
