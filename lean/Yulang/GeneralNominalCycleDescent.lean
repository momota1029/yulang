import Yulang.GeneralNominalCycleEdges

/-! Removing outgoing edges at cyclic nodes yields a finite well-founded
inspection graph, even when a noncyclic root has cyclic descendants. The rank
is derived from the complete finite slot set, not supplied as fuel. Connecting
this graph abstraction to captured declaration patterns remains separate. -/
namespace Yulang.GeneralNominalCycleDescent

open GeneralNominalCycleK2

noncomputable section
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable (state : GeneralNominalState.State)

def CutEdge (first last : Fin state.base.slots) : Prop := ¬ Cycle state first ∧ Edge state first last

inductive CutPath : Fin state.base.slots → Fin state.base.slots → Prop
  | nil (root) : CutPath root root
  | cons : CutEdge state first middle → CutPath middle last → CutPath first last

theorem path_original (path : CutPath state first last) : Path state first last := by
  induction path with
  | nil => exact .nil _
  | cons edge _ ih => exact .cons edge.2 ih

theorem path_trans (first : CutPath state a b) (last : CutPath state b c) : CutPath state a c := by
  induction first with
  | nil => exact last
  | cons edge path ih => exact .cons edge (ih last)

def reached (source : Fin state.base.slots) : List (Fin state.base.slots) :=
  (List.finRange state.base.slots).filter fun target => decide (CutPath state source target)

theorem mem_reached (source target : Fin state.base.slots) : target ∈ reached state source ↔ CutPath state source target := by
  simp [reached]

def rank (source : Fin state.base.slots) : Nat := (reached state source).length

theorem rank_bounded (source : Fin state.base.slots) : rank state source ≤ state.base.slots := by
  simpa [rank,reached] using List.length_filter_le
    (fun target => decide (CutPath state source target)) (List.finRange state.base.slots)

theorem rank_decreases (source target : Fin state.base.slots) (edge : CutEdge state source target) :
    rank state target < rank state source := by
  have absent : source ∉ reached state target := by
    intro member
    exact edge.1 ⟨target,edge.2,path_original state ((mem_reached state target source).mp member)⟩
  have distinct : (source :: reached state target).Nodup :=
    List.nodup_cons.mpr ⟨absent,(List.nodup_finRange state.base.slots).filter _⟩
  have included : source :: reached state target ⊆ reached state source := by
    intro node member
    rcases List.mem_cons.mp member with rfl | later
    · exact (mem_reached state _ _).mpr (.nil _)
    · exact (mem_reached state source node).mpr (.cons edge ((mem_reached state target node).mp later))
  have sizes := distinct.length_le_of_subset included
  simp only [List.length_cons] at sizes
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) sizes

theorem cut_accessible (root : Fin state.base.slots) : Acc (fun child parent => CutEdge state parent child) root := by
  induction root using (measure (rank state)).wf.induction with
  | h root ih =>
    refine Acc.intro root ?_
    intro child edge
    exact ih child (rank_decreases state root child edge)

theorem cyclic_leaf (root : Fin state.base.slots) (cycle : Cycle state root) :
    ∀ child, ¬ CutEdge state root child := fun _ edge => edge.1 cycle

/-- A ready, non-K2 demand has strictly decreasing outgoing graph edges at
its unnamed lower roots, provided the semantic edge interpretation has a model. -/
theorem root_edge_decreases (demand : GeneralSourceState.Demand roles)
    (linked : GeneralNominalState.Linked state demand) (ready : ¬ GeneralNominalState.RootPending state demand)
    (safe : ¬ RootK2 state demand) (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state model) (index : Fin (roles demand.role).arity)
    (root child : Fin state.base.slots) (source : state.base.source root = (demand.arguments index).1)
    (edge : Edge state root child) : rank state child < rank state root :=
  rank_decreases state root child ⟨fun cycle => safe (cycle_rejects state demand linked ready index root source cycle model valid),edge⟩

/-- The same derived rank applies to each constructor position inspected by a
candidate whose K2 check is clear. This does not assert capture/emission readback. -/
theorem inspected_edge_decreases (registry : GeneralDeclarations.Registry)
    (context : GeneralNominalCandidates.Context) (root : GeneralSourceDictionaries.Occurrence roles)
    (ready : ¬ GeneralNominalState.RootPending context.state root.demand)
    (safe : ¬ CandidateK2 registry context root) (declaration : GeneralDeclarations.Declaration)
    (visible : declaration ∈ registry.declarations)
    (checked : GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
    (role : declaration.role = root.demand.role)
    (head : GeneralNominalRecursiveCandidates.HeadReady registry context root declaration)
    (bounds : List (GeneralNominalInspection.Bounds context.state))
    (located : GeneralNominalRecursiveCandidates.arguments context root = some bounds)
    (visited : GeneralNominalInspection.Bounds context.state)
    (member : visited ∈ (GeneralNominalRecursiveCandidates.report context declaration bounds).inspected)
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models context.state model)
    (child : Fin context.state.base.slots) (edge : Edge context.state visited.1 child) :
    rank context.state child < rank context.state visited.1 := by
  apply rank_decreases context.state visited.1 child
  refine ⟨?_,edge⟩
  intro cycle
  exact safe ⟨ready,declaration,visible,checked,role,head,bounds,located,visited,member,Or.inr ⟨cycle,model,valid⟩⟩

end
end Yulang.GeneralNominalCycleDescent
