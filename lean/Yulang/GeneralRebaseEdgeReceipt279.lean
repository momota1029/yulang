import Yulang.GeneralRebaseOccurrenceCode279

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseEdgeReceipt279
open GeneralSourceDictionaries (Occurrence)
open GeneralDeclarations GeneralNominalCenters
open GeneralRebaseInstallNovelty279 (Edge FreshChild Covered)
open GeneralRebaseOccurrenceCode279 (OccurrenceCode codeEdge edgeCode_injective)
open GeneralNominalVersionedChildren232 (edges edge_iff)
open GeneralNominalVersionedJournal232 (State Effect)

def edgeKnown (recorded : List (Edge roles)) (edge : Edge roles) : Bool :=
  (recorded.map codeEdge).contains (codeEdge edge)

theorem edgeKnown_exact (recorded : List (Edge roles)) (edge : Edge roles) :
    edgeKnown recorded edge = true ↔ edge ∈ recorded := by
  simp only [edgeKnown,List.contains_iff_mem,List.mem_map]
  constructor
  · rintro ⟨e,mem,equal⟩
    exact (edgeCode_injective _ _ equal) ▸ mem
  · intro mem
    exact ⟨edge,mem,rfl⟩

def freshEdges (recorded prospective : List (Edge roles)) : List (Edge roles) :=
  prospective.filter fun edge => !edgeKnown recorded edge

theorem mem_freshEdges (recorded prospective : List (Edge roles)) (edge : Edge roles) :
    edge ∈ freshEdges recorded prospective ↔ edge ∈ prospective ∧ edge ∉ recorded := by
  simp only [freshEdges,List.mem_filter,Bool.not_eq_true',← Bool.not_eq_true,
    edgeKnown_exact]

def receipt (state : State roles) (plan : Plan roles) : List (Edge roles) :=
  freshEdges state.core.erased.current.edges (edges plan)

theorem receipt_exact (state : State roles) (effect : Effect roles) (edge : Edge roles) :
    edge ∈ receipt state effect.plan ↔
      edge ∈ (GeneralNominalVersionedInstall232.install state effect).core.erased.current.edges ∧
        edge ∉ state.core.erased.current.edges :=
  (mem_freshEdges ..).trans (GeneralRebaseInstallNovelty279.edge_exact state effect edge).symm

theorem receipt_retains_order (state : State roles) (plan : Plan roles) :
    (receipt state plan).Sublist (edges plan) :=
  List.filter_sublist

theorem receipt_some_iff (state : State roles) (effect : Effect roles) :
    receipt state effect.plan ≠ [] ↔ FreshChild state effect.plan := by
  rw [GeneralRebaseInstallNovelty279.fresh_iff_edge state effect]
  constructor
  · intro nonempty
    cases list : receipt state effect.plan with
    | nil => exact False.elim (nonempty list)
    | cons edge rest =>
      have member : edge ∈ receipt state effect.plan := list ▸ List.mem_cons_self ..
      exact ⟨edge,(receipt_exact state effect edge).mp member⟩
  · rintro ⟨edge,step⟩ empty
    have member := (receipt_exact state effect edge).mpr step
    rw [empty] at member
    cases member

theorem receipt_empty_iff (state : State roles) (effect : Effect roles) :
    receipt state effect.plan = [] ↔ Covered state effect.plan := by
  classical
  constructor
  · intro empty
    by_cases covers : Covered state effect.plan
    · exact covers
    · exact False.elim (((receipt_some_iff state effect).mpr
        ((GeneralRebaseInstallNovelty279.not_covered state effect.plan).mp covers)) empty)
  · intro covers
    by_cases empty : receipt state effect.plan = []
    · exact empty
    · exact False.elim (((GeneralRebaseInstallNovelty279.not_covered state effect.plan).mpr
        ((receipt_some_iff state effect).mp empty)) covers)

theorem append_delta_membership (recorded prospective : List (Edge roles)) (edge : Edge roles) :
    edge ∈ recorded ++ freshEdges recorded prospective ↔ edge ∈ recorded ++ prospective := by
  simp only [List.mem_append, mem_freshEdges]
  classical
  by_cases already : edge ∈ recorded <;> simp [already]

end Yulang.GeneralRebaseEdgeReceipt279
