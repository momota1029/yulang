import Yulang.GeneralDictionaryGroundCopy218Obstruction
import Yulang.GeneralDictionaryGroundCopy218Leaf

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDictionaryGroundCopy218Stability
open GeneralDictionaryGroundCopy218Source GeneralDictionaryGroundCopy218Install
open GeneralDictionaryGroundCopy218Reobserve GeneralDictionaryGroundCopy218Obstruction
open GeneralNominalCenters GeneralNominalRecursiveInspection CommonNominalFullCarrier
open GeneralDictionaryInspectionHeads215
open GeneralNominalCenteredHeadMatStepJournal
open GeneralDictionaryGroundCopy218Leaf (oldChild childId lo hi)
variable {atoms : List (PresenceNormalForm.Atom Nat)}

abbrev current (atoms : List (PresenceNormalForm.Atom Nat)) :=
  pointExtended installedAllocation installedReservation atoms

def Owned (identity : Nat) : Prop := identity ≤ 7 ∨
  ∃ key : GeneralNominalIdentities.Origin, key.1 = 0 ∧ GeneralNominalIdentities.source 7 key = identity

def Supported (atoms : List (PresenceNormalForm.Atom Nat)) : Prop :=
  ∀ identity ∈ atoms.flatMap GeneralNominalState.atomSources, Owned identity

theorem declaration_invocation {declaration : GeneralDeclarations.Declaration} (member : key ∈ GeneralNominalAllocation.declarationKeys invocation declaration) :
    key.1 = invocation := by
  simp only [GeneralNominalAllocation.declarationKeys,List.mem_append,List.mem_flatMap,List.mem_map,
    List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with (⟨name,_,rfl | rfl⟩ | ⟨name,_,rfl⟩) |
    ⟨clause,_,(rfl | ⟨index,_,rfl | rfl⟩) | ⟨equation,_,rfl⟩⟩
  all_goals rfl

theorem key_invocation (member : key ∈ GeneralNominalAllocation.keys value invocation) : key.1 = invocation := by
  obtain ⟨declaration,_,member⟩ := List.mem_flatMap.mp member
  exact declaration_invocation member

theorem source_owned (supported : Supported atoms)
    (member : identity ∈ GeneralNominalState.sources (current atoms)) : Owned identity := by
  simp only [GeneralNominalState.sources,List.mem_append] at member
  rcases member with ((type | row) | reserved) | ordinary
  · obtain ⟨slot,equal⟩ := List.mem_ofFn.mp type
    change Fin 8 at slot
    change slot.val = identity at equal
    exact Or.inl (by have bound := slot.isLt; omega)
  · obtain ⟨slot,equal⟩ := List.mem_ofFn.mp row
    change Fin 8 at slot
    change slot.val = identity at equal
    exact Or.inl (by have bound := slot.isLt; omega)
  · change identity ∈ ([] ++ GeneralNominalAllocation.reserved snapshot registry root.identity) ++ [] at reserved
    simp only [List.nil_append,List.append_nil] at reserved
    obtain ⟨key,member,equal⟩ := List.mem_map.mp reserved
    exact Or.inr ⟨key,key_invocation member,equal⟩
  · exact supported identity ordinary

theorem supported_initial : Supported initialAtoms := by
  have ordinary : initialAtoms =
      [.tyLe (.var 2) (.var 3),.tyLe (.var 2) (.var 3),
       .tyLe (.var 6) (.var 6),.tyLe (.var 6) (.var 6),
       .tyLe (.var 2) (.var 3),.tyLe (.var 2) (.var 3)] := by
    change (GeneralNominalRecursiveCandidates.privateState registry context root declaration [(6,6)]).ordinary = _
    unfold GeneralNominalRecursiveCandidates.privateState
    rw [report_exact]
    rfl
  intro identity member
  rw [ordinary] at member
  change identity ∈ [2,3,2,3,6,6,6,6,2,3,2,3] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  exact Or.inl (by omega)

theorem supported_equate (supported : Supported atoms)
    (one : first ∈ GeneralNominalState.sources (current atoms))
    (two : last ∈ GeneralNominalState.sources (current atoms)) :
    Supported (atoms ++ GeneralNominalAllocation.equations first (.var last)) := by
  intro identity member
  rw [List.flatMap_append] at member
  rcases List.mem_append.mp member with prior | fresh
  · exact supported identity prior
  · change identity ∈ [first,last,last,first] at fresh
    simp only [List.mem_cons,List.not_mem_nil,or_false] at fresh
    rcases fresh with rfl | rfl | rfl | rfl
    · exact source_owned supported one
    · exact source_owned supported two
    · exact source_owned supported two
    · exact source_owned supported one

theorem child_positive : 0 < childId := GeneralNominalIdentities.source_above_invocation 7 (0,0,6,0,0)

theorem owned_not_child (owned : Owned identity) (key : GeneralNominalIdentities.Origin)
    (invocation : key.1 = childId) : identity ≠ GeneralNominalIdentities.source 7 key := by
  intro equal
  rcases owned with small | ⟨prior,zero,found⟩
  · have above := GeneralNominalIdentities.source_above_seed 7 key
    omega
  · have same := (GeneralNominalIdentities.source_identity 7 _ _).mp (found.trans equal)
    have first := congrArg Prod.fst same
    have positive := child_positive
    omega

theorem missing (supported : Supported atoms) :
    ∀ identity ∈ GeneralNominalState.sources (current atoms), identity ≠ lo ∧ identity ≠ hi := by
  intro identity member
  exact ⟨owned_not_child (source_owned supported member) (childId,1,0,0,0) rfl,
    owned_not_child (source_owned supported member) (childId,1,1,0,0) rfl⟩

theorem fresh (supported : Supported atoms) : GeneralNominalAllocation.Fresh (current atoms) registry childId := by
  intro key member collision
  exact False.elim (owned_not_child (source_owned supported collision) key (key_invocation member) rfl)

theorem raw_edge_decreases (held : PresenceNormalForm.All CommonNominalFullCarrier.model model atoms)
    {a b : Fin 8} (edge : GeneralNominalMixedRecurrence.Edge (current atoms) a b) :
    (sourceForm b.val).rank < (sourceForm a.val).rank := by
  rcases edge with structural | nominal
  · obtain ⟨kind,children,recorded,index,child⟩ := structural
    change (if a = 2 then .structural 0 (fun _ => 0) else if a = 3 then .structural 0 (fun _ => 1) else
      .deferred .unresolved : GeneralNormalizedObservation.Head view.shapes 8) = .structural kind children at recorded
    split at recorded
    · rename_i equal; subst a
      cases recorded
      have zero : b = 0 := child.symm
      subst b
      change 0 < 1; decide
    · split at recorded
      · rename_i equal; subst a
        cases recorded
        have one : b = 1 := child.symm
        subst b
        change 0 < 1; decide
      · cases recorded
  · obtain ⟨descriptor,recorded,index,actual,seen,same⟩ :=
      GeneralNominalMixedRecurrence.actual_edge_sound (current atoms) a b nominal model (model_if_atoms atoms held).1
    have observation := embed_observation model _ actual seen
    cases observation with
    | nominal parent equal found =>
      cases parent
      have firstValue : (model a.val).1 = (sourceForm a.val).value :=
        (model_small a.val (by omega)).trans (source_form a.val)
      have lastValue : (model b.val).1 = (sourceForm b.val).value :=
        (model_small b.val (by omega)).trans (source_form b.val)
      rw [firstValue] at equal
      obtain ⟨child,smaller,meaning⟩ := GeneralDictionaryGroundCopy218Cycles.nominal_child
        (sourceForm a.val) equal found
      rw [lastValue] at same
      have rankEq := GeneralDictionaryGroundCopy218Cycles.equivalent_rank child (sourceForm b.val)
        ⟨subtype_trans meaning.2 same.1,subtype_trans same.2 meaning.1⟩
      omega

theorem no_raw_recurs (held : PresenceNormalForm.All CommonNominalFullCarrier.model model atoms)
    (slot : Fin 8) : ¬ GeneralNominalCycleK2.RecursAt (current atoms) slot := by
  have paths : ∀ a b, GeneralNominalMixedRecurrence.Path (current atoms) a b →
      (sourceForm b.val).rank ≤ (sourceForm a.val).rank := by
    intro a b path
    induction path with
    | nil => exact Nat.le_refl _
    | cons edge path ih => exact Nat.le_trans ih (Nat.le_of_lt (raw_edge_decreases held edge))
  intro cycle
  obtain ⟨next,edge,path⟩ := GeneralNominalCycleK2.recurs_cycle _ _ cycle
  have smaller := raw_edge_decreases held edge
  have larger := paths _ _ path
  omega

theorem no_reobserve (revision : GeneralNominalReobservationSteps.Revision (stage atoms).core.erased.current) :
    ¬ GeneralNominalReobservationSteps.Improves revision :=
  GeneralNominalReobservationSteps.pointClosed_no_revision
    (point_closed installedAllocation installedReservation atoms) revision

theorem source_no_scalar (identity : Nat) (scalar : Inference.Base) :
    ¬ Equivalent (sourceValue identity) (.base scalar) := by
  rcases identity with _ | (_ | (_ | (_ | (_ | (_ | (_ | (_ | identity)))))))
  all_goals intro equal
  all_goals first
    | exact GeneralNominalCenteredHeadMatHeadShape.bottom_no_head (.scalar scalar) equal
    | exact GeneralDictionaryGroundCopy218Refresh.top_no_head (.scalar scalar) equal
    | have tags := tag_subtype
        (show Tagged _ (.variant 0) from by intro env; rfl) (tagged_scalar scalar) equal.1
      cases tags
    | have tags := tag_subtype (tagged_nominal 5 _) (tagged_scalar scalar) equal.1
      cases tags

theorem model_no_scalar (identity : Nat) (scalar : Inference.Base) :
    ¬ Equivalent (model identity).1 (.base scalar) := by
  unfold GeneralDictionaryGroundCopy218Install.model
  split
  · intro equal
    have tags := tag_subtype
      (show Tagged GeneralDictionaryLooseVariant217.first (.variant 0) from by intro env; rfl)
      (tagged_scalar scalar) equal.1
    cases tags
  · split
    · intro equal
      have tags := tag_subtype
        (show Tagged GeneralDictionaryLooseVariant217.second (.variant 0) from by intro env; rfl)
        (tagged_scalar scalar) equal.1
      cases tags
    · exact source_no_scalar identity scalar

theorem unknown_shape (unknown : ¬ GeneralNominalState.Known (current atoms) identity) :
    (model identity).1 = .bottom ∨ (model identity).1 = .top ∨
      ∃ scalar, (model identity).1 = variant 0 (.base scalar) ∧
        ∀ source, ¬ Equivalent (model source).1 (.base scalar) := by
  by_cases a : identity = GeneralNominalCenters.fresh 7 0 0 8 0 0
  · exact Or.inr (Or.inr ⟨.int,by simp only [GeneralDictionaryGroundCopy218Install.model,ite_eq_left a]; rfl,fun source => model_no_scalar source .int⟩)
  by_cases b : identity = GeneralNominalCenters.fresh 7 0 0 8 1 0
  · exact Or.inr (Or.inr ⟨.bool,by simp only [GeneralDictionaryGroundCopy218Install.model,ite_eq_right a,ite_eq_left b]; rfl,fun source => model_no_scalar source .bool⟩)
  have value : (model identity).1 = sourceValue identity := by simp [GeneralDictionaryGroundCopy218Install.model,a,b]
  have two : identity ≠ 2 := by
    rintro rfl
    exact unknown ⟨(2 : Fin 8),rfl,Or.inl (by intro h; cases h)⟩
  have three : identity ≠ 3 := by
    rintro rfl
    exact unknown ⟨(3 : Fin 8),rfl,Or.inl (by intro h; cases h)⟩
  have six : identity ≠ 6 := by
    rintro rfl
    exact unknown ⟨(6 : Fin 8),rfl,Or.inr ⟨exactCopy,rfl⟩⟩
  have seven : identity ≠ 7 := by
    rintro rfl
    exact unknown ⟨(7 : Fin 8),rfl,Or.inr ⟨exactCopy,rfl⟩⟩
  rcases identity with _ | (_ | (_ | (_ | (_ | (_ | (_ | (_ | identity)))))))
  · exact Or.inl value
  · exact Or.inr (Or.inl value)
  · exact False.elim (two rfl)
  · exact False.elim (three rfl)
  · exact Or.inr (Or.inr ⟨.int,value,fun source => model_no_scalar source .int⟩)
  · exact Or.inr (Or.inr ⟨.bool,value,fun source => model_no_scalar source .bool⟩)
  · exact False.elim (six rfl)
  · exact False.elim (seven rfl)
  · exact Or.inl value

theorem no_refresh (held : PresenceNormalForm.All CommonNominalFullCarrier.model model atoms)
    (certificate : GeneralNominalCenteredHeadMatStepRefresh.Refresh (stage atoms) nextContext)
    (unknown : ¬ GeneralNominalState.Known (current atoms) identity)
    (known : GeneralNominalState.Known nextContext.state identity) : False :=
  GeneralDictionaryGroundCopy218Refresh.no_new_head (stage atoms) model (model_if_atoms atoms held)
    nextContext.state certificate.cache identity (unknown_shape unknown) known

end Yulang.GeneralDictionaryGroundCopy218Stability
