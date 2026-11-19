import Yulang.GeneralRebaseMixedOwnedTrace277
import Yulang.GeneralNominalVersionedMixedProgressSplit236

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseQuietBasis277
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedAdministrative236 (Update Fact Holds monotone)
open GeneralRebaseMixedOwnedTrace277 (Invariant raw)
open GeneralNominalState (sources)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable QuietStep reachable_step same_length_administrative)
variable {roles : Roles.RoleDecls}

def sourceNames (s : State roles) : List Nat := (sources (raw s)).eraseDups

def centerNames (s : State roles) : List Nat :=
    (s.core.sites.map fun site => site.occurrence.identity).eraseDups

def basis (s : State roles) : List Fact :=
  (sourceNames s).map Fact.known ++ (sourceNames s).map Fact.point ++
  ((sourceNames s).flatMap fun l => (sourceNames s).map fun r => Fact.equal l r) ++
  ((centerNames s).flatMap fun l => (centerNames s).map fun r => Fact.alias l r)

def budget (s : State roles) : Nat :=
  (sourceNames s).length + (sourceNames s).length +
    (sourceNames s).length * (sourceNames s).length +
    (centerNames s).length * (centerNames s).length

theorem pair_count {α β γ : Type} (left : List α) (right : List β) (mk : α → β → γ) :
    (left.flatMap fun l => right.map (mk l)).length = left.length * right.length := by
  induction left with
  | nil => simp
  | cons first tail ih =>
    simp [List.flatMap_cons,ih,Nat.add_mul,Nat.add_comm]

theorem basis_count (s : State roles) : (basis s).length = budget s := by
  unfold basis budget
  simp only [List.length_append,List.length_map,pair_count]

theorem source_administrative {a b : State roles} (held : Invariant a) (move : Update a b) :
    sources (raw b) ⊆ sources (raw a) := by
  cases move with
  | refresh context cert => exact cert.support
  | reobserve => exact fun _ member => member
  | equate first last one two =>
    exact GeneralNominalCenteredHeadMatStepEnumeration.equate_sources (before := a.core.erased.current) one two
  | merge first last one two =>
    exact GeneralNominalCenteredEnumeration.merge_sources (before := a.core.erased.current)
      (fun _ member => member) (held.outputs first one) (held.outputs last two)

theorem advances {start a b : State roles} (same : a.core.sites = start.core.sites)
    (within : sources (raw a) ⊆ sources (raw start)) (action : Update a b) :
    ∃ fact ∈ basis start, ¬ Holds a fact ∧ Holds b fact := by
  have sourceAt {id} (seen : id ∈ sources (raw a)) : id ∈ sourceNames start := by
    unfold sourceNames
    exact List.mem_eraseDups.mpr (within seen)
  have centerAt {site : Site roles} (seen : site ∈ a.core.sites) :
      site.occurrence.identity ∈ centerNames start := by
    unfold centerNames
    exact List.mem_eraseDups.mpr (List.mem_map.mpr ⟨site,same ▸ seen,rfl⟩)
  cases action with
  | refresh ctx cert id tracked old now =>
    refine ⟨.known id,?_,old,now⟩
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.mpr ⟨id,sourceAt tracked,rfl⟩)))
  | reobserve revision cert improves =>
    obtain ⟨slot,old,now⟩ := improves.2
    have source := sourceAt (GeneralNominalAllocationSupport.slot_source (raw a) slot)
    refine ⟨.point ((raw a).base.source slot),?_,?_,slot,rfl,now⟩
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.mpr ⟨_,source,rfl⟩)))
    · rintro ⟨other,equal,seen⟩
      have sameSlot := (raw a).base.source_injective equal
      exact old (sameSlot ▸ seen)
  | equate first last one two equal novel =>
    refine ⟨.equal first last,?_,novel,GeneralNominalFeedbackSteps.equate_feedback _ _ _⟩
    exact List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨first,sourceAt one,List.mem_map.mpr ⟨last,sourceAt two,rfl⟩⟩))
  | merge first last one two equal novel =>
    refine ⟨.alias first.occurrence.identity last.occurrence.identity,?_,novel,
      GeneralNominalCycleSteps.merged_inputs _ first.observed last.observed⟩
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨_,centerAt one,
      List.mem_map.mpr ⟨_,centerAt two,rfl⟩⟩)

end Yulang.GeneralRebaseQuietBasis277
