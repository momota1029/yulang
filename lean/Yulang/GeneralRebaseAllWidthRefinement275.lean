import Yulang.GeneralRebaseAllWidthRegistration275

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 14000
set_option maxHeartbeats 5500000
namespace Yulang.GeneralRebaseAllWidthRefinement275
open Core.PresenceGeneration (TyTerm)
open GeneralSourceState (equationAtoms)
open GeneralRebaseAllWidthRegistration275
open GeneralRebaseTerminalMixedRefresh274 (raw widthCandidates candidates_tracked)
open GeneralDictionaryJournalRefinement228Reobserve (pointSnapshot exactCopy)
open GeneralNominalRefinements (renameDescriptor)
open GeneralNominalState (Known sources)

def descriptor : GeneralNominalState.Descriptor 8 := renameDescriptor embed exactCopy
def nominals (slot : Fin 8) : Option (GeneralNominalState.Descriptor 8) :=
 if slot = 0 ∨ slot = 1 then some descriptor else none

theorem nominal_at (slot : Fin 8) (d : GeneralNominalState.Descriptor 8)
 (seen : nominals slot = some d) : (slot = 0 ∨ slot = 1) ∧ d = descriptor := by
 unfold nominals at seen
 split at seen
 · exact ⟨‹_›,(Option.some.inj seen).symm⟩
 · cases seen

noncomputable def snapshot : GeneralNominalState.State where
 base := base
 view := view
 constructors := raw.constructors
 nominals := nominals
 catalogue := by
  intro slot d seen
  obtain ⟨_,rfl⟩ := nominal_at slot d seen
  rfl
 bodies_opaque := by
  intro slot d seen
  obtain ⟨h,_⟩ := nominal_at slot d seen
  rcases h with rfl|rfl <;> rfl
 seed := raw.seed
 allocated := raw.allocated
 reserved := raw.reserved
 ordinary := raw.ordinary

theorem emb_nominal : ∀ slot : Fin 5, (embed slot = 0 ∨ embed slot = 1) ↔ (slot = 0 ∨ slot = 1) := by
 decide +kernel

theorem raw_equation (slot : Fin 5) (term : TyTerm (Fin 5))
 (seen : (raw.base.heads slot).equation = some term) : slot = 2 ∧ term = .emptyRecord := by
 change ((GeneralDictionaryJournalRefinement228Source.base.heads slot).equation = some term) at seen
 by_cases two : slot = 2
 · subst slot
   exact ⟨rfl,(Option.some.inj seen).symm⟩
 · simp [GeneralDictionaryJournalRefinement228Source.base,two,GeneralSourceState.Head.equation] at seen

theorem retain_atom (atom : PresenceNormalForm.Atom (Fin 5)) (member : atom ∈ raw.base.ordinary) :
 atom.rename embed ∈ atoms := by
 change atom ∈ equationAtoms 0 (.var 1) ++ equationAtoms 2 .emptyRecord ++
   equationAtoms 3 .top ++ [.tyLe (.var 4) (.var 2)] at member
 simp only [equationAtoms,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with (((rfl|rfl)|(rfl|rfl))|(rfl|rfl))|rfl
 all_goals simp only [PresenceNormalForm.Atom.rename,TyTerm.rename,atoms,equationAtoms,List.mem_append,
   List.mem_cons,List.not_mem_nil,or_false]
 all_goals decide +kernel

theorem keep_nominal (slot : Fin 5) (d : GeneralNominalState.Descriptor 5)
 (seen : raw.nominals slot = some d) :
 snapshot.nominals (embed slot) = some (renameDescriptor embed d) := by
 change (if slot = 0 ∨ slot = 1 then some exactCopy else none) = some d at seen
 split at seen
 · cases Option.some.inj seen
   exact ite_eq_left ((emb_nominal slot).mpr ‹_›)
 · cases seen

theorem raw_graph_two (slot : Fin 5) (known : raw.base.graph slot ≠ .unresolved) : slot = 2 := by
 by_cases two : slot = 2
 · exact two
 exfalso
 apply known
 change GeneralDictionaryJournalRefinement228Source.base.graph slot = .unresolved
 simp [GeneralSourceState.State.graph,GeneralDictionaryJournalRefinement228Source.base,two,GeneralSourceState.Head.node]

theorem view_graph_two (slot : Fin 5) (known : raw.view.graph slot ≠ .unresolved) : slot = 2 := by
 by_cases two : slot = 2
 · exact two
 exfalso
 apply known
 change GeneralDictionaryJournalRefinement228Source.view.graph slot = .unresolved
 simp [GeneralNormalizedObservation.Snapshot.graph,
   two,GeneralNormalizedObservation.Head.node]

noncomputable def refines :
 GeneralNominalRefinements.Refines raw snapshot where
 base := {
  embed := embed
  source := source_embed
  rowSource := row_embed
  ordinary := retain_atom
  known := by
   intro slot known
   have two := raw_graph_two slot known
   subst slot
   intro never
   cases never
  intervals := by intro _ impossible; cases impossible }
 heads := by
  intro slot term seen
  obtain ⟨rfl,rfl⟩ := raw_equation slot term seen
  exact .head rfl
 nominals := keep_nominal
 ordinary := fun _ present => present
 known := by
  rintro uid ⟨slot,equal,head|⟨d,seen⟩⟩
  · refine ⟨embed slot,(source_embed slot).trans equal,Or.inl ?_⟩
    have two := view_graph_two slot head
    subst slot
    intro never
    cases never
  · exact ⟨embed slot,(source_embed slot).trans equal,Or.inr ⟨_,keep_nominal slot d seen⟩⟩
 reserved := fun _ present => present
 allocated := fun _ present => present
 seed := rfl
 constructors := rfl

open GeneralDictionaryVersionedSecondRaw233 (oldHi newLo newHi)
theorem source_covered :
 ∀ slot : Fin 8, (∃ prev : Fin 5, source slot = prev.val) ∨ source slot ∈ widthCandidates := by
 decide +kernel

theorem row_covered : ∀ slot : Fin 8, ∃ prev : Fin 5, rows slot = prev.val := by
 decide +kernel

theorem support : ∀ name ∈ sources snapshot, name ∈ sources raw := by
 intro name present
 simp only [sources,List.mem_append] at present ⊢
 rcases present with ((type|row)|reserved)|ordinary
 · obtain ⟨slot,equal⟩ := List.mem_ofFn.mp type
   rcases source_covered slot with ⟨prev,same⟩|tracked
   · exact Or.inl (Or.inl (Or.inl (List.mem_ofFn.mpr ⟨prev,same.symm.trans equal⟩)))
   · simpa only [sources,List.mem_append] using candidates_tracked name (equal ▸ tracked)
 · obtain ⟨slot,equal⟩ := List.mem_ofFn.mp row
   obtain ⟨prev,same⟩ := row_covered slot
   exact Or.inl (Or.inl (Or.inr (List.mem_ofFn.mpr ⟨prev,same.symm.trans equal⟩)))
 · exact Or.inl (Or.inr reserved)
 · exact Or.inr ordinary

theorem registered (id : Nat) (tracked : id ∈ widthCandidates) : Known snapshot id := by
 simp only [widthCandidates,List.mem_cons,List.not_mem_nil,or_false] at tracked
 rcases tracked with rfl|rfl|rfl
 · exact ⟨(5 : Fin 8),rfl,Or.inl (by intro impossible; cases impossible)⟩
 · exact ⟨(6 : Fin 8),rfl,Or.inl (by intro impossible; cases impossible)⟩
 · exact ⟨(7 : Fin 8),rfl,Or.inl (by intro impossible; cases impossible)⟩

theorem point_closed : GeneralNominalReobservationSteps.PointClosed snapshot := by
 intro slot d seen
 obtain ⟨_,rfl⟩ := nominal_at slot d seen
 intro parameter member
 change GeneralNominalState.Parameter 8 at parameter
 change parameter ∈ [.type (2,2),.type (2,2)] at member
 simp only [List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl <;> rfl

end Yulang.GeneralRebaseAllWidthRefinement275
