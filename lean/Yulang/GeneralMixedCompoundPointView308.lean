import Yulang.GeneralMixedCompoundPointViewBase308
import Yulang.GeneralMixedCompoundBatchBase307

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 16000000
namespace Yulang.GeneralMixedCompoundPointView308
open GeneralDictionaryJournalRefinement228Source (snapshot interpretation)
open GeneralDictionaryJournalRefinement228Reobserve (exactCopy)
open GeneralDictionaryCompoundBase239 (lo hi)
open GeneralMixedCompoundPointPorts308 (afterSnap lower_reserved upper_reserved)
open GeneralMixedCompoundPointFeedback308 (port_sources)
open GeneralMixedCompoundPointViewBase308 (base view source source_old source_new upper)
open GeneralMixedCompoundBatchBase307 (embed)
open GeneralMixedCompoundUpperSnapshot307 (desc)
open GeneralNominalState (State Known)
open GeneralNominalRefinements (Refines)

noncomputable abbrev snap : State where
  base := base
  view := view
  constructors := afterSnap.constructors
  nominals := fun slot => if slot = 0 ∨ slot = 1 then some desc else none
  catalogue := by
    intro slot d found
    split at found
    · cases Option.some.inj found; rfl
    · cases found
  bodies_opaque := by
    intro slot d found
    split at found
    · rename_i either
      rcases either with rfl|rfl <;> rfl
    · cases found
  allocated := afterSnap.allocated
  reserved := afterSnap.reserved
  ordinary := afterSnap.ordinary
  seed := afterSnap.seed

noncomputable abbrev context : GeneralNominalCandidates.Context := ⟨snap,interpretation⟩

theorem nominals (slot : Fin 5) (d : GeneralNominalState.Descriptor 5)
    (saved : afterSnap.nominals slot = some d) :
    snap.nominals (embed slot) = some (GeneralNominalRefinements.renameDescriptor embed d) := by
  change (if slot = 0 ∨ slot = 1 then some exactCopy else none) = some d at saved
  split at saved
  · rename_i either
    cases Option.some.inj saved
    rcases either with rfl|rfl <;> rfl
  · cases saved

theorem base_head (slot : Fin 5) : afterSnap.base.graph slot ≠ .unresolved →
    base.graph (embed slot) ≠ .unresolved := by revert slot; decide +kernel

theorem view_head (slot : Fin 5) : afterSnap.view.graph slot ≠ .unresolved →
    view.graph (embed slot) ≠ .unresolved := by revert slot; decide +kernel

theorem embedded_source (slot : Fin 5) : source (embed slot) = slot.val :=
  (source_old _).trans (GeneralDictionaryCompoundBase239.source_embed slot)

theorem slots7 (j : Fin 7) :
    (∃ k : Fin 5, GeneralDictionaryCompoundBase239.embed k = j) ∨ j = 5 ∨ j = 6 := by
  revert j
  decide +kernel

theorem old_not_port (i : Fin 5) : i.val ≠ lo := by revert i; decide +kernel

noncomputable def refines : Refines afterSnap snap where
  base := ⟨embed,embedded_source,embedded_source,
     (fun a h => List.mem_append_left _ (List.mem_map.mpr ⟨a,h,rfl⟩)),
     base_head,(fun _ absent => nomatch absent)⟩
  heads := by
    intro slot term saved
    change Fin 5 at slot
    by_cases two : slot = 2
    · subst slot
      have same : term = .emptyRecord := Option.some.inj saved.symm
      subst term; exact .head rfl
    · change (GeneralDictionaryJournalRefinement228Source.base.heads slot).equation = some term at saved
      simp [GeneralDictionaryJournalRefinement228Source.base,two,GeneralSourceState.Head.equation] at saved
  nominals := nominals
  ordinary := fun _ h => h
  known := by
    rintro n ⟨slot,eq,seen|⟨d,seen⟩⟩
    · exact ⟨embed slot,(embedded_source slot).trans eq,Or.inl (view_head slot seen)⟩
    · exact ⟨embed slot,(embedded_source slot).trans eq,Or.inr ⟨_,nominals slot d seen⟩⟩
  reserved := fun _ h => h
  allocated := fun _ h => h
  seed := rfl
  constructors := rfl

theorem upper_reserved_new : upper ∈ afterSnap.reserved := by
  change upper ∈ GeneralNominalVersionedInstallation231.reserved GeneralMixedCompoundPointFirstPlan308.pkt
  unfold GeneralNominalVersionedInstallation231.reserved
  rw [GeneralDictionaryCompoundCurrent238.bindings_exact]
  decide +kernel

theorem support (n : Nat) (present : n ∈ GeneralNominalState.sources snap) :
    n ∈ GeneralNominalState.sources afterSnap := by
  have indexed (i : Fin 8) : source i ∈ GeneralNominalState.sources afterSnap := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · change source (7 : Fin 8) ∈ _
      rw [source_new]
      exact List.mem_append_left _ (List.mem_append_right _ upper_reserved_new)
    · rw [source_old]
      refine (slots7 j).elim ?_ ?_
      · rintro ⟨k,rfl⟩
        rw [GeneralDictionaryCompoundBase239.source_embed]
        exact GeneralNominalAllocationSupport.slot_source afterSnap k
      · rintro (rfl|rfl)
        · exact port_sources.1
        · exact port_sources.2
  simp only [GeneralNominalState.sources,List.mem_append] at present
  rcases present with ((term|row)|reserved)|atoms
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp term
    exact indexed i
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp row
    exact indexed i
  · exact List.mem_append_left _ (List.mem_append_right _ reserved)
  · exact List.mem_append_right _ atoms

theorem previously_unknown : ¬ Known afterSnap lo := by
  rintro ⟨i,eq,_⟩
  exact old_not_port i eq

theorem seen_lo : Known snap lo := ⟨5,rfl,Or.inl (by decide +kernel)⟩
theorem seen_hi : Known snap hi := ⟨6,rfl,Or.inl (by decide +kernel)⟩

end Yulang.GeneralMixedCompoundPointView308
