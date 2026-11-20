import Yulang.GeneralMixedCompoundUpperBase307
import Yulang.GeneralDictionaryCompoundRefresh239

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 14000
namespace Yulang.GeneralMixedCompoundUpperSnapshot307
open GeneralDictionaryJournalRefinement228Source (constructors interpretation snapshot descriptor)
open GeneralDictionaryCompoundRefresh239 (refreshed)
open GeneralDictionaryCompoundSnapshot239 (extendedSnapshot extendedContext pointDesc)
open GeneralDictionaryCompoundBase239 (extendedBase extendedView)
open GeneralMixedCompoundUpperBase307 (base view embed source source_old source_new upper)

abbrev desc : GeneralNominalState.Descriptor 8 :=
  GeneralNominalRefinements.renameDescriptor embed pointDesc

noncomputable abbrev snap : GeneralNominalState.State where
  base := base
  view := view
  constructors := constructors
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
  allocated := extendedSnapshot.allocated
  reserved := extendedSnapshot.reserved
  ordinary := extendedSnapshot.ordinary
  seed := snapshot.seed

noncomputable abbrev context : GeneralNominalCandidates.Context := ⟨snap,interpretation⟩

theorem base_transport (i : Fin 7) :
    (base.heads (embed i)).equation = (extendedBase.heads i).equation.map (fun t => t.rename embed) := by
  revert i
  decide +kernel

theorem base_known (i : Fin 7) :
    extendedBase.graph i ≠ .unresolved → base.graph (embed i) ≠ .unresolved := by
  revert i
  decide +kernel

theorem view_known (i : Fin 7) :
    extendedView.graph i ≠ .unresolved → view.graph (embed i) ≠ .unresolved := by
  revert i
  decide +kernel

theorem nominals (i : Fin 7) (d) (hd : extendedSnapshot.nominals i = some d) :
    snap.nominals (embed i) = some (GeneralNominalRefinements.renameDescriptor embed d) := by
  change (if i = 0 ∨ i = 1 then some pointDesc else none) = some d at hd
  split at hd
  · rename_i e
    cases Option.some.inj hd
    rcases e with rfl|rfl <;> rfl
  · cases hd

noncomputable def refineRaw : GeneralNominalRefinements.Refines extendedSnapshot snap where
  base := ⟨embed,source_old,source_old,(fun atom found => List.mem_append_left _
    (List.mem_map.mpr ⟨atom,found,rfl⟩)),base_known,(fun _ found => nomatch found)⟩
  heads := by
    intro i term found
    exact .head (by rw [base_transport,found]; rfl)
  nominals := nominals
  ordinary := fun _ h => h
  known := by
    rintro n ⟨i,eq,head|⟨d,desc⟩⟩
    · exact ⟨embed i,(source_old i).trans eq,Or.inl (view_known i head)⟩
    · exact ⟨embed i,(source_old i).trans eq,Or.inr ⟨_,nominals i d desc⟩⟩
  reserved := fun _ h => h
  allocated := fun _ h => h
  seed := rfl
  constructors := rfl

theorem upper_high : 4 < upper :=
  GeneralNominalAggregateVersion231.above_seed _ _ _ _ _ _

theorem upper_not_old (i : Fin 7) : GeneralDictionaryCompoundBase239.source i ≠ upper := by
  revert i
  decide +kernel

theorem upper_unknown : ¬ GeneralNominalState.Known extendedSnapshot upper := by
  rintro ⟨i,eq,_⟩
  exact upper_not_old i eq

theorem upper_known : GeneralNominalState.Known snap upper :=
  ⟨7,source_new,Or.inl (by decide +kernel)⟩

theorem upper_reserved : upper ∈ extendedSnapshot.reserved := by
  change upper ∈ (GeneralNominalVersionedAllocation231.reserved snapshot
    GeneralDictionaryCompoundSource238.registry GeneralDictionaryJournalRefinement228Source.root.identity
    GeneralDictionaryCompoundPacket238.packet.bindings)
  rw [GeneralDictionaryCompoundPacket238.bindings_exact]
  decide +kernel

theorem upper_supported : upper ∈ GeneralNominalState.sources extendedSnapshot :=
  List.mem_append_left _ (List.mem_append_right _ upper_reserved)

theorem support (n : Nat) (h : n ∈ GeneralNominalState.sources snap) :
    n ∈ GeneralNominalState.sources extendedSnapshot := by
  simp only [GeneralNominalState.sources,List.mem_append] at h ⊢
  rcases h with ((ty|rows)|reserved)|atoms
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ty
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact Or.inl (Or.inr (show source (Fin.last 7) ∈ extendedSnapshot.reserved from source_new.symm ▸ upper_reserved))
    · exact Or.inl (Or.inl (Or.inl (List.mem_ofFn.mpr ⟨j,(source_old j).symm⟩)))
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp rows
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact Or.inl (Or.inr (show source (Fin.last 7) ∈ extendedSnapshot.reserved from source_new.symm ▸ upper_reserved))
    · exact Or.inl (Or.inl (Or.inr (List.mem_ofFn.mpr ⟨j,(source_old j).symm⟩)))
  · exact Or.inl (Or.inr reserved)
  · exact Or.inr atoms

end Yulang.GeneralMixedCompoundUpperSnapshot307
