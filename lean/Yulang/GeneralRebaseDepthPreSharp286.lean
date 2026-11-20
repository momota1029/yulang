import Yulang.GeneralRebaseDepthFullTrace286

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27500
set_option maxHeartbeats 12000000
namespace Yulang.GeneralRebaseDepthPreSharp286
open GeneralDictionaryOutputDepth252 (snapshot root registry roles initial context)
open GeneralRebaseDepthFullTrace286 (RefreshTrace)
open GeneralRebaseDepthPhase286 (InstallHop Post)
open GeneralNominalVersionedMixedObservations233 (Refresh CacheSound)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalState (Known)
open GeneralNominalRefinements (Refines)
open GeneralRebaseDepthPathRank285 (Hop ActualPath)
open GeneralNominalVersionedMixedKernel234 (Step)

noncomputable abbrev old := context
noncomputable def target := GeneralRebaseScalarSnapshot271.context old

theorem from_source (m) (valid : GeneralNominalState.Models snapshot m) :
    GeneralNominalState.Models target.state m := valid

theorem present (n : Nat) (small : n ≤ 1) : n ∈ GeneralNominalState.sources old.state := by
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_left
  exact List.mem_ofFn.mpr ⟨(⟨n,by omega⟩ : Fin 4),rfl⟩

theorem previously_unknown (n : Nat) (small : n ≤ 1) : ¬ Known old.state n := by
  rintro ⟨slot,loc,head | ⟨d,found⟩⟩
  · exact head rfl
  · let slot4 : Fin 4 := slot
    have eqn : slot4.val = n := loc
    have found4 : (if slot4 = (2 : Fin 4) then some GeneralDictionaryOutputDepth252.foo else none) = some d := found
    split at found4
    · rename_i eq
      have vv : slot4.val = 2 := congrArg Fin.val eq
      omega
    · cases found4

theorem new_zero : Known target.state 0 := ⟨(0 : Fin 4),rfl,Or.inl (by decide +kernel)⟩
theorem new_one : Known target.state 1 := ⟨(1 : Fin 4),rfl,Or.inl (by decide +kernel)⟩

noncomputable def halfView : GeneralNormalizedObservation.Snapshot old.state.base where
  kinds := old.state.view.kinds
  shapes := old.state.view.shapes
  shapes_injective := old.state.view.shapes_injective
  canonical := old.state.view.canonical
  heads := fun slot => if slot.val = 0 then target.state.view.heads slot else old.state.view.heads slot
  checked := by
    intro slot term recorded
    change (if slot.val = 0 then target.state.view.heads slot else old.state.view.heads slot).term = some term at recorded
    split at recorded
    · exact target.state.view.checked slot term recorded
    · exact old.state.view.checked slot term recorded

noncomputable def halfState : GeneralNominalState.State :=
  { old.state with
    view := halfView
    bodies_opaque := by
      intro slot d observed
      change (if slot.val = 0 then target.state.view.heads slot else old.state.view.heads slot) = _
      split
      · exact target.state.bodies_opaque slot d observed
      · exact old.state.bodies_opaque slot d observed }

noncomputable def half : GeneralNominalCandidates.Context := { old with state := halfState }

theorem half_raw (m) : GeneralNominalState.Models half.state m ↔ GeneralNominalState.Models target.state m := Iff.rfl

theorem half_keep (n : Nat) : Known old.state n → Known half.state n := by
  rintro ⟨slot,source,heads|nom⟩
  · change snapshot.view.graph slot ≠ .unresolved at heads
    exact (heads rfl).elim
  · exact ⟨slot,source,Or.inr nom⟩

noncomputable def ref_half : Refines old.state half.state where
  base := (GeneralNominalRefinements.refl old.state).base
  heads := (GeneralNominalRefinements.refl old.state).heads
  nominals := (GeneralNominalRefinements.refl old.state).nominals
  ordinary := fun _ held => held
  known := half_keep
  reserved := fun _ held => held
  allocated := fun _ held => held
  seed := rfl
  constructors := rfl

theorem cache_half : CacheSound initial half.state := by
 intro observation recorded
 exact ⟨[],[],.source,.source,fun m _ valid =>
   GeneralCanonicalObservations.recorded_sound half.state m
     ((half_raw m).mpr (from_source m valid.1)) recorded⟩

noncomputable def cert_half : Refresh initial half where
  refines := ref_half
  interpretation := rfl
  support := fun _ held => held
  constraints := fun _ held => ⟨held.1.1.1,held.1.1.2.2⟩
  cache := cache_half

theorem zero_half : Known half.state 0 := ⟨(0 : Fin 4),rfl,Or.inl (by decide +kernel)⟩

theorem no_one_half : ¬ Known half.state 1 := by
  rintro ⟨slot,source,seen⟩
  apply previously_unknown 1 (by decide)
  refine ⟨slot,source,?_⟩
  rcases seen with head|nom
  · left
    let s : Fin 4 := slot
    have index : s.val = 1 := source
    have check : half.state.view.graph s = old.state.view.graph s := by
      simp only [GeneralNormalizedObservation.Snapshot.graph]
      change (if s.val = 0 then target.state.view.heads s else old.state.view.heads s).node =
        (old.state.view.heads s).node
      rw [index]
      rfl
    exact fun eq => head (check.trans eq)
  · exact Or.inr nom

noncomputable def halfway := refresh initial half

theorem half_models (m) : Models halfway m ↔ Models initial m :=
  GeneralNominalVersionedMixedObservations233.refresh_models cert_half

theorem all_keep (n : Nat) : Known half.state n → Known target.state n := by
  rintro ⟨slot,source,heads|nom⟩
  · by_cases take : slot.val = 0
    · have same : n = 0 := source.symm.trans take
      simpa only [same] using new_zero
    · have eq : half.state.view.graph slot = old.state.view.graph slot := by
        unfold GeneralNormalizedObservation.Snapshot.graph
        change (if slot.val = 0 then target.state.view.heads slot else old.state.view.heads slot).node =
          (old.state.view.heads slot).node
        rw [ite_eq_right take]
      exact False.elim (heads (eq.trans rfl))
  · exact ⟨slot,source,Or.inr nom⟩

noncomputable def ref_both : Refines half.state target.state where
  base := (GeneralNominalRefinements.refl half.state).base
  heads := (GeneralNominalRefinements.refl half.state).heads
  nominals := (GeneralNominalRefinements.refl half.state).nominals
  ordinary := fun _ held => held
  known := all_keep
  reserved := fun _ held => held
  allocated := fun _ held => held
  seed := rfl
  constructors := rfl

theorem cache_both : CacheSound halfway target.state := by
 intro observation recorded
 exact ⟨[],[],.source,.source,fun m _ valid =>
   GeneralCanonicalObservations.recorded_sound target.state m (from_source m valid.1) recorded⟩

noncomputable def cert_both : Refresh halfway target where
  refines := ref_both
  interpretation := rfl
  support := fun _ held => held
  constraints := fun _ held => ⟨held.1.1.1,held.1.1.2.2⟩
  cache := cache_both

theorem first : Hop initial halfway :=
  .refresh half cert_half 0 (present 0 (by decide)) (previously_unknown 0 (by decide)) zero_half

theorem second : Hop halfway (refresh halfway target) :=
  .refresh target cert_both 1 (present 1 (by decide)) no_one_half new_one

noncomputable def prepared := refresh halfway target

theorem two_refreshes : RefreshTrace initial prepared 2 :=
  .more (.more (.empty _) first) second

theorem sharp_install_last :
    ∃ terminal, InstallHop prepared terminal ∧ ActualPath initial terminal 3 ∧
      (∀ next, ¬ Step registry root terminal next) := by
  have linked := GeneralRebaseDepthFullTrace286.linked_after two_refreshes
  obtain ⟨terminal, take⟩ := GeneralRebaseDepthPreAvailable286.offers linked
  have pre := GeneralRebaseDepthEnableShape286.as_pre linked
  have post := GeneralRebaseDepthPhase286.cross pre take
  have rawZero : GeneralRebaseDepthPathRank285.rank prepared = 0 := by
    classical
    unfold GeneralRebaseDepthPathRank285.rank GeneralRebaseDepthPathRank285.pending
    change (if Known target.state 0 then 0 else 1) + (if Known target.state 1 then 0 else 1) = 0
    simp only [new_zero,new_one,ite_true,Nat.add_zero]
  have terminalZero := GeneralRebaseDepthFullRank286.scalar_same_at_install pre take
  rw [rawZero] at terminalZero
  refine ⟨terminal,take,.more (GeneralRebaseDepthFullTrace286.real_refresh_trace two_refreshes)
    (GeneralRebaseDepthPhase286.as_step take),?_⟩
  intro next more
  have less := GeneralRebaseDepthPathRank285.drop post.anchor (GeneralRebaseDepthPhase286.post_step post more)
  omega

end Yulang.GeneralRebaseDepthPreSharp286
