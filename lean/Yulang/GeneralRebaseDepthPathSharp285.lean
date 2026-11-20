import Yulang.GeneralRebaseDepthPathRank285

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27500
set_option maxHeartbeats 12000000
namespace Yulang.GeneralRebaseDepthPathSharp285
open GeneralDictionaryOutputDepth252 (snapshot root registry roles initial plan)
open GeneralDictionaryOutputDepthInstall252 (installed)
open GeneralRebaseDepthScalar285 (old target present previously_unknown from_source new_zero new_one)
open GeneralNominalVersionedMixedObservations233 (Refresh CacheSound)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalState (Known)
open GeneralNominalRefinements (Refines)
open GeneralRebaseDepthPathRank285 (Hop ActualPath)
open GeneralNominalVersionedMixedKernel234 (Step)

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

theorem cache_half : CacheSound installed half.state := by
 intro observation recorded
 exact ⟨[],[],.source,.source,fun m _ valid =>
   GeneralCanonicalObservations.recorded_sound half.state m
     ((half_raw m).mpr (from_source m valid.1)) recorded⟩

noncomputable def cert_half : Refresh installed half where
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

noncomputable def halfway := refresh installed half

theorem half_models (m) : Models halfway m ↔ Models installed m :=
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

theorem first : Hop installed halfway :=
  .refresh half cert_half 0 (present 0 (by decide)) (previously_unknown 0 (by decide)) zero_half

theorem second : Hop halfway (refresh halfway target) :=
  .refresh target cert_both 1 (present 1 (by decide)) no_one_half new_one

theorem same_endpoint : refresh halfway target = GeneralRebaseDepthScalar285.refreshed := rfl

theorem two_refreshes : ActualPath installed GeneralRebaseDepthScalar285.refreshed 2 := by
 have a := GeneralRebaseDepthPathAnchor285.initial
 have k := GeneralRebaseDepthPathKeep285.start
 have before := GeneralRebaseDepthPathRank285.anchored a k first
 have path := ActualPath.more (ActualPath.more (.empty _) ((GeneralRebaseDepthPathRank285.exact a k).mpr first))
   ((GeneralRebaseDepthPathRank285.exact before.1 before.2).mpr second)
 exact same_endpoint ▸ path

end Yulang.GeneralRebaseDepthPathSharp285
