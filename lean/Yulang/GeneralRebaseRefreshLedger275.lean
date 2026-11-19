import Yulang.GeneralRebaseRefreshSaturation275

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 8500000
namespace Yulang.GeneralRebaseRefreshLedger275
open GeneralDictionaryJournalRefinement228Source (roles)
open GeneralDictionaryVersionedSecondInstall233 (installed)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalState (sources)
open GeneralRebaseRefreshRank275 (Hop snapshot)
open GeneralRebaseRefreshPublic275 (After)
open GeneralRebaseRefreshEvidence275 (all_histories kept)

structure Retained (before after : State roles) : Prop where
 support : ∀ id, id ∈ sources (snapshot before) ↔ id ∈ sources (snapshot after)
 plans : after.plans = before.plans
 effects : after.effects = before.effects
 source : after.core.erased.source = before.core.erased.source
 row_slots : ∀ id, (∃ slot, (snapshot before).base.rowSource slot = id) →
   ∃ slot, (snapshot after).base.rowSource slot = id
 type_slots : ∀ id, (∃ slot, (snapshot before).base.source slot = id) →
   ∃ slot, (snapshot after).base.source slot = id
 seed : (snapshot after).seed = (snapshot before).seed
 constructors : (snapshot after).constructors = (snapshot before).constructors
 interpretation : after.core.erased.current.context.interpretation = before.core.erased.current.context.interpretation

theorem refl (s : State roles) : Retained s s :=
 ⟨fun _ => Iff.rfl,rfl,rfl,rfl,fun _ h => h,fun _ h => h,rfl,rfl,rfl⟩

theorem trans {a b c : State roles} (ab : Retained a b) (bc : Retained b c) : Retained a c :=
 ⟨fun i => (ab.support i).trans (bc.support i),bc.plans.trans ab.plans,bc.effects.trans ab.effects,
  bc.source.trans ab.source,fun i h => bc.row_slots i (ab.row_slots i h),
  fun i h => bc.type_slots i (ab.type_slots i h),bc.seed.trans ab.seed,bc.constructors.trans ab.constructors,
  bc.interpretation.trans ab.interpretation⟩

theorem hop_retains {s t : State roles} (move : Hop s t) : Retained s t := by
 cases move with
 | step ctx cert _ _ _ _ =>
   refine ⟨fun i => ⟨GeneralNominalRefinements.sources cert.refines i,cert.support i⟩,rfl,rfl,rfl,
     ?_,?_,cert.refines.seed,cert.refines.constructors,cert.interpretation⟩
   · rintro i ⟨slot,equal⟩
     exact ⟨cert.refines.base.embed slot,(cert.refines.base.rowSource slot).trans equal⟩
   · rintro i ⟨slot,equal⟩
     exact ⟨cert.refines.base.embed slot,(cert.refines.base.source slot).trans equal⟩

theorem all_retained {s : State roles} (path : After s) : Retained installed s := by
 induction path with
 | refl => exact refl installed
 | tail before hop ih =>
   have witness := all_histories before
   exact trans ih (hop_retains ((GeneralRebaseRefreshAcc275.exact_hop ⟨witness.1,kept witness.2⟩).mp hop))

end Yulang.GeneralRebaseRefreshLedger275
