import Yulang.GeneralMixedCompoundEarlySquare308

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
namespace Yulang.GeneralMixedCompoundEarlyNoShortcut308
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryJournalRefinement228Reobserve (loose)
open GeneralDictionaryCompoundFrame238 (installed)
open GeneralDictionaryCompoundSource238 (registry)
open GeneralMixedCompoundUpperSnapshot307 (snap desc context)
open GeneralMixedCompoundUpperRefresh307 (upperState)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalRefinements (renameDescriptor)

def slots (s : State roles) : Nat := s.core.erased.current.context.state.base.slots
theorem width : slots installed ≠ slots upperState := by decide +kernel

theorem refresh_impossible : ¬ Nonempty (Refresh installed context) := by
  rintro ⟨co⟩
  let f := co.refines.base.embed
  have at0 : f (0 : Fin 5) = (0 : Fin 8) :=
    snap.base.source_injective (co.refines.base.source (0 : Fin 5))
  have at2 : f (2 : Fin 5) = (2 : Fin 8) :=
    snap.base.source_injective (co.refines.base.source (2 : Fin 5))
  have at4 : f (4 : Fin 5) = (4 : Fin 8) :=
    snap.base.source_injective (co.refines.base.source (4 : Fin 5))
  have keeps := co.refines.nominals (0 : Fin 5) loose rfl
  change snap.nominals (f (0 : Fin 5)) = some (renameDescriptor f loose) at keeps
  rw [at0] at keeps
  have clash : desc = renameDescriptor f loose := Option.some.inj keeps
  have caps := congrArg GeneralNominalState.Descriptor.arguments clash
  change ([.type ((2 : Fin 8),2),.type (2,2)] : List (GeneralNominalState.Parameter 8)) =
    [.type (f (4 : Fin 5),f (2 : Fin 5)), .type (f (4 : Fin 5),f (2 : Fin 5))] at caps
  rw [at2,at4] at caps
  have distinct := congrArg Prod.fst (GeneralNominalState.Parameter.type.inj (List.cons.inj caps).1)
  exact (by decide : (2 : Fin 8) ≠ 4) distinct

theorem refresh_target_impossible (ctx : GeneralNominalCandidates.Context)
    (cert : Refresh installed ctx) : refresh installed ctx ≠ upperState := by
  intro eq
  have same := congrArg (fun s : State roles => s.core.erased.current.context) eq
  change ctx = context at same
  subst ctx
  exact refresh_impossible ⟨cert⟩

theorem no_shortcut : ¬ Step registry root installed upperState := by
  rintro ⟨focus,generated,op⟩
  have rule {t : State roles} (same : t = upperState) (old : slots t = slots installed) : False :=
    width (old.symm.trans (congrArg slots same))
  have all {t : State roles} (op : GeneralNominalVersionedMixedKernel234.At registry installed focus t) :
      t ≠ upperState := by
    intro same
    cases op with
    | administrative action =>
      cases action with
      | enqueue => exact rule same rfl
      | refresh ctx cert _ _ _ _ => exact refresh_target_impossible ctx cert same
      | equate => exact rule same rfl
      | reobserve => exact rule same rfl
    | refresh _ ctx cert _ _ _ _ => exact refresh_target_impossible ctx cert same
    | install e enabled _ =>
      have ctx := e.frame.context_eq.trans (congrArg (fun c => c.erased.current.context) enabled.snapshot_eq)
      apply rule same
      change e.plan.packet.context.state.base.slots = installed.core.erased.current.context.state.base.slots
      exact congrArg (fun c : GeneralNominalCandidates.Context => c.state.base.slots) ctx
    | merge => exact rule same rfl
  exact all op rfl

end Yulang.GeneralMixedCompoundEarlyNoShortcut308
