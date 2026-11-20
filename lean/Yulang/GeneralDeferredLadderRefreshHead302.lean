import Yulang.GeneralDeferredLadderBranch302
import Yulang.GeneralDictionaryInspectionHeads215

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeferredLadderRefreshHead302
open GeneralDeferredLadderLedger302 (Phase)
open GeneralDeferredLadderStage302 (model)
open GeneralObservedLadderRoute301 (focus)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalRecursiveInspection (Test)
open GeneralNominalSupport (Head)
open GeneralNominalFiniteHeadInversion (head)
open GeneralDictionaryInspectionHeads215 (tagged_scalar tagged_test tag_subtype)
open CommonNominalFullCarrier (Equivalent Ty subtype_refl)

theorem int_test (probe : Test) (ok : probe.Holds (.base .int)) : probe = .scalar .int := by
  have same := tag_subtype (tagged_test probe ok) (tagged_scalar .int) (subtype_refl _)
  cases probe with
  | scalar b => exact congrArg Test.scalar (CommonNominalFullDemand.Head.base.inj same)
  | nominal _ _ => cases same
  | structural shape => cases shape <;> cases same

theorem scalar_witness {snap : GeneralNominalState.State} {a tag}
    (cert : Head snap a (.scalar .int) tag) :
    ∃ i, snap.base.source i = a ∧ snap.view.heads i = .scalar .int := by
  cases cert with
  | scalar slot _ recorded => exact ⟨slot,rfl,recorded⟩

theorem terminal_scalar (p : Phase n k) (ctx : GeneralNominalCandidates.Context)
    (cert : Refresh p.state ctx) (known : GeneralNominalState.Known ctx.state (n+1)) :
    ∃ slot, ctx.state.base.source slot = n+1 ∧ ctx.state.view.heads slot = .scalar .int := by
  obtain ⟨test,observation,found⟩ := GeneralNominalCenteredHeadMatStepCache.known_has_head known
  have certified := cert.cache _ (GeneralNominalSupport.head_recorded found)
  have interpreted := GeneralNominalVersionedMixedObservations233.justified_sound certified (model p)
  have actual := GeneralNominalCenteredHeadAllocMergeStable.head_holds found interpreted
  have isInt : (GeneralNominalOutputGrowth.finiteModel n (n+1)).1 = .base .int := by
    change GeneralNominalOutputGrowth.tower (n+1-(n+1)) = _
    rw [Nat.sub_self]
    rfl
  rw [isInt] at actual
  cases int_test test actual
  exact scalar_witness found

theorem terminal_has_no_nominal (p : Phase n k) (ctx : GeneralNominalCandidates.Context)
    (cert : Refresh p.state ctx) (known : GeneralNominalState.Known ctx.state (n+1))
    (slot : Fin ctx.state.base.slots) (source : ctx.state.base.source slot = n+1) :
    ctx.state.view.heads slot = .scalar .int ∧ ctx.state.nominals slot = none := by
  obtain ⟨whereAt,loc,observed⟩ := terminal_scalar p ctx cert known
  have same := ctx.state.base.source_injective (source.trans loc.symm)
  subst whereAt
  refine ⟨observed,?_⟩
  cases record : ctx.state.nominals slot with
  | none => rfl
  | some desc =>
    have bodies := ctx.state.bodies_opaque slot desc record
    rw [observed] at bodies
    cases bodies

end Yulang.GeneralDeferredLadderRefreshHead302
