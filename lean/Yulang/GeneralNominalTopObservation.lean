import Yulang.GeneralNominalState

/-! Top bounds carry no scalar, structural, or nominal head observation.
One actual model assigning top therefore prevents a certified Known head.
This concerns the existing observation language, not an execution policy. -/
namespace Yulang.GeneralNominalTopObservation

open CommonNominalFullCarrier

theorem le_top (value : Ty) : Subtype value .top := by
  intro depth
  apply (CommonNominalFullDemand.producerLe_iff_probe _ _).mpr
  intro rank env observation accepted
  cases observation with
  | trivial => exact CommonNominalFullDemand.probeAt_trivial rank _
  | _ => cases rank <;> cases accepted

theorem top_not_scalar (base : Inference.Base) : ¬ Subtype .top (.base base) := by
  intro below
  exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
    ⟨fun _ => .bottom, fun _ => []⟩ (.base base) rfl

theorem top_not_nominal (name : Nat) (arguments : List Argument) :
    ¬ Subtype .top (nominal name arguments) := by
  intro below
  exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
    ⟨fun _ => .bottom, fun _ => []⟩ (.nominalHead name arguments.length) ⟨rfl,by simp⟩

theorem top_not_shape (shape : GeneralNormalizedObservation.Shape)
    (children : Fin shape.arity → Fin slots)
    (assignment : Fin slots → Core.PresenceGeneration.Comp CommonNominalFullCarrier.model) :
    ¬ Subtype .top ((shape.term children).eval CommonNominalFullCarrier.model assignment) := by
  intro below
  let role : CommonNominalFullDemand.Head := match shape with
    | .pair => .pair | .variant tag => .variant tag | _ => .records
  have probe := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
    ⟨fun _ => .bottom,fun _ => [role]⟩ (.role 0)
  cases shape with
  | pair | variant | exactEmpty =>
    simp [role, GeneralNormalizedObservation.Shape.term,Core.PresenceGeneration.TyTerm.eval,
      CommonNominalFullCarrier.model,CommonNominalFullCarrier.pair,CommonNominalFullCarrier.variant,
      observeTy,CommonNominalSyntax.Layer.evalAt,CommonNominalFullDemand.ProbeAt,
      CommonNominalFullDemand.ProbeStep,CommonNominalFullDemand.MaskedProbeStep] at probe
  | record labels =>
    cases labels <;>
      simp [role, GeneralNormalizedObservation.Shape.term,GeneralNormalizedObservation.recordTerm,
        List.ofFn_succ,Core.PresenceGeneration.TyTerm.eval,CommonNominalFullCarrier.model,
        CommonNominalFullCarrier.record,observeTy,CommonNominalSyntax.Layer.evalAt,
        CommonNominalFullDemand.ProbeAt,CommonNominalFullDemand.ProbeStep,
        CommonNominalFullDemand.MaskedProbeStep] at probe

theorem not_known (state : GeneralNominalState.State)
    (model : GeneralNominalCommonBridge.Assignment) (source : Nat)
    (valid : GeneralNominalState.Models state model) (at_source : (model source).1 = .top) :
    ¬ GeneralNominalState.Known state source := by
  rintro ⟨slot,identity,head | ⟨descriptor,recorded⟩⟩
  · have observation := GeneralNominalState.normalized_models state model valid
    cases seen : state.view.heads slot with
    | deferred reason =>
        exact head (by simp [GeneralNormalizedObservation.Snapshot.graph,seen,
          GeneralNormalizedObservation.Head.node])
    | scalar base =>
        have equal := observation slot (.base base)
          (by simp [seen,GeneralNormalizedObservation.Head.term])
        exact top_not_scalar base (by simpa [identity,at_source,
          Core.PresenceGeneration.TyTerm.eval,CommonNominalFullCarrier.model] using equal.1)
    | structural kind children =>
        have equal := observation slot ((state.view.shapes kind).term children)
          (by simp [seen,GeneralNormalizedObservation.Head.term])
        exact top_not_shape _ children _ (by simpa [identity,at_source] using equal.1)
  · obtain ⟨arguments,_,equal⟩ := valid.2.1 slot descriptor recorded
    exact top_not_nominal _ _ (by simpa [identity,at_source] using equal.1)

end Yulang.GeneralNominalTopObservation
