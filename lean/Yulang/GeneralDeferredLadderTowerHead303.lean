import Yulang.GeneralNominalOutputGrowth

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeferredLadderTowerHead303
open CommonNominalFullCarrier
open GeneralNominalOutputGrowth (tower finiteModel)
open GeneralNormalizedObservation (Shape Head)
open Core.PresenceGeneration (TyTerm Comp)

def emptyEnv : CommonNominalFullDemand.Environment Common.Row :=
  ⟨fun _ => .bottom,fun _ => []⟩

theorem tower_no_probe (d : Nat) (obs : CommonNominalFullDemand.Observation Common.Row)
    (contraBase : ¬ CommonNominalFullDemand.ProbeAt Common.rowLe 0 emptyEnv
      (observeTy 0 (.base .int)) obs)
    (contraNominal : ∀ n, ¬ CommonNominalFullDemand.ProbeAt Common.rowLe 0 emptyEnv
      (observeTy 0 (nominal 0 [.inl (tower n)])) obs) :
    ¬ CommonNominalFullDemand.ProbeAt Common.rowLe 0 emptyEnv (observeTy 0 (tower d)) obs := by
  cases d with
  | zero => exact contraBase
  | succ d => exact contraNominal d

abbrev Probe (t : Ty) (obs : CommonNominalFullDemand.Observation Common.Row) :=
  CommonNominalFullDemand.ProbeAt Common.rowLe 0 emptyEnv (observeTy 0 t) obs

theorem structural_not_tower {slots : Nat} (shape : Shape)
    (children : Fin shape.arity → Fin slots) (values : Fin slots → Comp CommonNominalFullCarrier.model) (d : Nat) :
    ¬ Subtype (tower d) ((shape.term children).eval CommonNominalFullCarrier.model values) := by
  intro below
  have preserve := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0 emptyEnv
  cases shape with
  | pair =>
    exact tower_no_probe d (.pairFirst .trivial) (by intro bad; exact bad) (by intro j bad; exact bad)
      (preserve (.pairFirst .trivial) (by trivial))
  | variant tag =>
    have accepted : Probe ((Shape.term (.variant tag) children).eval CommonNominalFullCarrier.model values)
        (.variant tag .trivial) := by
      change tag = tag ∧ _
      exact ⟨rfl,trivial⟩
    exact tower_no_probe d (.variant tag .trivial) (by intro bad; exact bad) (by intro j bad; exact bad)
      (preserve _ accepted)
  | exactEmpty =>
    exact tower_no_probe d .records (by intro bad; exact bad) (by intro j bad; exact bad)
      (preserve .records (by trivial))
  | record labels =>
    cases labels with
    | nil =>
      exact tower_no_probe d .records (by intro bad; exact bad) (by intro j bad; exact bad)
        (preserve .records (by trivial))
    | cons label labels =>
      have seen : Probe ((Shape.term (.record (label :: labels)) children).eval
          CommonNominalFullCarrier.model values) .records := by
        simp only [Shape.term,List.ofFn_succ,GeneralNormalizedObservation.recordTerm,List.foldr_cons,
          TyTerm.eval,CommonNominalFullCarrier.model,CommonNominalFullCarrier.record,observeTy,
          CommonNominalSyntax.Layer.evalAt,Probe,CommonNominalFullDemand.ProbeAt,
          CommonNominalFullDemand.ProbeStep,CommonNominalFullDemand.MaskedProbeStep]
      exact tower_no_probe d .records (by intro bad; exact bad) (by intro j bad; exact bad)
        (preserve .records seen)

theorem no_structural_head (n : Nat) (s : GeneralNominalState.State)
    (valid : GeneralNominalState.Models s (finiteModel n))
    (slot : Fin s.base.slots) (kind : Fin s.view.kinds)
    (children : Fin (s.view.shapes kind).arity → Fin s.base.slots) :
    s.view.heads slot ≠ .structural kind children := by
  intro found
  have equation : (s.view.heads slot).term = some ((s.view.shapes kind).term children) := by
    rw [found]
    rfl
  have model := GeneralNominalState.normalized_models s _ valid slot _ equation
  exact structural_not_tower (s.view.shapes kind) children
    (GeneralNominalCommonBridge.assignment s.base (finiteModel n))
    (n+1-s.base.source slot) model.1

end Yulang.GeneralDeferredLadderTowerHead303
