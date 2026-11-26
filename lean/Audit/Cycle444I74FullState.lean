import Yulang.GeneralDeclarativeI65I74FullState444

namespace Yulang.GeneralDeclarativeI65.I72.FullStateAudit444
open CommonNominalFullCarrier (Equivalent)
open CommonDeclaredNominalInspection (Kind)
open GeneralDeclarativeI65

theorem evidence_at_every_exact_typed_target444 (s : FullState) (m : Model)
    (fit : FitsFull s m) (e : RetainedEquation s.base) (stored : e ∈ s.retained) :
    ∃ ty, e.output.receipt.actualEquation m = some (e.target,ty) ∧
      evaluateMixedRhs401 (sourceRead401 m (e.frame.slots e.body)) e.output.plan = some ty ∧
      Equivalent (m.assignment e.target).1 ty := by
  obtain ⟨v,eqv,retained⟩ := fit.2 e stored
  obtain ⟨x,eqx,typed⟩ := named_mixed_output_is_fixed_equation401 e.output m
  have same : v = x := (Prod.mk.inj (Option.some.inj (eqv.symm.trans eqx))).2
  exact ⟨v,eqv,same.symm ▸ typed,retained⟩

theorem retention_does_not_replace_legacy_constraints444 (s : FullState) (m : Model) :
    FitsFull s m → Fits s.base m := fun fit => fit.1

theorem row_addresses_are_the_original_source_indices444 {s : State} (e : RetainedEquation s) :
    e.output.receipt.occurrence = e.occurrence ∧
    e.declarationOrdinal = e.frame.ordinal ∧
    e.output.receipt.outputOrdinal = e.outputOrdinal.val ∧
    e.output.receipt.original.target = e.target ∧
    e.output.receipt.body = e.body ∧
    e.kind = Kind.value ∧
    s.b6.read e.request e.declarationOrdinal e.outputOrdinal e.body = some e.output.plan :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,e.output.originalTyped⟩

#print axioms fits_iff_fitsFull_liftState
#print axioms evidence_at_every_exact_typed_target444
#print axioms retention_does_not_replace_legacy_constraints444
#print axioms row_addresses_are_the_original_source_indices444
end Yulang.GeneralDeclarativeI65.I72.FullStateAudit444
