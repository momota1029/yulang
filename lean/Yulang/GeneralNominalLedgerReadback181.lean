import Yulang.GeneralNominalOriginRootAlias181

/-! Centered model validity already includes every registered plan's equations.
Actual-use readback therefore needs no execution path or raw-packet membership.
Current recorded root aliases transport that readback to renamed origins. -/
namespace Yulang.GeneralNominalLedgerReadback181
open GeneralNominalCenters GeneralNominalCenteredSteps GeneralNominalRecursiveInspection
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralNominalOriginAlias181 (mapSource)
open GeneralNominalOriginRootAlias181 (RootRecorded recorded_root_similar)

variable {roles : Roles.RoleDecls} {state : State roles} {model : Assignment}

 theorem registered_actual (old : Plan roles) (registered : old ∈ state.plans)
    (model : Assignment) (valid : Models state model) (use : GeneralNominalMaterialization.Use)
    (present : use ∈ old.headSchema.variables) (actual : use.mode = .actual) :
    GeneralNominalOriginTerms.Same model use.origin (.source (old.binder use.name)) := by
  have equation := (valid.2.2 old registered).2.2.1.2 use present
  simpa only [actual,ite_true] using equation

 theorem registered_readback (old candidate : Plan roles) (registered : old ∈ state.plans)
    (model : Assignment) (valid : Models state model) (use : GeneralNominalMaterialization.Use)
    (present : use ∈ old.headSchema.variables) (actual : use.mode = .actual)
    (origin : Origin) (sameOrigin : origin = use.origin) (name : Nat)
    (sameCenter : candidate.binder name = old.binder use.name)
    (value : Ty) (seen : Observes model origin value) :
    Equivalent value (model (candidate.binder name)).1 := by
  have readback := registered_actual old registered model valid use present actual
  rw [sameOrigin] at seen
  rw [sameCenter]
  exact readback.2.2 value (model (old.binder use.name)).1 seen (.source _)

 theorem registered_alias_readback (old candidate : Plan roles) (registered : old ∈ state.plans)
    (model : Assignment) (valid : Models state model) (use : GeneralNominalMaterialization.Use)
    (present : use ∈ old.headSchema.variables) (actual : use.mode = .actual)
    (rename : Nat → Nat)
    (recorded : RootRecorded state.erased.current.context.state rename use.origin)
    (name : Nat) (sameCenter : candidate.binder name = old.binder use.name)
    (value : Ty) (seen : Observes model (mapSource rename use.origin) value) :
    Equivalent value (model (candidate.binder name)).1 := by
  have related := recorded_root_similar state.erased.current.context.state model valid.1.1 rename use.origin recorded
  obtain ⟨other,observed,equal⟩ := related.2 value seen
  have oldReadback := registered_readback old candidate registered model valid use present actual
    use.origin rfl name sameCenter other observed
  exact ⟨subtype_trans equal.1 oldReadback.1,subtype_trans oldReadback.2 equal.2⟩

end Yulang.GeneralNominalLedgerReadback181
