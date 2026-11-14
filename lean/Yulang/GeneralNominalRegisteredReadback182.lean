import Yulang.GeneralNominalLedgerReadback181

/-! Readback for every schema already interpreted by a registered centered plan.
Capture bounds and site bounds are kept separate from actual-origin equations. -/
namespace Yulang.GeneralNominalRegisteredReadback182
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredSteps GeneralNominalRecursiveInspection
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalMaterialization (Schema Use)
open CommonNominalFullCarrier
open GeneralNominalOriginAlias181 (mapSource)
open GeneralNominalOriginRootAlias181 (RootRecorded recorded_root_similar)

variable {roles : Roles.RoleDecls} {state : State roles} {model : Assignment}

/-- Exactly the schema locations present in Plan.Equations. -/
inductive SchemaLocation (plan : Plan roles) : Schema → Prop where
  | head : SchemaLocation plan plan.headSchema
  | input : SchemaLocation plan (GeneralNominalPacketSupport.inputSchema plan.packet)
  | named : SchemaLocation plan (GeneralNominalPacketSupport.namedSchema plan.packet)
  | child (clause : Clause) (member : clause ∈ plan.packet.declaration.requirements)
      (valid : clause.Signature roles) :
      SchemaLocation plan (plan.schema (plan.childRequests clause valid))

theorem equations_schema (plan : Plan roles) (valid : plan.Equations model)
    (location : SchemaLocation plan schema) : plan.SchemaHolds schema model := by
  cases location with
  | head => exact valid.2.2.1
  | input => exact valid.2.2.2.1
  | named => exact valid.2.2.2.2.1
  | child clause member signature => exact (valid.2.2.2.2.2 clause member signature).2

theorem registered_schema (plan : Plan roles) (registered : plan ∈ state.plans)
    (valid : Models state model) (location : SchemaLocation plan schema) :
    plan.SchemaHolds schema model :=
  equations_schema plan (valid.2.2 plan registered) location

theorem registered_actual (plan : Plan roles) (registered : plan ∈ state.plans)
    (valid : Models state model) (location : SchemaLocation plan schema)
    (entry : Use) (present : entry ∈ schema.variables) (actual : entry.mode = .actual) :
    GeneralNominalOriginTerms.Same model entry.origin (.source (plan.binder entry.name)) := by
  have equation := (registered_schema plan registered valid location).2 entry present
  simpa only [actual,ite_true] using equation

theorem registered_readback (plan : Plan roles) (registered : plan ∈ state.plans)
    (valid : Models state model) (location : SchemaLocation plan schema)
    (entry : Use) (present : entry ∈ schema.variables) (actual : entry.mode = .actual)
    (value : Ty) (seen : Observes model entry.origin value) :
    Equivalent value (model (plan.binder entry.name)).1 :=
  (registered_actual plan registered valid location entry present actual).2.2
    value (model (plan.binder entry.name)).1 seen (.source _)

theorem registered_alias_readback (plan : Plan roles) (registered : plan ∈ state.plans)
    (valid : Models state model) (location : SchemaLocation plan schema)
    (entry : Use) (present : entry ∈ schema.variables) (actual : entry.mode = .actual)
    (rename : Nat → Nat)
    (recorded : RootRecorded state.erased.current.context.state rename entry.origin)
    (value : Ty) (seen : Observes model (mapSource rename entry.origin) value) :
    Equivalent value (model (plan.binder entry.name)).1 := by
  have related := recorded_root_similar state.erased.current.context.state model valid.1.1
    rename entry.origin recorded
  obtain ⟨other,observed,equal⟩ := related.2 value seen
  have readback := registered_readback plan registered valid location entry present actual other observed
  exact ⟨subtype_trans equal.1 readback.1,subtype_trans readback.2 equal.2⟩

theorem registered_capture_fits (plan : Plan roles) (registered : plan ∈ state.plans)
    (valid : Models state model) (name : Nat)
    (needed : name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name) :
    GeneralNominalCaptureMerges.Fits model
      ((GeneralNominalPacketSupport.capture plan.packet).inputs name) (model (plan.binder name)).1 :=
  (valid.2.2 plan registered).2.1 name needed

theorem registered_site_fits (site : Site roles) (registered : site ∈ state.sites)
    (valid : Models state model) (index : Fin (roles site.occurrence.demand.role).arity) :
    GeneralNominalCaptureMerges.Fits model (site.occurrence.demand.arguments index)
      (model (site.center index)).1 :=
  valid.2.1 site registered index

theorem registered_input_fits (plan : Plan roles) (registered : plan ∈ state.plans)
    (valid : Models state model) (index : Fin (roles plan.input.occurrence.demand.role).arity) :
    GeneralNominalCaptureMerges.Fits model (plan.input.occurrence.demand.arguments index)
      (model (plan.input.center index)).1 :=
  (valid.2.2 plan registered).1 index

theorem registered_child_fits (plan : Plan roles) (registered : plan ∈ state.plans)
    (valid : Models state model) (clause : Clause) (member : clause ∈ plan.packet.declaration.requirements)
    (signature : clause.Signature roles)
    (index : Fin (roles (plan.childSite clause signature).occurrence.demand.role).arity) :
    GeneralNominalCaptureMerges.Fits model
      ((plan.childSite clause signature).occurrence.demand.arguments index)
      (model ((plan.childSite clause signature).center index)).1 :=
  (valid.2.2 plan registered).2.2.2.2.2 clause member signature |>.1 index

end Yulang.GeneralNominalRegisteredReadback182
