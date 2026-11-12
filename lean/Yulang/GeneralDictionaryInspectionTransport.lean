import Yulang.GeneralDictionaryRecursiveEvidenceFacts
import Yulang.GeneralNominalUnaryCaptureFacts

/-!
# Source evidence under inspection-preserving reobservation

Only the normalized view and nominal descriptor table change. Source slots,
allocation seed, ordinary constraints, constructor catalogue and interpretation
stay fixed. A report-equality premise is a finite computed inspection condition,
not a premise about Instance, Evidence, candidate choice or execution. The target
model is explicit: changing descriptors can change the set of state models.
This is not invariance under arbitrary descriptor refresh and does not close
V4 evidenceNode by itself.
-/
namespace Yulang.GeneralDictionaryInspectionTransport
open GeneralDeclarations
open GeneralNominalRecursiveCandidates (Context report arguments generated RequestReady)
open GeneralNominalRecursiveInspection
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCommonBridge (Assignment)

/-- An alternative observation on the same source carrier and allocation seed. -/
structure Observation (state : GeneralNominalState.State) where
  view : GeneralNormalizedObservation.Snapshot state.base
  nominals : Fin state.base.slots → Option (GeneralNominalState.Descriptor state.base.slots)
  catalogue : ∀ slot descriptor, nominals slot = some descriptor →
    state.constructors descriptor.constructor = some descriptor.declaration
  bodiesOpaque : ∀ slot descriptor, nominals slot = some descriptor →
    view.heads slot = .deferred .unresolved

abbrev reobserve (context : Context) (next : Observation context.state) : Context :=
  ⟨{ context.state with
      view := next.view
      nominals := next.nominals
      catalogue := next.catalogue
      bodies_opaque := next.bodiesOpaque }, context.interpretation⟩

def capture (context : Context) (next : Observation context.state)
    (value : Capture context.state) : Capture (reobserve context next).state :=
  ⟨value.name,value.bounds,value.origin⟩

def transferReport (context : Context) (next : Observation context.state)
    (value : Report context.state) : Report (reobserve context next).state :=
  ⟨value.captures.map (capture context next),value.inspected,value.checked,value.blocked,
    value.conflicts,value.arity,value.anchors,value.tests⟩

@[simp] theorem transferred_bindings (context : Context) (next : Observation context.state)
    (value : Report context.state) :
    bindings (reobserve context next).state (transferReport context next value) =
      bindings context.state value := by
  simp [bindings,transferReport,capture,reobserve,List.map_map,Function.comp_def]

@[simp] theorem transferred_selfChecks (context : Context) (next : Observation context.state)
    (value : Report context.state) :
    selfChecks (reobserve context next).state (transferReport context next value) =
      selfChecks context.state value := rfl

@[simp] theorem transferred_finished (context : Context) (next : Observation context.state)
    (value : Report context.state) :
    Finished (transferReport context next value) ↔ Finished value := Iff.rfl

@[simp] theorem transferred_projection (context : Context) (next : Observation context.state)
    (value : Report context.state) (model : Assignment) :
    ProjectionModels (reobserve context next).state (transferReport context next value) model ↔
      ProjectionModels context.state value model := by
  simp [ProjectionModels,transferReport,capture,Fits,reobserve]

@[simp] theorem transferred_materialization (context : Context) (next : Observation context.state)
    (value : Report context.state) (declaration : Declaration)
    (captured : GeneralDeclarationDemands.Capture)
    (schema : GeneralNominalMaterialization.Schema) (model : Assignment) :
    GeneralNominalMaterialization.Models (reobserve context next).state declaration captured
      (transferReport context next value) schema model ↔
    GeneralNominalMaterialization.Models context.state declaration captured value schema model := by
  simp [GeneralNominalMaterialization.Models,transferReport,capture]

/-- A concrete sufficient locality condition: only the queried unary nominal
head descriptor must survive. All other descriptors and normalized heads may
change arbitrarily. Its variable child is captured, not recursively inspected. -/
theorem nominal_unary_report (context : Context) (next : Observation context.state)
    (declaration : Declaration) (slot : Fin context.state.base.slots)
    (descriptor : GeneralNominalState.Descriptor context.state.base.slots)
    (old : context.state.nominals slot = some descriptor)
    (kept : next.nominals slot = some descriptor)
    (binder : Nat) (bounds : GeneralNominalInspection.Bounds context.state)
    (parameters : descriptor.arguments = [.type bounds])
    (query : GeneralNominalInspection.queries context.state context.interpretation declaration =
      [.nominal descriptor.declaration.name [.variables [binder]]]) :
    report (reobserve context next) declaration [(slot,slot)] =
      transferReport context next (report context declaration [(slot,slot)]) := by
  rw [GeneralNominalUnaryCaptureFacts.report_exact context declaration slot descriptor
    old binder bounds parameters query]
  rw [GeneralNominalUnaryCaptureFacts.report_exact (reobserve context next) declaration slot
    descriptor kept binder bounds parameters query]
  rfl

/-- Generated requests depend on the computed captures, not directly on the
nominal descriptor table. Equal reports preserve their entire schema. -/
theorem generated_eq (registry : Registry) (context : Context) (next : Observation context.state)
    (root : Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (bounds : List (GeneralNominalInspection.Bounds context.state))
    (same : report (reobserve context next) declaration bounds =
      transferReport context next (report context declaration bounds)) :
    generated registry (reobserve context next) root declaration checked bounds =
      generated registry context root declaration checked bounds := by
  unfold generated
  rw [same,transferred_bindings]
  rfl

/-- In the target model, every semantic branch obligation apart from the state
model itself is retained by an unchanged computed inspection report. -/
theorem branch_of_report (registry : Registry) (context : Context) (next : Observation context.state)
    (root : Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (bounds : List (GeneralNominalInspection.Bounds context.state)) (model : Assignment)
    (same : report (reobserve context next) declaration bounds =
      transferReport context next (report context declaration bounds))
    (valid : GeneralNominalState.Models (reobserve context next).state model)
    (old : GeneralNominalRecursiveCandidates.BranchModels registry context root declaration checked bounds model) :
    GeneralNominalRecursiveCandidates.BranchModels registry (reobserve context next)
      root declaration checked bounds model := by
  rw [GeneralDictionaryRecursiveEvidence.branch_models_iff] at old ⊢
  rw [same,transferred_bindings,transferred_selfChecks,transferred_projection,
    generated_eq registry context next root declaration checked bounds same]
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧
    GeneralNominalMaterialization.Models (reobserve context next).state declaration
      (GeneralNominalAllocation.capture context.state registry root.identity declaration.id
        (bindings context.state (report context declaration bounds)))
      (transferReport context next (report context declaration bounds))
      (generated registry context root declaration checked bounds) model
  rw [transferred_materialization]
  exact ⟨valid,old.2⟩

/-- The report guard is limited to declarations actually visible at this root,
and to bounds actually located there. It is not an instance/evidence premise. -/
def PreservesAt (registry : Registry) (context : Context) (next : Observation context.state)
    (root : Occurrence roles) : Prop :=
  ∀ declaration ∈ registry.declarations, declaration.role = root.demand.role →
    ∀ bounds, arguments context root = some bounds →
      report (reobserve context next) declaration bounds =
        transferReport context next (report context declaration bounds)

/-- The declaration key, exact canonical ordered child list and model are
preserved. No new choice or existential model is substituted. -/
theorem instance_of_reports (registry : Registry) (context : Context) (next : Observation context.state)
    (model : Assignment) (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (same : PreservesAt registry context next root)
    (valid : GeneralNominalState.Models (reobserve context next).state model)
    (old : GeneralDictionaryRecursiveEvidence.Instance registry context model root key children) :
    GeneralDictionaryRecursiveEvidence.Instance registry (reobserve context next) model root key children := by
  obtain ⟨declaration,visible,checked,identity,role,bounds,located,finished,ready,emitted,metadata,branch⟩ := old
  have reports := same declaration visible role bounds located
  refine ⟨declaration,visible,checked,identity,role,bounds,located,?_,?_,?_,metadata,
    branch_of_report registry context next root declaration checked bounds model reports valid branch⟩
  · rw [reports,transferred_finished]
    exact finished
  · unfold RequestReady at ready ⊢
    rw [generated_eq registry context next root declaration checked bounds reports]
    exact ready
  · rw [reports,transferred_bindings]
    exact emitted

/-- For a refreshed parent, child dictionaries are checked in the new context.
Only the parent's reports need preservation; child descriptors may change. -/
theorem node_of_reports (registry : Registry) (context : Context) (next : Observation context.state)
    (model : Assignment) (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (dictionaries : List GeneralDictionaryReadback.Payload)
    (same : PreservesAt registry context next root)
    (valid : GeneralNominalState.Models (reobserve context next).state model)
    (old : GeneralDictionaryRecursiveEvidence.Instance registry context model root key children)
    (given : CommonRoleOutermostResolver.All₂
      (GeneralDictionaryRecursiveEvidence.Evidence registry (reobserve context next) model)
      children dictionaries) :
    GeneralDictionaryRecursiveEvidence.Evidence registry (reobserve context next) model root
      (.node key dictionaries) :=
  GeneralDictionaryRecursiveEvidence.evidence_node registry (reobserve context next) model
    root key children dictionaries
    (instance_of_reports registry context next model root key children same valid old) given

/-- Whole-tree transport: each occurrence inspected in the source witness must
retain its reports. The raw runtime payload is unchanged. -/
theorem evidence_of_reports (registry : Registry) (context : Context) (next : Observation context.state)
    (model : Assignment) (root : Occurrence roles) (payload : GeneralDictionaryReadback.Payload)
    (same : ∀ occurrence : Occurrence roles, PreservesAt registry context next occurrence)
    (valid : GeneralNominalState.Models (reobserve context next).state model)
    (old : GeneralDictionaryRecursiveEvidence.Evidence registry context model root payload) :
    GeneralDictionaryRecursiveEvidence.Evidence registry (reobserve context next) model root payload := by
  obtain ⟨tree,readback,given⟩ := old
  refine ⟨tree,readback,?_⟩
  exact GeneralSourceDictionaries.evidence_mono _ _
    (fun occurrence key children rule =>
      instance_of_reports registry context next model occurrence key children
        (same occurrence) valid rule) given

end Yulang.GeneralDictionaryInspectionTransport
