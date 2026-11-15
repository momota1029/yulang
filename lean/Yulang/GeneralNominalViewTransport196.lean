import Yulang.GeneralDictionaryOrdinaryTransport

/-! Descriptor-changing reinspection transport. The source/allocation skeleton
is fixed, but normalized heads and nominal descriptors may change. Report
agreement is a structural condition, not a semantic dictionary premise. -/
set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralNominalViewTransport196
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalRecursiveInspection
open GeneralNominalInspection (Bounds)
open GeneralNominalState (State)
open GeneralNominalCommonBridge (Assignment)

structure View (state : State) where
  view : GeneralNormalizedObservation.Snapshot state.base
  nominals : Fin state.base.slots → Option (GeneralNominalState.Descriptor state.base.slots)
  catalogue : ∀ slot descriptor, nominals slot = some descriptor →
    state.constructors descriptor.constructor = some descriptor.declaration
  opaqueHeads : ∀ slot descriptor, nominals slot = some descriptor →
    view.heads slot = .deferred .unresolved

def replace (state : State) (next : View state) : State :=
  { state with view := next.view, nominals := next.nominals, catalogue := next.catalogue, bodies_opaque := next.opaqueHeads }

def context (old : GeneralNominalCandidates.Context) (next : View old.state) :
    GeneralNominalCandidates.Context := ⟨replace old.state next,old.interpretation⟩

def capture (next : View state) (item : Capture state) : Capture (replace state next) :=
  ⟨item.name,item.bounds,item.origin⟩
def report (next : View state) (item : Report state) : Report (replace state next) :=
  ⟨item.captures.map (capture next),item.inspected,item.checked,item.blocked,
    item.conflicts,item.arity,item.anchors,item.tests⟩

variable {old : GeneralNominalCandidates.Context} {next : View old.state}
variable {declaration : Declaration} {bounds : List (Bounds old.state)}

/-- Re-run the real inspector and compare its finite output, not Evidence. -/
def Rechecked (old : GeneralNominalCandidates.Context) (next : View old.state)
    (declaration : Declaration) (bounds : List (Bounds old.state)) : Prop :=
  GeneralNominalRecursiveCandidates.report (context old next) declaration bounds =
    report next (GeneralNominalRecursiveCandidates.report old declaration bounds)

@[simp] theorem bindings_report (state : State) (next : View state) (value : Report state) :
    bindings (replace state next) (report next value) = bindings state value := by
  simp only [bindings,report,List.map_map]
  rfl

@[simp] theorem selfChecks_report (state : State) (next : View state) (value : Report state) :
    selfChecks (replace state next) (report next value) = selfChecks state value := rfl

@[simp] theorem projection_report (state : State) (next : View state) (value : Report state)
    (model : Assignment) :
    ProjectionModels (replace state next) (report next value) model ↔
      ProjectionModels state value model := by
  simp [ProjectionModels,report,GeneralNominalViewTransport196.capture,Fits,replace]

@[simp] theorem materialization_report (state : State) (next : View state) (value : Report state)
    (decl : Declaration) (captured : GeneralDeclarationDemands.Capture)
    (schema : GeneralNominalMaterialization.Schema) (model : Assignment) :
    GeneralNominalMaterialization.Models (replace state next) decl captured (report next value) schema model ↔
      GeneralNominalMaterialization.Models state decl captured value schema model := by
  simp [GeneralNominalMaterialization.Models,report,capture]

@[simp] theorem finished_report (state : State) (next : View state) (value : Report state) :
    Finished (report next value) ↔ Finished value := Iff.rfl

 theorem generated_eq (checkedReport : Rechecked old next declaration bounds)
    (registry : Registry) (root : Occurrence roles)
    (checked : DeclarationChecked registry.constructors roles declaration) :
    GeneralNominalRecursiveCandidates.generated registry (context old next) root declaration checked bounds =
      GeneralNominalRecursiveCandidates.generated registry old root declaration checked bounds := by
  unfold GeneralNominalRecursiveCandidates.generated
  rw [checkedReport]
  simp only [context,bindings_report]
  rfl

 theorem branch_transport (checkedReport : Rechecked old next declaration bounds)
    (registry : Registry) (root : Occurrence roles)
    (checked : DeclarationChecked registry.constructors roles declaration) (model : Assignment)
    (valid : GeneralNominalState.Models (replace old.state next) model)
    (branch : GeneralNominalRecursiveCandidates.BranchModels registry old root declaration checked bounds model) :
    GeneralNominalRecursiveCandidates.BranchModels registry (context old next) root declaration checked bounds model := by
  rw [GeneralDictionaryRecursiveEvidence.branch_models_iff] at branch ⊢
  rw [generated_eq checkedReport]
  change GeneralNominalRecursiveCandidates.report (context old next) declaration bounds = _ at checkedReport
  rw [checkedReport]
  simp only [context,bindings_report,selfChecks_report,projection_report,materialization_report]
  exact ⟨valid,branch.2⟩

/-- Report equality need only be supplied for declarations actually in this registry. -/
def Rechecks (registry : Registry) (old : GeneralNominalCandidates.Context)
    (next : View old.state) : Prop :=
  ∀ declaration ∈ registry.declarations, ∀ bounds, Rechecked old next declaration bounds

 theorem instance_transport (registry : Registry) (rechecked : Rechecks registry old next)
    (model : Assignment) (valid : GeneralNominalState.Models (replace old.state next) model)
    (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (source : GeneralDictionaryRecursiveEvidence.Instance registry old model root key children) :
    GeneralDictionaryRecursiveEvidence.Instance registry (context old next) model root key children := by
  obtain ⟨decl,visible,checked,identity,role,bs,located,finished,ready,kids,metadata,branch⟩ := source
  have same := rechecked decl visible bs
  refine ⟨decl,visible,checked,identity,role,bs,located,?_,?_,?_,metadata,?_⟩
  · rw [same]; exact finished
  · unfold GeneralNominalRecursiveCandidates.RequestReady at ready ⊢
    rw [generated_eq same]; exact ready
  · rw [same]
    simp only [context,bindings_report]
    exact kids
  · exact branch_transport same registry root checked model valid branch

/-- Every source node is transported; the complete dictionary and raw payload
are retained, with all children interpreted in this same supplied assignment. -/
 theorem evidence_transport (registry : Registry) (rechecked : Rechecks registry old next)
    (model : Assignment) (valid : GeneralNominalState.Models (replace old.state next) model)
    (root : Occurrence roles) (payload : GeneralDictionaryReadback.Payload)
    (source : GeneralDictionaryRecursiveEvidence.Evidence registry old model root payload) :
    GeneralDictionaryRecursiveEvidence.Evidence registry (context old next) model root payload := by
  obtain ⟨tree,readback,evidence⟩ := source
  exact ⟨tree,readback,GeneralSourceDictionaries.evidence_mono _ _
    (fun focus key children rule => instance_transport registry rechecked model valid focus key children rule) evidence⟩
end Yulang.GeneralNominalViewTransport196
