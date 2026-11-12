import Yulang.GeneralDictionaryRecursiveEvidenceFacts

/-! Ordinary constraints and reserved identities do not change the inspection
view. Evidence transport retains the source dictionary and requires added
ordinary constraints in the model. Normalized-head refresh is not covered. -/
namespace Yulang.GeneralDictionaryOrdinaryTransport
open GeneralNominalRecursiveInspection
open GeneralNominalInspection (Query Bounds)
open GeneralNominalState (State)
open GeneralDeclarations
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCommonBridge (Assignment)
abbrev extendState (state : State) (reserved : List Nat) (atoms : List (PresenceNormalForm.Atom Nat))
    (allocated : List GeneralNominalIdentities.Origin) : State :=
  { state with reserved := state.reserved ++ reserved, ordinary := state.ordinary ++ atoms, allocated := state.allocated ++ allocated }


variable (allocated : List GeneralNominalIdentities.Origin)
variable (reserved : List Nat) (atoms : List (PresenceNormalForm.Atom Nat))

def capture (item : Capture state) : Capture (extendState state reserved atoms allocated) :=
  ⟨item.name,item.bounds,item.origin⟩
def report (item : Report state) : Report (extendState state reserved atoms allocated) :=
  ⟨item.captures.map (capture allocated reserved atoms),item.inspected,item.checked,item.blocked,
    item.conflicts,item.arity,item.anchors,item.tests⟩
@[simp] theorem report_append (first last : Report state) :
    report allocated reserved atoms (first.append last) =
      (report allocated reserved atoms first).append (report allocated reserved atoms last) := by
  simp [report,Report.append,List.map_append]
@[simp] theorem report_visit (bounds : Bounds state) (origin : Option Origin)
    (test : Test) (value : Report state) :
    report allocated reserved atoms (Report.visit bounds origin test value) =
      @Report.visit (extendState state reserved atoms allocated) bounds origin test (report allocated reserved atoms value) := by rfl
mutual
 theorem inspect_extended (state : State) (query : Query) (bounds : Bounds state)
     (origin : Option Origin) :
     inspect (extendState state reserved atoms allocated) query bounds origin =
       report allocated reserved atoms (inspect state query bounds origin) := by
   cases query with
   | variables names => simp only [inspect,report,capture,List.map_map,Function.comp_def]
   | deferred term => simp only [inspect,block,report]; rfl
   | scalar expected =>
     simp only [inspect,extendState]
     repeat' split
     all_goals rfl
   | node expected patterns =>
     have ih := inspectMany_extended state patterns
     simp only [extendState] at ih
     simp only [inspect,extendState]
     repeat' split
     all_goals try simp only [ih]
     all_goals rfl
   | nominal expected patterns =>
     have ih := inspectMany_extended state patterns
     simp only [extendState] at ih
     simp only [inspect,extendState]
     repeat' split
     all_goals try simp only [ih,← report_append]
     all_goals rfl
 termination_by sizeOf query
 theorem inspectMany_extended (state : State) (queries : List Query) (bounds : List (Bounds state))
     (origins : Nat → Option Origin) (index : Nat) :
     inspectMany (extendState state reserved atoms allocated) queries bounds origins index =
       report allocated reserved atoms (inspectMany state queries bounds origins index) := by
   cases queries with
   | nil => cases bounds <;> simp only [inspectMany,report] <;> rfl
   | cons query queries =>
     cases bounds with
     | nil => simp only [inspectMany,report]; rfl
     | cons bound bounds =>
       rw [inspectMany,inspectMany,inspect_extended state query bound (origins index),inspectMany_extended state queries bounds origins (index+1),report_append]
 termination_by sizeOf queries
end

abbrev extend (context : GeneralNominalCandidates.Context) (reserved : List Nat)
    (atoms : List (PresenceNormalForm.Atom Nat)) (allocated : List GeneralNominalIdentities.Origin) :
    GeneralNominalCandidates.Context :=
  ⟨extendState context.state reserved atoms allocated,context.interpretation⟩


theorem models_extended (state : State) (model : Assignment) :
    GeneralNominalState.Models (extendState state reserved atoms allocated) model ↔
      GeneralNominalState.Models state model ∧ PresenceNormalForm.All CommonNominalFullCarrier.model model atoms := by
  change GeneralNominalState.Models (GeneralNominalState.extend state reserved atoms) model ↔ _
  exact GeneralNominalState.extend_models state reserved atoms model

theorem candidate_report_extended (context : GeneralNominalCandidates.Context)
    (declaration : Declaration) (bounds : List (Bounds context.state)) :
    GeneralNominalRecursiveCandidates.report (extend context reserved atoms allocated) declaration bounds =
      report allocated reserved atoms (GeneralNominalRecursiveCandidates.report context declaration bounds) := by
  unfold GeneralNominalRecursiveCandidates.report
  rw [inspectMany_extended]
  rfl

@[simp] theorem bindings_report (state : State) (value : Report state) :
    bindings (extendState state reserved atoms allocated) (report allocated reserved atoms value) =
      bindings state value := by
  simp [bindings,report,capture,extendState,List.map_map,Function.comp_def]

@[simp] theorem selfChecks_report (state : State) (value : Report state) :
    selfChecks (extendState state reserved atoms allocated) (report allocated reserved atoms value) =
      selfChecks state value := rfl

@[simp] theorem projection_report (state : State) (value : Report state) (model : Assignment) :
    ProjectionModels (extendState state reserved atoms allocated) (report allocated reserved atoms value) model ↔
      ProjectionModels state value model := by
  simp [ProjectionModels,report,capture,Fits,extendState]

@[simp] theorem materialization_report (state : State) (value : Report state)
    (declaration : Declaration) (captured : GeneralDeclarationDemands.Capture)
    (schema : GeneralNominalMaterialization.Schema) (model : Assignment) :
    GeneralNominalMaterialization.Models (extendState state reserved atoms allocated) declaration captured
      (report allocated reserved atoms value) schema model ↔
    GeneralNominalMaterialization.Models state declaration captured value schema model := by
  simp [GeneralNominalMaterialization.Models,report,capture]

@[simp] theorem generated_extended (context : GeneralNominalCandidates.Context) (registry : Registry)
    (root : Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (bounds : List (Bounds context.state)) :
    GeneralNominalRecursiveCandidates.generated registry (extend context reserved atoms allocated)
      root declaration checked bounds =
    GeneralNominalRecursiveCandidates.generated registry context root declaration checked bounds := by
  unfold GeneralNominalRecursiveCandidates.generated
  rw [candidate_report_extended,bindings_report]
  rfl

theorem branch_extended_iff (context : GeneralNominalCandidates.Context) (registry : Registry)
    (root : Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (bounds : List (Bounds context.state)) (model : Assignment) :
    GeneralNominalRecursiveCandidates.BranchModels registry (extend context reserved atoms allocated)
      root declaration checked bounds model ↔
    GeneralNominalRecursiveCandidates.BranchModels registry context root declaration checked bounds model ∧
      PresenceNormalForm.All CommonNominalFullCarrier.model model atoms := by
  rw [GeneralDictionaryRecursiveEvidence.branch_models_iff,GeneralDictionaryRecursiveEvidence.branch_models_iff]
  simp only [candidate_report_extended,extend,bindings_report,selfChecks_report,projection_report,
    generated_extended,materialization_report,models_extended]
  change ((_ ∧ _) ∧ _ ∧ _ ∧ _ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _) ∧ _
  constructor
  · rintro ⟨⟨old,added⟩,a,b,c,d,e⟩
    exact ⟨⟨old,a,b,c,d,e⟩,added⟩
  · rintro ⟨⟨old,a,b,c,d,e⟩,added⟩
    exact ⟨⟨old,added⟩,a,b,c,d,e⟩


@[simp] theorem finished_report (state : State) (value : Report state) :
    Finished (report allocated reserved atoms value) ↔ Finished value := Iff.rfl

/-- The unchanged declaration and emitted child list are valid in the extended
snapshot exactly when they were valid before and all new atoms hold. -/
theorem instance_extend_iff (registry : Registry) (context : GeneralNominalCandidates.Context)
    (model : Assignment) (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles)) :
    GeneralDictionaryRecursiveEvidence.Instance registry (extend context reserved atoms allocated) model root key children ↔
      GeneralDictionaryRecursiveEvidence.Instance registry context model root key children ∧
        PresenceNormalForm.All CommonNominalFullCarrier.model model atoms := by
  simp only [GeneralDictionaryRecursiveEvidence.Instance,GeneralNominalRecursiveCandidates.RequestReady,
    candidate_report_extended,bindings_report,generated_extended,branch_extended_iff,finished_report]
  constructor
  · rintro ⟨declaration,visible,checked,identity,role,bounds,located,finished,ready,children,metadata,branch,added⟩
    exact ⟨⟨declaration,visible,checked,identity,role,bounds,located,finished,ready,children,metadata,branch⟩,added⟩
  · rintro ⟨⟨declaration,visible,checked,identity,role,bounds,located,finished,ready,children,metadata,branch⟩,added⟩
    exact ⟨declaration,visible,checked,identity,role,bounds,located,finished,ready,children,metadata,branch,added⟩

/-- The exact same raw payload and source-indexed witness survive, including
all child obligations; added atoms are required once at the common model. -/
theorem evidence_extend_iff (registry : Registry) (context : GeneralNominalCandidates.Context)
    (model : Assignment) (root : Occurrence roles) (payload : GeneralDictionaryReadback.Payload) :
    GeneralDictionaryRecursiveEvidence.Evidence registry (extend context reserved atoms allocated) model root payload ↔
      GeneralDictionaryRecursiveEvidence.Evidence registry context model root payload ∧
        PresenceNormalForm.All CommonNominalFullCarrier.model model atoms := by
  constructor
  · rintro ⟨tree,readback,given⟩
    have added : PresenceNormalForm.All CommonNominalFullCarrier.model model atoms := by
      cases given with
      | node localRule children =>
        exact ((instance_extend_iff allocated reserved atoms registry context model _ _ _).mp localRule).2
    refine ⟨⟨tree,readback,?_⟩,added⟩
    exact GeneralSourceDictionaries.evidence_mono _ _
      (fun occurrence key children rule =>
        ((instance_extend_iff allocated reserved atoms registry context model occurrence key children).mp rule).1) given
  · rintro ⟨⟨tree,readback,given⟩,added⟩
    refine ⟨tree,readback,?_⟩
    exact GeneralSourceDictionaries.evidence_mono _ _
      (fun occurrence key children rule =>
        (instance_extend_iff allocated reserved atoms registry context model occurrence key children).mpr ⟨rule,added⟩) given

end Yulang.GeneralDictionaryOrdinaryTransport
