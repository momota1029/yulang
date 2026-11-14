import Yulang.GeneralNominalCenteredHeadAllocExecutor
import Yulang.GeneralNominalCenteredModelExtension

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralNominalCenteredHeadAllocCollisionSource
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection CommonNominalFullCarrier

abbrev roles := GeneralNominalCenteredHeadMatCompletionCollisionSource.roles
abbrev sourceRegistry := GeneralNominalCenteredHeadMatCompletionCollisionSource.registry
abbrev registry := GeneralNominalCenteredHeadAllocEncoding.registry sourceRegistry
abbrev declaration := GeneralNominalCenteredHeadAllocEncoding.declaration GeneralNominalCenteredHeadMatCompletionCollisionSource.declaration
abbrev firstClause := GeneralNominalCenteredHeadAllocEncoding.clause GeneralNominalCenteredHeadMatCompletionCollisionSource.firstClause
abbrev lastClause := GeneralNominalCenteredHeadAllocEncoding.clause GeneralNominalCenteredHeadMatCompletionCollisionSource.lastClause
abbrev context := GeneralNominalCenteredHeadMatCompletionCollisionSource.context
abbrev snapshot := GeneralNominalCenteredHeadMatCompletionCollisionSource.snapshot
abbrev root := GeneralNominalCenteredHeadMatCompletionCollisionSource.root
abbrev start := GeneralNominalCenteredHeadMatCompletionCollisionSource.start

theorem declaration_checked : DeclarationChecked registry.constructors roles declaration := GeneralNominalCenteredHeadAllocEncoding.declaration_checked GeneralNominalCenteredHeadMatCompletionCollisionSource.declaration_checked
theorem checked : Checked registry := GeneralNominalCenteredHeadAllocEncoding.registry_checked GeneralNominalCenteredHeadMatCompletionCollisionSource.checked

theorem source : GeneralNominalSourceFormation.InitialSource registry context root := GeneralNominalCenteredHeadAllocEncoding.initial_source GeneralNominalCenteredHeadMatCompletionCollisionSource.source

theorem initial_source : (GeneralNominalCenteredHeadAllocBoundary.boundary roles).Initial sourceRegistry root start := GeneralNominalCenteredHeadMatCompletionCollisionSource.initial_source

theorem reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadAllocBoundary.boundary roles) sourceRegistry root start :=
  ⟨start,initial_source,.refl⟩

theorem compiled_reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadMatStepBoundary.boundary roles) registry root start :=
  GeneralNominalCenteredHeadAllocBoundary.reachable_compiled reachable

abbrev packet : GeneralNominalSaturationState.Packet roles :=
  ⟨registry,context,GeneralNominalDemandMerging.pointSite root,declaration,declaration_checked,[(1,1)]⟩
abbrev plan : Plan roles := ⟨packet,rootSite snapshot.seed root,rfl⟩
noncomputable abbrev children := packet.children

abbrev firstTarget := GeneralNominalAllocation.source snapshot registry root.identity
  (GeneralNominalAllocation.origin root.identity declaration.id 5 (GeneralNominalIdentities.pair 42 43) 0)
abbrev lastTarget := GeneralNominalAllocation.source snapshot registry root.identity
  (GeneralNominalAllocation.origin root.identity declaration.id 5 (GeneralNominalIdentities.pair 44 43) 0)

theorem targets_distinct : firstTarget ≠ lastTarget := by
  intro same
  have identity := (GeneralNominalIdentities.source_identity snapshot.seed _ _).mp same
  have pair := congrArg (fun key : GeneralNominalIdentities.Origin => key.2.2.2.1) identity
  have clause := (GeneralNominalCenteredHeadAllocEncoding.equation_key.mp pair).1
  contradiction

theorem last_above_seed : snapshot.seed < lastTarget := GeneralNominalIdentities.source_above_seed ..
theorem first_above_seed : snapshot.seed < firstTarget := GeneralNominalIdentities.source_above_seed ..

def model : GeneralNominalCommonBridge.Assignment := fun identity =>
  if identity = lastTarget then (variant 0 (.base .int),Common.rowEmpty) else GeneralNominalCenteredHeadMatCompletionCollisionSource.model identity

theorem model_old (member : identity ∈ GeneralNominalState.sources snapshot) : model identity = GeneralNominalCenteredHeadMatCompletionCollisionSource.model identity := by
  have bounded := GeneralNominalCenteredHeadMatCompletionCollisionSource.source.below_seed identity member
  change identity ≤ snapshot.seed at bounded
  have larger := last_above_seed
  have different : identity ≠ lastTarget := by omega
  exact ite_eq_right different

theorem model_one : model 1 = GeneralNominalCenteredHeadMatCompletionCollisionSource.model 1 := model_old (GeneralNominalAllocationSupport.slot_source snapshot (1 : Fin 3))

theorem source_model : GeneralNominalState.Models snapshot model :=
  GeneralNominalCenteredModelExtension.source_models_same snapshot (fun _ member => (model_old member).symm) GeneralNominalCenteredHeadMatCompletionCollisionSource.source_model

theorem inhabited : GeneralNominalCenteredHeadMatStepJournal.Models start model :=
  (GeneralNominalCenteredHeadMatStepJournal.point_initial_models (fun _ => rfl)).mpr source_model

theorem query : GeneralNominalInspection.queries snapshot context.interpretation declaration = [.scalar .int] := GeneralNominalCenteredHeadMatCompletionCollisionSource.query

theorem report_exact : report context declaration [(1,1)] =
    { inspected := [((1 : Fin 3),(1 : Fin 3))], checked := [((1 : Fin 3),(1 : Fin 3)),((1 : Fin 3),(1 : Fin 3))] } := GeneralNominalCenteredHeadMatCompletionCollisionSource.report_exact

theorem bindings_empty : packet.bindings = [] := by
  change bindings snapshot (report context declaration [(1,1)]) = []
  rw [report_exact]; rfl

theorem head_model : GeneralNominalCenteredHeadCandidates.HeadModels registry context root declaration [(1,1)] model := by
  constructor
  · unfold privateState
    rw [report_exact]
    apply (GeneralNominalState.extend_models ..).mpr
    refine ⟨(GeneralNominalAllocation.propagate_models ..).mpr ⟨source_model,?_,?_⟩,?_⟩
    · simp [bindings,GeneralNominalAllocation.Compatible]
    · have names : declaration.inputNames = [] := rfl
      simp [bindings,GeneralNominalAllocation.merges,names]
    · simp [selfChecks,PresenceNormalForm.All]
      exact subtype_refl _
  · rw [report_exact]; simp [ProjectionModels]

theorem prepared : GeneralNominalCenteredHeadCandidates.Prepared registry context root declaration := by
  refine ⟨source.metadata,source.linked,GeneralNominalSourceFormation.initial_fresh _ source _,
    [(1,1)],rfl,?_,model,head_model⟩
  rw [report_exact]; exact ⟨rfl,rfl,rfl⟩

end Yulang.GeneralNominalCenteredHeadAllocCollisionSource
