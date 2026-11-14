import Yulang.GeneralDictionaryMatScalarOutputs200
import Yulang.GeneralDictionaryMatGuardTrace199
import Yulang.GeneralNominalProvenanceDeclarations
import Yulang.GeneralNominalCenteredTerminalObservations

set_option backward.isDefEq.respectTransparency false

/-! Scalar-compatible syntax is not enough: target zero is nominal in the
current source. This is a distinct negative fixture, not a new prior target. -/
namespace Yulang.GeneralDictionaryMatScalarConflict200
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalCenters CommonNominalFullCarrier
open GeneralDeclarationExamples (constructors)

abbrev roles : Roles.RoleDecls := fun _ => GeneralNominalProvenanceDeclarations.outputRole 1 0
abbrev declaration : Declaration := ⟨37,0,[.app 2 []],[],[⟨43,0,.app 2 []⟩],[]⟩
abbrev registry : Registry := ⟨constructors,roles,[declaration]⟩
abbrev context := GeneralNominalCenteredTerminalForkSource.context (some false)
abbrev snapshot := context.state
abbrev root : Occurrence roles := ⟨100,⟨0,fun _ => (1,1),[⟨0,0⟩],by
  intro output member; cases List.mem_singleton.mp member; exact ⟨none,rfl⟩⟩⟩
abbrev start := GeneralNominalCenteredHeadMatStepJournal.initial context root
abbrev model := GeneralNominalCenteredTerminalObservations.model

theorem declaration_checked : DeclarationChecked constructors roles declaration := by
  constructor
  · simp [Declaration.Signature,Clause.Signature,Declared]
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,
      variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  · intro clause member; cases member
  · intro clause member; cases member
  · intro clause member; cases member
  · intro clause member; cases member

theorem checked : Checked registry :=
  ⟨by simp,by intro d member; cases List.mem_singleton.mp member; exact declaration_checked⟩

theorem source : GeneralNominalSourceFormation.InitialSource registry context root where
  roles_agree := rfl
  metadata := GeneralNominalCenteredTerminalForkSource.metadata (some false)
  linked := by
    constructor
    · intro index; constructor <;> simp [GeneralNominalState.sources,List.ofFn_succ]
    · intro output member; cases List.mem_singleton.mp member; simp [GeneralNominalState.sources,List.ofFn_succ]
  intervals := fun _ _ _ => subtype_refl _
  below_seed := (GeneralNominalCenteredTerminalForkSource.source (some false)).below_seed
  unallocated := rfl

theorem ground : GeneralNominalGroundAccessibility.GroundRoots context root [.app 2 []] := by
  refine ⟨rfl,?_⟩
  intro index
  let term : GeneralNominalOriginTerms.Expr Nat := .node (.scalar .int) Fin.elim0
  refine ⟨term,?_,?_⟩
  · refine ⟨?_,?_,?_⟩
    · simp [normalize,normalizeArgs,GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,
        GeneralNominalCompoundReadback.quote,term]
    · simp [term,GeneralNominalOriginTerms.Expr.leaves,List.ofFn_zero,GeneralNominalOriginTerms.arity]
    · exact ⟨trivial,fun index => Fin.elim0 index⟩
  · intro assignment valid
    exact GeneralNominalCenteredTerminalForkSource.scalar assignment valid 1 (by decide +kernel)

theorem coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation := by
  constructor
  · intro d member
    cases List.mem_singleton.mp member
    simp [GeneralNominalCenteredHeadWFSource.DeclarationCovered,
      GeneralNominalCenteredHeadWFSource.PatternsCovered,GeneralNominalCenteredHeadWFSource.PatternCovered,
      GeneralNominalCenteredHeadWFSource.ConstructorUse,GeneralNominalExamples.interpretation,constructors]
    rfl
  · intro role name body found
    change (if name = 0 then some none else none) = some (some body) at found
    split at found <;> cases found

theorem initial_source : (GeneralNominalCenteredHeadMatStepBoundary.boundary roles).Initial registry root start :=
  ⟨context,[.app 2 []],source,(fun _ => rfl),ground,coverage,rfl⟩

theorem reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadMatStepBoundary.boundary roles) registry root start :=
  ⟨start,initial_source,.refl⟩

theorem source_model : GeneralNominalState.Models snapshot model :=
  GeneralNominalCenteredTerminalObservations.source_model (some false)

theorem inhabited : GeneralNominalCenteredHeadMatStepJournal.Models start model :=
  (GeneralNominalCenteredHeadMatStepJournal.point_initial_models (fun _ => rfl)).mpr source_model

abbrev packet : GeneralNominalSaturationState.Packet roles :=
  ⟨registry,context,GeneralNominalDemandMerging.pointSite root,declaration,declaration_checked,[(1,1)]⟩
abbrev plan : Plan roles := ⟨packet,rootSite snapshot.seed root,rfl⟩
noncomputable abbrev children := packet.children

theorem query : GeneralNominalInspection.queries snapshot context.interpretation declaration = [.scalar .int] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation]

theorem report_exact : report context declaration [(1,1)] =
    { inspected := [((1 : Fin 3),(1 : Fin 3))], checked := [((1 : Fin 3),(1 : Fin 3)),((1 : Fin 3),(1 : Fin 3))] } := by
  unfold report
  rw [query]
  simp [inspectMany,inspect,Report.visit,Report.append]

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
    · simp [bindings,GeneralNominalAllocation.merges,Declaration.inputNames,normalizeArgs,normalize,
        variablesArgs,Pattern.variables]
    · simp [selfChecks,PresenceNormalForm.All]
      exact subtype_refl _
  · rw [report_exact]; simp [ProjectionModels]

theorem prepared : GeneralNominalCenteredHeadCandidates.Prepared registry context root declaration := by
  refine ⟨source.metadata,⟨source.linked.1,by intro output member; cases member⟩,GeneralNominalSourceFormation.initial_fresh _ source _,
    [(1,1)],rfl,?_,model,head_model⟩
  rw [report_exact]; exact ⟨rfl,rfl,rfl⟩


theorem frame : GeneralNominalCenteredHeadOutputs.Frame registry start.core root 37 plan :=
  ⟨rfl,rfl,rfl,rfl,List.mem_singleton_self _,List.mem_singleton_self _,List.mem_singleton_self _,rfl,rfl,prepared⟩

theorem head_schema : plan.headSchema = { tests := [(.source 1,.scalar .int)] } := by
  unfold Plan.headSchema
  rw [query]
  simp [GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,plan,rootSite,List.ofFn_succ]

theorem root_requests : GeneralNominalMaterialization.rootRequests declaration root =
    [⟨.app 2 [],0,.actual⟩] := rfl

theorem scalar_requests : GeneralDictionaryMatScalarOutputs200.ScalarRequests registry context
    (GeneralNominalMaterialization.rootRequests declaration root) := by
  rw [root_requests]
  intro request member
  cases List.mem_singleton.mp member
  refine ⟨.int,?_,rfl⟩
  simp [normalize,normalizeArgs,GeneralNominalInspection.translate,GeneralNominalExamples.interpretation]


theorem no_total_holds : ¬ GeneralNominalCenteredHeadMatStepPackets.Holds plan model := by
  intro holds
  have member : (⟨.app 2 [],0,.actual⟩ : GeneralNominalMaterialization.Request) ∈
      GeneralNominalCenteredHeadMatSchemas.requests snapshot registry root declaration declaration_checked packet.bindings := by
    apply List.mem_append_left
    rw [root_requests]
    exact List.mem_singleton_self _
  have equation := GeneralNominalCenteredHeadMatStepPackets.output_equation holds.2.2 member
    (show GeneralNominalCenteredHeadMatExpressions.translate registry.constructors context.interpretation
      (.app 2 []) = some (.primitive (.scalar .int) []) from rfl)
  exact GeneralNominalPeelingOrigins.base_not_nominal .int 0 [Sum.inl (.base .int)] equation.2

theorem requested_scalar : (.source 0,.scalar .int) ∈
    (generated registry context root declaration declaration_checked [(1,1)]).tests := by
  unfold generated
  rw [GeneralNominalFiniteAssociatedFacts.terminal_requests snapshot registry root declaration declaration_checked _ rfl]
  simp [GeneralNominalMaterialization.rootRequests,GeneralNominalMaterialization.generated,
    normalize,normalizeArgs,GeneralNominalInspection.translate,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,GeneralNominalExamples.interpretation]

theorem no_evidence : ¬ (GeneralNominalCenteredHeadMatStepBoundary.boundary roles).Evidence
    registry start model root (.node 37 []) := by
  intro evidence
  obtain ⟨decl,visible,check,_,_,bounds,located,_,_,_,_,branch⟩ :=
    (GeneralDictionaryRecursiveEvidence.evidence_leaf_iff registry context model root 37).mp evidence
  cases List.mem_singleton.mp visible
  have equal : [(1,1)] = bounds := Option.some.inj located
  subst bounds
  have equation := (branch.2.2.1 (.source 0,.scalar .int) requested_scalar).2 _ (.source 0)
  exact GeneralNominalPeelingOrigins.base_not_nominal .int 0 [Sum.inl (.base .int)] equation.2

/-- Even a real frame and compiler-compatible named request do not replace the
same-model full packet premise. The initial journal has not recorded this plan. -/
theorem source_not_total :
    GeneralNominalCenteredHeadMatStepJournal.Models start model ∧
    GeneralNominalCenteredHeadOutputs.Frame registry start.core root 37 plan ∧
    GeneralDictionaryMatScalarOutputs200.ScalarRequests registry context
      (GeneralNominalMaterialization.rootRequests declaration root) ∧
    ¬ GeneralNominalCenteredHeadMatStepPackets.Holds plan model :=
  ⟨inhabited,frame,scalar_requests,no_total_holds⟩

end Yulang.GeneralDictionaryMatScalarConflict200
