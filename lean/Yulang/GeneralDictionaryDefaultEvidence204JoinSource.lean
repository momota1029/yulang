import Yulang.GeneralDictionaryMatGuardTrace199
import Yulang.GeneralNominalCenteredHeadStepDefaults
import Yulang.GeneralDictionaryMatTerminalAssembly200
import Yulang.GeneralNominalProvenanceDeclarations
import Yulang.GeneralNominalCenteredTerminalObservations

set_option backward.isDefEq.respectTransparency false

/-! Two compatible scalar constructor aliases retain a syntactically distinct
output join. Its total meaning is Int union Int; partial inspection defers it. -/
namespace Yulang.GeneralDictionaryDefaultEvidence204JoinSource
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalCenters CommonNominalFullCarrier
open GeneralDeclarationExamples (constructors)

abbrev roles : Roles.RoleDecls := GeneralNominalCenteredHeadStepDefaults.roles
abbrev equation : Equation := ⟨17,0,.join (.app 2 []) (.app 42 [])⟩
abbrev declaration : Declaration := ⟨37,0,[.app 2 []],[],[equation],[]⟩
abbrev registry : Registry := ⟨constructors,roles,[declaration]⟩
abbrev interpretation : GeneralNominalInspection.Interpretation where
  primitives := fun name => if name = 2 ∨ name = 42 then some (.scalar .int) else none
  invariantNominal := fun name => name == 0
  disjoint := by intro name yes; simp_all
abbrev context : GeneralNominalCandidates.Context :=
  ⟨(GeneralNominalCenteredTerminalForkSource.context (some false)).state,interpretation⟩
abbrev snapshot := context.state
abbrev root : Occurrence roles := ⟨100,⟨0,fun _ => (1,1),[⟨0,1⟩],by
  intro output member; cases List.mem_singleton.mp member; exact ⟨some (.var 0),rfl⟩⟩⟩
abbrev start := GeneralNominalCenteredHeadMatStepJournal.initial context root
abbrev model := GeneralNominalCenteredTerminalObservations.model

theorem declaration_checked : DeclarationChecked constructors roles declaration := by
  constructor
  · refine ⟨rfl,?_,?_,by simp⟩
    · intro e member; cases List.mem_singleton.mp member; exact ⟨_,rfl⟩
    · intro name body found
      change (if name = 0 then some (some (Roles.Term.var 0)) else none) = some body at found
      split at found
      · cases found; exact Or.inr rfl
      · cases found
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,
      variablesArgs,Pattern.variables,equation,merge,variantRow]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors,equation]
  · intro clause member; cases member
  · intro clause member; cases member
  · intro clause member; cases member
  · intro clause member; cases member

theorem checked : Checked registry :=
  ⟨by simp,by intro d member; cases List.mem_singleton.mp member; exact declaration_checked⟩

theorem source : GeneralNominalSourceFormation.InitialSource registry context root where
  roles_agree := rfl
  metadata := by
    refine ⟨rfl,?_⟩
    intro name primitive found
    change (if name = 2 ∨ name = 42 then _ else none) = some primitive at found
    split at found
    · rename_i which
      cases found
      rcases which with rfl | rfl <;> exact ⟨⟨[],_⟩,rfl,rfl⟩
    · cases found
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
    · simp [normalize,normalizeArgs,GeneralNominalInspection.translate,interpretation,
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
      GeneralNominalCenteredHeadWFSource.ConstructorUse,interpretation,constructors,equation]
    rfl
  · intro role name body found
    change (if name = 0 then some (some (Roles.Term.var 0)) else none) = some (some body) at found
    split at found
    · cases found; trivial
    · cases found

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
    GeneralNominalInspection.translate,interpretation]

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


theorem head_model_any (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models snapshot assignment) : GeneralNominalCenteredHeadCandidates.HeadModels registry context root declaration [(1,1)] assignment := by
  constructor
  · unfold privateState
    rw [report_exact]
    apply (GeneralNominalState.extend_models ..).mpr
    refine ⟨(GeneralNominalAllocation.propagate_models ..).mpr ⟨valid,?_,?_⟩,?_⟩
    · simp [bindings,GeneralNominalAllocation.Compatible]
    · simp [bindings,GeneralNominalAllocation.merges,Declaration.inputNames,normalizeArgs,normalize,
        variablesArgs,Pattern.variables]
    · simp [selfChecks,PresenceNormalForm.All]
      exact subtype_refl _
  · rw [report_exact]; simp [ProjectionModels]

end Yulang.GeneralDictionaryDefaultEvidence204JoinSource
