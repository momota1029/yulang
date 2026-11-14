import Yulang.GeneralNominalSingleVariableModels189
import Yulang.GeneralNominalCenteredHeadWFFixtures
import Yulang.GeneralNominalCenteredTerminalObservations

set_option backward.isDefEq.respectTransparency false

/-! Positive variable-head leaf fixture reuses the concrete scalar source and
adds an explicit identity output. The actual WF boundary is unchanged. -/
namespace Yulang.GeneralNominalInitialNamedFixture189
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalCenters CommonNominalFullCarrier
open GeneralDeclarationExamples (constructors)

abbrev roles : Roles.RoleDecls := fun _ => GeneralDeclarationExamples.outputRole 0
abbrev declaration : Declaration := ⟨3,0,[.var 0],[],[⟨0,0,.var 0⟩],[]⟩
abbrev registry : Registry := ⟨constructors,roles,[declaration]⟩
abbrev context := GeneralNominalCenteredTerminalForkSource.context (some false)
abbrev snapshot := context.state
abbrev root : Occurrence roles := ⟨100,⟨0,fun _ => (1,1),[⟨0,1⟩],by
  intro output member; cases List.mem_singleton.mp member; exact ⟨none,rfl⟩⟩⟩
abbrev start := GeneralNominalCenteredHeadStepEffects.initial context root
abbrev model := GeneralNominalCenteredTerminalObservations.model

theorem declaration_checked : DeclarationChecked constructors roles declaration := by
  constructor
  · refine ⟨rfl,?_,?_,by simp⟩
    · intro equation member; cases List.mem_singleton.mp member; exact ⟨none,rfl⟩
    · intro name body found
      change (if name = 0 then some none else none) = some body at found
      split at found
      · rename_i same
        subst name
        cases found; exact Or.inl ⟨⟨0,0,.var 0⟩,by simp,rfl⟩
      · cases found
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped]
  · simp
  · simp
  · simp
  · simp

theorem checked : Checked registry :=
  ⟨by simp,by intro d member; cases List.mem_singleton.mp member; exact declaration_checked⟩

theorem source : GeneralNominalSourceFormation.InitialSource registry context root where
  roles_agree := rfl
  metadata := GeneralNominalCenteredTerminalForkSource.metadata (some false)
  linked := by
    constructor
    · intro index; constructor <;> simp [GeneralNominalState.sources,List.ofFn_succ]
    · intro output member; cases List.mem_singleton.mp member
      simp [GeneralNominalState.sources,List.ofFn_succ]
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
      GeneralNominalCenteredHeadWFSource.PatternsCovered,GeneralNominalCenteredHeadWFSource.PatternCovered]
  · intro role name body found
    change (if name = 0 then some none else none) = some (some body) at found
    split at found <;> cases found

theorem initial_source : (GeneralNominalCenteredHeadWFBoundary.boundary roles).Initial registry root start :=
  ⟨⟨context,[.app 2 []],source,(fun _ => rfl),ground,rfl⟩,coverage⟩

theorem reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadWFBoundary.boundary roles) registry root start :=
  ⟨start,initial_source,.refl⟩

theorem source_model : GeneralNominalState.Models snapshot model :=
  GeneralNominalCenteredTerminalObservations.source_model (some false)

theorem inhabited : GeneralNominalCenteredHeadStepEffects.Models start model := by
  apply GeneralNominalCenteredHeadStepEffects.initial_models.mpr
  exact (GeneralNominalCenteredSteps.point_initial_models _ _ (fun _ => rfl) _).mpr source_model

abbrev packet : GeneralNominalSaturationState.Packet roles :=
  ⟨registry,context,GeneralNominalDemandMerging.pointSite root,declaration,declaration_checked,[(1,1)]⟩
abbrev plan : Plan roles := ⟨packet,rootSite snapshot.seed root,rfl⟩
noncomputable abbrev children := packet.children

theorem query : GeneralNominalInspection.queries snapshot context.interpretation declaration = [.variables [0]] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation]

theorem report_exact : report context declaration [(1,1)] =
    { captures := [⟨0,((1 : Fin 3),(1 : Fin 3)),none⟩], checked := [((1 : Fin 3),(1 : Fin 3)),((1 : Fin 3),(1 : Fin 3))] } := by
  unfold report
  rw [query]
  simp [inspectMany,inspect,Report.append]

theorem head_model : GeneralNominalCenteredHeadCandidates.HeadModels registry context root declaration [(1,1)] model :=
  GeneralNominalSingleVariableModels189.head_models plan (1 : Fin 3) query rfl rfl model source_model

theorem prepared : GeneralNominalCenteredHeadCandidates.Prepared registry context root declaration := by
  refine ⟨source.metadata,?_,GeneralNominalSourceFormation.initial_fresh _ source _,
    [(1,1)],rfl,?_,model,head_model⟩
  · exact ⟨source.linked.1,by intro output member; cases member⟩
  · rw [report_exact]; exact ⟨rfl,rfl,rfl⟩

end Yulang.GeneralNominalInitialNamedFixture189
