import Yulang.GeneralDictionaryMatGuardTrace199
import Yulang.GeneralNominalCenteredHeadStepDefaults
import Yulang.GeneralDictionaryMatTerminalAssembly200
import Yulang.GeneralNominalProvenanceDeclarations
import Yulang.GeneralNominalCenteredTerminalObservations

set_option backward.isDefEq.respectTransparency false

/-! A terminal scalar head with a positional role default at a distinct linked
source. That output source has no fixed head or nominal descriptor. The all-Int
assignment and a bottom-valued output assignment are both genuine models. -/
namespace Yulang.GeneralDictionaryDefaultGap206Source
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalCenters CommonNominalFullCarrier
open GeneralDeclarationExamples (constructors)

abbrev roles : Roles.RoleDecls := GeneralNominalCenteredHeadStepDefaults.roles
abbrev declaration : Declaration := ⟨37,0,[.app 2 []],[],[],[]⟩
abbrev registry : Registry := ⟨constructors,roles,[declaration]⟩
abbrev snapshot : GeneralNominalState.State :=
  { GeneralNominalCenteredTerminalForkSource.snapshot (some false) with
    nominals := fun _ => none
    catalogue := by intro slot d h; cases h
    bodies_opaque := by intro slot d h; cases h }
abbrev context : GeneralNominalCandidates.Context := ⟨snapshot,GeneralNominalExamples.interpretation⟩
abbrev root : Occurrence roles := ⟨100,⟨0,fun _ => (1,1),[⟨0,0⟩],by
  intro output member; cases List.mem_singleton.mp member; exact ⟨some (.var 0),rfl⟩⟩⟩
abbrev start := GeneralNominalCenteredHeadMatStepJournal.initial context root
abbrev model : GeneralNominalCommonBridge.Assignment := fun n => (.base .int,(GeneralNominalExamples.model n).2)
abbrev counter : GeneralNominalCommonBridge.Assignment := fun n => (if n = 1 ∨ n = 2 then .base .int else .bottom,(GeneralNominalExamples.model n).2)

theorem declaration_checked : DeclarationChecked constructors roles declaration := by
  constructor
  · refine ⟨rfl,by simp,?_,by simp⟩
    intro name body found
    change (if name = 0 then some (some (Roles.Term.var 0)) else none) = some body at found
    split at found
    · cases found; exact Or.inr rfl
    · cases found
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

theorem scalar (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models snapshot assignment) :
    Equivalent (assignment 1).1 (.base .int) := by
  exact valid.1.2.1 (1 : Fin 3) (.base .int) rfl

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
    exact scalar assignment valid

theorem coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation := by
  constructor
  · intro d member
    cases List.mem_singleton.mp member
    simp [GeneralNominalCenteredHeadWFSource.DeclarationCovered,
      GeneralNominalCenteredHeadWFSource.PatternsCovered,GeneralNominalCenteredHeadWFSource.PatternCovered,
      GeneralNominalCenteredHeadWFSource.ConstructorUse,GeneralNominalExamples.interpretation,constructors]
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

theorem assignment_model (assignment : GeneralNominalCommonBridge.Assignment)
    (one : (assignment 1).1 = .base .int) (two : (assignment 2).1 = .base .int) :
    GeneralNominalState.Models snapshot assignment := by
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · intro atom member
    simp only [GeneralNominalCenteredTerminalForkSource.base,GeneralSourceState.equationAtoms,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with (rfl | rfl) | (rfl | rfl)
    · change Subtype (assignment 1).1 (.base .int); rw [one]; exact subtype_refl _
    · change Subtype (.base .int) (assignment 1).1; rw [one]; exact subtype_refl _
    · change Subtype (assignment 2).1 (.base .int); rw [two]; exact subtype_refl _
    · change Subtype (.base .int) (assignment 2).1; rw [two]; exact subtype_refl _
  · intro slot term recorded
    by_cases zero : slot = 0
    · simp [GeneralNominalCenteredTerminalForkSource.base,zero,GeneralSourceState.Head.equation] at recorded
    · have equal : (.base .int : Core.PresenceGeneration.TyTerm (Fin 3)) = term := by
        simpa [GeneralNominalCenteredTerminalForkSource.base,zero,GeneralSourceState.Head.equation] using recorded
      subst term
      have casesSlot : slot = 1 ∨ slot = 2 := by
        have bound : slot.val < 3 := slot.isLt
        have nonzero : slot.val ≠ 0 := fun h => zero (Fin.ext h)
        rcases show slot.val = 1 ∨ slot.val = 2 by omega with h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext h)
      rcases casesSlot with rfl | rfl
      · change Equivalent (assignment 1).1 (.base .int); rw [one]; exact ⟨subtype_refl _,subtype_refl _⟩
      · change Equivalent (assignment 2).1 (.base .int); rw [two]; exact ⟨subtype_refl _,subtype_refl _⟩
  · intro interval member; cases member
  · intro slot d recorded; cases recorded
  · exact PresenceNormalForm.all_nil _ _

theorem source_model : GeneralNominalState.Models snapshot model := assignment_model _ rfl rfl
theorem counter_model : GeneralNominalState.Models snapshot counter := assignment_model _ rfl rfl

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

end Yulang.GeneralDictionaryDefaultGap206Source
