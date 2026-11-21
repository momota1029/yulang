import Yulang.GeneralRebaseCompiledInstall277
import Yulang.GeneralGeneratedNestedInitial299

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 22000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralPositiveForkSource309
open GeneralDeclarationExamples (roles constructors bareRole outputRole)
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalExamples (interpretation state context model state_models)
open GeneralNominalCenteredHeadWFSource
open GeneralNominalCenteredHeadWFFixtures (int_constructor list_constructor)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

abbrev loClause : Clause := ⟨10,0,[.var 0],[]⟩
abbrev hiClause : Clause := ⟨20,3,[.var 0],[]⟩
abbrev associated : Equation := ⟨30,0,.var 0⟩
abbrev parent : Declaration := ⟨1,1,[.app 0 [.var 0]],[hiClause,loClause],[associated],[]⟩
abbrev left : Declaration := ⟨2,0,[.app 2 []],[],[],[]⟩
abbrev right : Declaration := ⟨3,3,[.app 2 []],[],[],[]⟩
abbrev registry : Registry := ⟨constructors,roles,[right,parent,left]⟩
abbrev compiled : Registry := GeneralNominalCenteredHeadAllocEncoding.registry registry
abbrev root : Occurrence roles :=
  ⟨100,⟨1,fun _ => (0,0),[⟨0,1⟩],by intro o hit; cases List.mem_singleton.mp hit; exact ⟨none,rfl⟩⟩⟩
abbrev initial := GeneralNominalVersionedJournal232.initial (context true) root

theorem parent_signature : parent.Signature roles := by
  refine ⟨rfl,?_,?_,?_⟩
  · intro e member
    cases List.mem_singleton.mp member
    exact ⟨none,rfl⟩
  · intro name body present
    by_cases h : name = 0
    · subst name; exact Or.inl ⟨associated,List.mem_singleton_self _,rfl⟩
    · simp [roles,outputRole,h] at present
  · intro c member
    rcases List.mem_cons.mp member with same|tail
    · subst c; exact ⟨rfl,fun _ h => nomatch h⟩
    · cases List.mem_singleton.mp tail
      exact ⟨rfl,fun _ h => nomatch h⟩

theorem parent_checked : DeclarationChecked constructors roles parent := by
  constructor
  · exact parent_signature
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames,variablesArgs,Pattern.variables]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  · intro c member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl <;> exact ⟨rfl,rfl⟩
  · intro c member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl <;> exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro c member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl <;> unfold ConservativeSmaller <;> decide +kernel
  · intro c member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl <;> exact unary_descent 0 0

theorem left_checked : DeclarationChecked constructors roles left := by
  constructor
  · simp [Declaration.Signature,roles,bareRole]
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  all_goals simp

theorem right_checked : DeclarationChecked constructors roles right := by
  constructor
  · simp [Declaration.Signature,roles,bareRole]
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  all_goals simp

theorem checked : Checked registry := by
  refine ⟨by decide +kernel,?_⟩
  intro d member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl
  · exact right_checked
  · exact parent_checked
  · exact left_checked

theorem coverage : Coverage registry interpretation := by
  constructor
  · intro d member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl <;>
      simp [DeclarationCovered,PatternsCovered,PatternCovered,int_constructor,list_constructor]
  · intro r name body found
    simp only [roles,outputRole,GeneralDeclarationExamples.binaryRole,bareRole] at found
    split at found
    · by_cases n : name = 0 <;> simp [n] at found
    · split at found
      · by_cases n : name = 1 <;> simp [n] at found
      · split at found <;> cases found

theorem init_source : GeneralNominalSourceFormation.InitialSource registry (context true) root := by
  have fixture := GeneralDictionarySupportRecursiveExample.initial_source
  refine ⟨rfl,⟨rfl,fixture.metadata.2⟩,?_,?_,fixture.below_seed,rfl⟩
  · refine ⟨?_,?_⟩
    · intro i
      have a := GeneralNominalAllocationSupport.slot_source (state true) (0 : Fin 2)
      exact ⟨a,a⟩
    · intro x member
      cases List.mem_singleton.mp member
      exact GeneralNominalAllocationSupport.slot_source (state true) (1 : Fin 2)
  · intro m _ i
    exact subtype_refl _

theorem ground : GeneralNominalGroundAccessibility.GroundRoots (context true) root [.app 0 [.app 2 []]] :=
  GeneralNominalCenteredCompletionAliasTrace.ground

theorem actual_initial : (boundary roles).Initial registry root initial := by
  refine ⟨_,⟨context true,[.app 0 [.app 2 []]],init_source,(fun _ => rfl),ground,coverage,rfl⟩,rfl⟩

theorem init_reached : B4TargetV8.Reachable (boundary roles) registry root initial :=
  ⟨_,actual_initial,.refl⟩

theorem init_model : Models initial model :=
  (GeneralNominalVersionedJournal232.initial_models ..).mpr
    ⟨state_models true,GeneralNominalCenters.point_root_holds _ _ (fun _ => rfl) _⟩

end Yulang.GeneralPositiveForkSource309
