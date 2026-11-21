import Yulang.GeneralDepthTwoSafety300
import Yulang.GeneralRebaseCompiledInstall277

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 13000000
namespace Yulang.GeneralLatePeerSource311
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralDeclarationExamples (roles constructors bareRole binaryRole outputRole)
open GeneralGeneratedNestedSource299 (snapshot context model snapshot_model listDescriptor)
open GeneralNominalExamples (interpretation)
open GeneralNominalCenteredHeadWFSource
open GeneralNominalCenteredHeadWFFixtures (int_constructor list_constructor)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedJournal232 (Models)

abbrev atLeft : Clause := ⟨10,2,[.var 1],[⟨11,1,.var 5⟩]⟩
abbrev atRoute : Clause := ⟨20,0,[.var 0],[]⟩
abbrev makePeer : Clause := ⟨30,2,[.var 0],[]⟩
abbrev parent : Declaration := ⟨1,4,[.app 0 [.var 0],.app 0 [.var 1]],[atLeft,atRoute],[],[⟨5,10,11⟩]⟩
abbrev receiver : Declaration := ⟨2,2,[.app 2 []],[],[⟨40,1,.app 2 []⟩],[]⟩
abbrev route : Declaration := ⟨3,0,[.app 0 [.var 0]],[makePeer],[],[]⟩
abbrev registry : Registry := ⟨constructors,roles,[parent,receiver,route]⟩
abbrev compiled := GeneralNominalCenteredHeadAllocEncoding.registry registry
abbrev parentCode := GeneralNominalCenteredHeadAllocEncoding.declaration parent
abbrev leftCode := GeneralNominalCenteredHeadAllocEncoding.clause atLeft
abbrev routeCode := GeneralNominalCenteredHeadAllocEncoding.clause atRoute
abbrev root : Occurrence roles :=
  ⟨100,⟨4,fun i => (i.val,i.val),[],by intro _ h; cases h⟩⟩
abbrev initial := GeneralNominalVersionedJournal232.initial context root

private theorem strict {clause : Clause} (member : clause ∈ parent.requirements) :
    StableSmaller parent.head clause.arguments := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl
  all_goals
    intro capture
    constructor
    · simp only [counted,substArgs,Pattern.subst,normalizeArgs,normalize,encodeArgs,Pattern.encode,Roles.argsSize,Roles.Term.size]
      omega
    · intro name
      simp only [counted,substArgs,Pattern.subst,normalizeArgs,normalize,encodeArgs,Pattern.encode,Roles.argsOccurrences,Roles.Term.occurrences]
      omega

theorem parent_checked : DeclarationChecked constructors roles parent := by
  constructor
  · simp [Declaration.Signature,Clause.Signature,Declared,roles,bareRole,binaryRole,outputRole]
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames,variablesArgs,Pattern.variables]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  · intro c h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl <;> exact ⟨rfl,rfl⟩
  · intro c h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl <;> exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro c h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl <;> unfold ConservativeSmaller <;> decide +kernel
  · exact fun _ h => strict h

theorem receiver_checked : DeclarationChecked constructors roles receiver := by
  constructor
  · refine ⟨rfl,?_,?_,?_⟩
    · intro e h; cases List.mem_singleton.mp h; exact ⟨none,rfl⟩
    · intro n body h
      by_cases eq : n=1
      · subst n
        exact .inl ⟨_,List.mem_singleton_self _,rfl⟩
      · simp [roles,outputRole,eq] at h
    · intro _ h; cases h
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  all_goals simp

theorem route_checked : DeclarationChecked constructors roles route := by
  constructor
  · simp [Declaration.Signature,Clause.Signature,roles,bareRole]
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames,variablesArgs,Pattern.variables]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  · intro c eq; cases List.mem_singleton.mp eq; exact ⟨rfl,rfl⟩
  · intro c eq; cases List.mem_singleton.mp eq; exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro c eq; cases List.mem_singleton.mp eq; unfold ConservativeSmaller; decide +kernel
  · intro c eq; cases List.mem_singleton.mp eq; exact unary_descent 0 0

theorem checked : Checked registry := by
  refine ⟨by decide +kernel,?_⟩
  intro d seen
  simp only [List.mem_cons,List.not_mem_nil,or_false] at seen
  rcases seen with rfl|rfl|rfl
  · exact parent_checked
  · exact receiver_checked
  · exact route_checked

theorem coverage : Coverage registry interpretation := by
  constructor
  · intro d seen
    simp only [List.mem_cons,List.not_mem_nil,or_false] at seen
    rcases seen with rfl|rfl|rfl <;>
      simp [DeclarationCovered,PatternsCovered,PatternCovered,int_constructor,list_constructor]
  · intro r name body found
    simp only [roles,outputRole,binaryRole,bareRole] at found
    split at found
    · by_cases n : name=0 <;> simp [n] at found
    · split at found
      · by_cases n : name=1 <;> simp [n] at found
      · split at found <;> cases found

abbrev labels : List Pattern := [.app 0 [.app 0 [.app 2 []]],.app 0 [.app 2 []]]

theorem initial_source : GeneralNominalSourceFormation.InitialSource registry context root := by
  have existing := GeneralGeneratedNestedInitial299.initial_source
  refine ⟨rfl,⟨rfl,existing.metadata.2⟩,⟨?_,(by intro _ h; cases h)⟩,?_,existing.below_seed,rfl⟩
  · intro index
    let i : Fin snapshot.base.slots := ⟨index.val, by have b := index.isLt; change index.val < 2 at b; change index.val < 3; omega⟩
    have seen := GeneralNominalAllocationSupport.slot_source snapshot i
    exact ⟨seen,seen⟩
  · intro m _ _; exact CommonNominalFullCarrier.subtype_refl _

theorem ground : GeneralNominalGroundAccessibility.GroundRoots context root labels := by
  refine ⟨rfl,?_⟩
  intro i
  have ic : i.val = 0 ∨ i.val = 1 := by have b := i.isLt; change i.val < 2 at b; omega
  rcases ic with h|h
  · refine ⟨GeneralGeneratedNestedInitial299.sourceExpr,?_,?_⟩
    · simpa only [h,labels,GeneralGeneratedNestedInitial299.labels,List.getElem_cons_zero] using GeneralGeneratedNestedInitial299.closed_label
    · intro m valid
      change CommonNominalFullCarrier.Equivalent (m i.val).1 GeneralGeneratedNestedSource299.nestedTy
      rw [h]
      exact GeneralGeneratedNestedInitial299.two_levels m valid
  · refine ⟨GeneralGeneratedNestedInitial299.listExpr,?_,?_⟩
    · refine ⟨?_,rfl,⟨trivial,fun _ => ⟨trivial,fun i => Fin.elim0 i⟩⟩⟩
      simp [labels,h,GeneralDeclarationPatterns.normalize,GeneralDeclarationPatterns.normalizeArgs,
        GeneralNominalInspection.translate,interpretation,GeneralNominalCompoundReadback.quote,
        List.ofFn_succ,GeneralNominalOriginTerms.arity]
    · intro m valid
      change CommonNominalFullCarrier.Equivalent (m i.val).1 GeneralGeneratedNestedSource299.listTy
      rw [h]
      exact GeneralGeneratedNestedInitial299.one_level m valid

theorem actual_initial : (boundary roles).Initial registry root initial :=
  ⟨_,⟨context,labels,initial_source,(fun _ => rfl),ground,coverage,rfl⟩,rfl⟩

theorem init_reached : B4TargetV8.Reachable (boundary roles) registry root initial := ⟨_,actual_initial,.refl⟩

theorem initial_model : Models initial model :=
  (GeneralNominalVersionedJournal232.initial_models ..).mpr
    ⟨snapshot_model,GeneralNominalCenters.point_root_holds _ _ (fun _ => rfl) _⟩

end Yulang.GeneralLatePeerSource311
