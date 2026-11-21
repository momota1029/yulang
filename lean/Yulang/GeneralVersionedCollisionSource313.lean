import Yulang.GeneralVersionedFirstComputed313
import Yulang.GeneralDictionaryCompoundStep238

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
/-! Cross-clause duplicate output IDs are accepted by the actual checked
registry contract. The two clauses share a compound argument but their
private computed outputs are different constructors. -/
namespace Yulang.GeneralVersionedCollisionSource313
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralDictionaryJournalRefinement228Source
open GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedTraceSupport237 (Reachable)

abbrev width : GeneralDeclarations.Equation := ⟨17,0,.app 2 []⟩
abbrev exact : GeneralDeclarations.Equation := ⟨17,0,.app 3 []⟩
abbrev left : Clause := ⟨0,0,[.variant 0 (.var 0)],[width]⟩
abbrev right : Clause := ⟨1,0,[.variant 0 (.var 0)],[exact]⟩
abbrev original : Declaration := ⟨238,0,[.app 0 [.var 0,.var 0]],[left,right],
  [⟨0,0,GeneralDictionaryOptionalExpression229.pattern⟩],[]⟩
abbrev sourceRegistry : Registry := ⟨constructors,roles,[original]⟩
abbrev registry := GeneralNominalCenteredHeadAllocEncoding.registry sourceRegistry
abbrev d := GeneralNominalCenteredHeadAllocEncoding.declaration original
abbrev before := GeneralNominalVersionedJournal232.initial context root

theorem declaration_checked : DeclarationChecked constructors roles original := by
  constructor
  · simp [Declaration.Signature,Clause.Signature,Declared]
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,
      GeneralDictionaryOptionalExpression229.pattern,variablesArgs,Pattern.variables,merge,hide,variantRow]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors,GeneralDictionaryOptionalExpression229.pattern]
  · intro clause member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl <;> exact ⟨rfl,rfl⟩
  · intro clause member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl <;> exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro clause member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl <;> (unfold ConservativeSmaller; decide +kernel)
  · intro clause member capture; simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl
    all_goals
      constructor
      · simp [counted,substArgs,Pattern.subst,normalizeArgs,normalize,encodeArgs,Pattern.encode,Roles.argsSize,Roles.Term.size]
        exact Roles.Term.size_pos _
      · intro name
        simp [counted,substArgs,Pattern.subst,normalizeArgs,normalize,encodeArgs,Pattern.encode,Roles.argsOccurrences,Roles.Term.occurrences]

theorem checked : Checked sourceRegistry :=
  ⟨by simp,by intro decl member; cases List.mem_singleton.mp member; exact declaration_checked⟩

theorem boundary_checked : (boundary roles).Checked sourceRegistry := ⟨rfl,checked⟩

theorem coverage : GeneralNominalCenteredHeadWFSource.Coverage sourceRegistry context.interpretation := by
  constructor
  · intro decl member
    cases List.mem_singleton.mp member
    simp [GeneralNominalCenteredHeadWFSource.DeclarationCovered,
      GeneralNominalCenteredHeadWFSource.PatternsCovered,GeneralNominalCenteredHeadWFSource.PatternCovered,
      GeneralNominalCenteredHeadWFSource.ConstructorUse,interpretation,constructors,GeneralDictionaryOptionalExpression229.pattern]
    exact ⟨⟨rfl,rfl⟩,rfl,rfl,rfl⟩
  · exact GeneralDictionaryCompoundSource238.coverage.2

theorem source : GeneralNominalSourceFormation.InitialSource registry context root := initial_source registry rfl rfl

theorem initial : (boundary roles).Initial sourceRegistry root before :=
  ⟨GeneralNominalCenteredHeadMatStepJournal.initial context root,
    ⟨context,labels,initial_source sourceRegistry rfl rfl,root_point,ground,coverage,rfl⟩,rfl⟩

theorem reachable : Reachable sourceRegistry root before := ⟨before,initial,.refl⟩

abbrev packet : GeneralNominalSaturationState.Packet roles :=
  ⟨registry,context,GeneralNominalDemandMerging.pointSite root,d,GeneralNominalCenteredHeadAllocEncoding.declaration_checked declaration_checked,[(0,0)]⟩
abbrev plan : Plan roles := ⟨packet,rootSite snapshot.seed root,rfl⟩

theorem private_head : GeneralNominalVersionedPlans231.HeadModels packet GeneralDictionaryCompoundVersionedModel238.extended :=
  GeneralDictionaryCompoundVersionedPacket238.head_model

theorem fresh : GeneralNominalVersionedAllocation231.Fresh snapshot registry root.identity packet.bindings := by
  intro key _ collision
  have high := GeneralNominalIdentities.source_above_seed snapshot.seed key
  exact False.elim (Nat.not_lt_of_ge (source_bound _ collision) high)

theorem prepared : GeneralNominalVersionedCandidates231.Prepared registry context root d := by
  refine ⟨source.metadata,⟨source.linked.1,by intro output member; cases member⟩,
    [(0,0)],?_,fresh,?_,_,private_head⟩
  · decide +kernel
  · change GeneralNominalRecursiveInspection.Finished
      (GeneralNominalRecursiveCandidates.report context GeneralDictionaryCompoundSource238.declaration [(0,0)])
    rw [GeneralDictionaryCompoundPacket238.report_exact]
    exact ⟨rfl,rfl,rfl⟩

theorem frame : GeneralNominalVersionedEvidence231.Frame registry before.core root d.id plan :=
  ⟨rfl,rfl,rfl,rfl,List.mem_singleton_self _,List.mem_singleton_self _,List.mem_singleton_self _,rfl,
    by decide +kernel,prepared⟩

theorem survivor : GeneralNominalVersionedCandidates231.Survivor registry context root d.id
    (GeneralNominalVersionedFrame231.children packet) :=
  ⟨GeneralDictionaryCompoundPacket238.known,d,List.mem_singleton_self _,GeneralNominalCenteredHeadAllocEncoding.declaration_checked declaration_checked,
    rfl,rfl,[(0,0)],by decide +kernel,prepared,rfl⟩

theorem unique : GeneralNominalVersionedCandidates231.Unique registry context root d.id
    (GeneralNominalVersionedFrame231.children packet) := by
  refine ⟨survivor,?_⟩
  intro key kids found
  have copy := found
  obtain ⟨_,other,visible,_,eq,_⟩ := found
  cases List.mem_singleton.mp visible
  have same : key = d.id := eq.symm
  subst key
  exact ⟨rfl,GeneralNominalVersionedCandidates231.survivor_children_functional (GeneralNominalCenteredHeadAllocEncoding.registry_checked checked) copy survivor⟩

end Yulang.GeneralVersionedCollisionSource313
