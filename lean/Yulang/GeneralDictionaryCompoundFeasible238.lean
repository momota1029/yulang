import Yulang.GeneralDictionaryCompoundPrepared238
import Yulang.GeneralNominalVersionedCurrentHead237
import Yulang.GeneralNominalVersionedMixedReady235
import Yulang.GeneralNominalVersionedDiagnosticLaws232
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryCompoundFeasible238
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryCompoundSource238 GeneralDictionaryCompoundPoint238
open GeneralDictionaryCompoundObstruction238 GeneralDictionaryCompoundSites238
open GeneralDictionaryCompoundPrepared238
open GeneralNominalCenters GeneralNominalVersionedCandidates231
open GeneralDictionaryCompoundPointModel238 (extended)
open CommonNominalFullCarrier

theorem known : ¬ GeneralNominalState.RootPending point.core.erased.current.context.state root.demand := by
  rw [context_exact]
  rintro ⟨index,unknown⟩
  exact unknown ⟨0,rfl,Or.inr ⟨descriptor (2,2),rfl⟩⟩

theorem survivor : Survivor registry point.core.erased.current.context root declaration.id
    (GeneralNominalVersionedFrame231.children currentPlan.packet) := by
  rw [context_exact]
  refine ⟨?_,declaration,List.mem_singleton_self _,declaration_checked,rfl,rfl,[(0,0)],rfl,?_,rfl⟩
  · have h := known; rw [context_exact] at h; exact h
  · have h := prepared; rw [context_exact] at h; exact h

theorem unique : Unique registry point.core.erased.current.context root declaration.id
    (GeneralNominalVersionedFrame231.children currentPlan.packet) := by
  refine ⟨survivor,?_⟩
  intro key kids found
  have copy := found
  obtain ⟨_,d,visible,_,identity,_⟩ := found
  cases List.mem_singleton.mp visible
  have same : key = declaration.id := identity.symm
  subst key
  exact ⟨rfl,survivor_children_functional checked copy survivor⟩

theorem ready : GeneralNominalCenteredHeadMatEffects.Ready point.core root currentPlan :=
  GeneralNominalVersionedMixedReady235.ready ⟨rfl,checked⟩ reachable frame

theorem head_equations : GeneralNominalVersionedDiagnostic232.HeadEquations currentPlan extended := by
  have valid := GeneralDictionaryCompoundPointModel238.model
  have head := GeneralDictionaryCompoundReplay238.actual_head extended valid
  refine ⟨valid.1.2.2.2.1 currentPlan.input frame.center_recorded,?_,head⟩
  intro name named
  exact GeneralNominalVersionedCurrentHead237.capture_fits currentPlan frame valid head_model head name (Or.inl named)

theorem request_exact (focus : GeneralSourceDictionaries.Occurrence roles)
    (output : GeneralSourceState.Output)
    (member : output ∈ GeneralNominalCenteredHeadOutputs.requests point.core focus) : output = ⟨0,4⟩ := by
  obtain ⟨site,present,_,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
  rw [raw_sites] at present
  rcases List.mem_cons.mp present with same | present
  · subst site; exact List.mem_singleton.mp within
  · cases List.mem_singleton.mp present
    cases within

theorem equal_outputs (focus : GeneralSourceDictionaries.Occurrence roles) :
    GeneralNominalCenteredHeadOutputs.EqualOutputs point.core focus extended := by
  intro first one last two _
  cases request_exact focus first one
  cases request_exact focus last two
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem class_effects : GeneralNominalVersionedEffects231.ClassEffects point.core root currentPlan extended := by
  apply (GeneralNominalVersionedEffects231.class_effects_iff ..).mpr
  refine ⟨?_,equal_outputs root⟩
  intro output member body found
  cases request_exact root output member
  have same : body = .explicit ⟨0,0,GeneralDictionaryOptionalExpression229.pattern⟩ := Option.some.inj found |>.symm
  subst body
  intro equation present
  cases List.mem_singleton.mp present
  change Equivalent (extended 4).1 GeneralDictionaryOptionalOutput229.value
  rw [values.output]
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem output_clear : ¬ GeneralNominalVersionedDiagnostic232.OutputConflict registry point root declaration.id := by
  intro conflict
  exact conflict.2 ⟨extended,GeneralDictionaryCompoundPointModel238.model,⟨⟨_,unique⟩,currentPlan,frame,ready,head_equations,class_effects⟩⟩

theorem sharing_clear : ¬ GeneralNominalVersionedDiagnostic232.SharingConflict registry point root := by
  rintro ⟨other,kids,chosen,_,bad⟩
  have same : other = declaration.id := (unique.2 other kids chosen.1).1
  subst other
  exact bad.2.2 ⟨extended,GeneralDictionaryCompoundPointModel238.model,currentPlan,frame,
    GeneralNominalVersionedHeadSharing232.schema_holds currentPlan extended
      (GeneralDictionaryCompoundReplay238.actual_head extended GeneralDictionaryCompoundPointModel238.model)⟩

theorem merged_clear : ¬ GeneralNominalVersionedMergedConflict232.MergedOutputConflict point root :=
  GeneralNominalVersionedMergedConflict232.models_exclude_conflict GeneralDictionaryCompoundPointModel238.model
    (fun focus _ => equal_outputs focus) (equal_outputs root)

end Yulang.GeneralDictionaryCompoundFeasible238
