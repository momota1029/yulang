import Yulang.GeneralWherePhysicalOldHead319

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 22000000
namespace Yulang.GeneralWherePhysicalOldPick319
open GeneralWhereOriginSingleSource318
open GeneralWherePhysicalOldHead319 (start frame unique prepared schema_holds all_captures before_models)
open GeneralDictionaryJournalRefinement228Source (roles root snapshot root_point)
open GeneralLiveCompoundLeafProof316 (w)
open GeneralNominalVersionedDiagnostic232 (AdministrativeReady HeadEquations boundary)
open GeneralNominalCenteredHeadOutputs (requests EqualOutputs)
open GeneralNominalVersionedEffects231 (ClassEffects)
open GeneralNominalCenters
open CommonNominalFullCarrier

theorem all_requests (focus : GeneralSourceDictionaries.Occurrence roles) :
    ∀ out ∈ requests start.core focus, out = ⟨0,4⟩ := by
  intro out seen
  obtain ⟨s,member,_,asked⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp seen
  cases List.mem_singleton.mp member
  exact List.mem_singleton.mp asked

theorem equal_outputs (focus : GeneralSourceDictionaries.Occurrence roles) :
    EqualOutputs start.core focus w := by
  intro a h b i _
  cases all_requests focus a h
  cases all_requests focus b i
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem ready : GeneralNominalCenteredHeadMatEffects.Ready start.core root oldPlan := by
  intro out used
  cases all_requests root out used
  exact ⟨.explicit ⟨0,0,GeneralDictionaryOptionalExpression229.pattern⟩,rfl,rfl⟩

theorem actual_output : Equivalent (w 4).1 GeneralDictionaryOptionalOutput229.value :=
  GeneralWhereVersionWitness317.actual_row w GeneralLiveCompoundLeafInstall316.after_model

theorem class_effects : ClassEffects start.core root oldPlan w := by
  apply (GeneralNominalVersionedEffects231.class_effects_iff ..).mpr
  refine ⟨?_,equal_outputs root⟩
  intro out used body resolved
  cases all_requests root out used
  have bodyEq : body = .explicit ⟨0,0,GeneralDictionaryOptionalExpression229.pattern⟩ := Option.some.inj resolved |>.symm
  subst body
  intro row member
  cases List.mem_singleton.mp member
  exact actual_output

theorem administrative : AdministrativeReady start root := by
  refine ⟨⟨_,List.mem_singleton_self _,rfl⟩,?_⟩
  intro first one _ last two _
  cases List.mem_singleton.mp one
  cases List.mem_singleton.mp two
  exact .refl _

theorem safe : B4TargetV8.SafeKnown (boundary roles) registry start root := by
  refine ⟨GeneralDictionaryCompoundPacket238.known,?_,?_,?_⟩
  · rintro (raw | (⟨i,cycle⟩ | ⟨site,_,_,idx,cycle⟩))
    · obtain ⟨_,_,_,slot,_,cycle⟩ := raw
      exact GeneralDictionaryOptionalEnable229.no_raw_recurs slot cycle
    · exact GeneralLiveCompoundInstall316.acyclic _ cycle
    · exact GeneralLiveCompoundInstall316.acyclic _ cycle
  · rintro (raw | ⟨p,framed,entry,_,cycle⟩)
    · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ := raw
      exact GeneralDictionaryOptionalEnable229.no_raw_recurs visited.1 cycle
    · exact GeneralLiveCompoundInstall316.acyclic _ cycle
  · rintro (⟨_,d,visible,role,_,unprepared⟩ | unready)
    · rcases List.mem_cons.mp visible with eq|rest
      · subst d; exact unprepared prepared
      · cases List.mem_singleton.mp rest
        cases role
    · exact unready administrative

theorem equations : HeadEquations oldPlan w :=
  ⟨point_root_holds _ _ root_point _,fun n present => all_captures n (.inl present),schema_holds⟩

theorem selected : GeneralNominalVersionedMixedSourceBoundary234.Local sourceRegistry start root
    (.selected declaration.id (GeneralNominalVersionedFrame231.children older)) := by
  apply GeneralNominalVersionedMixedSourceBoundary234.local_iff.mpr
  apply GeneralNominalVersionedMixedBoundary234.local_iff.mpr
  refine .ordinary ?_ (.ordinary ?_ (.selected safe unique ?_))
  · rintro ⟨key,kids,picked,_,blocked⟩
    have same := (unique.2 key kids picked.1).1
    subst key
    exact blocked.2.2 ⟨w,before_models.1,oldPlan,frame,GeneralNominalVersionedHeadSharing232.schema_holds oldPlan w schema_holds⟩
  · exact GeneralNominalVersionedMergedConflict232.models_exclude_conflict before_models.1
      (fun focus _ => equal_outputs focus) (equal_outputs root)
  · intro clash
    exact clash.2 ⟨w,before_models.1,⟨⟨_,unique⟩,oldPlan,frame,ready,equations,class_effects⟩⟩

end Yulang.GeneralWherePhysicalOldPick319
