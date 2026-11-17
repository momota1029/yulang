import Yulang.GeneralDictionaryMixedGround218RootFrame236
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
namespace Yulang.GeneralDictionaryMixedGround218RootSelected236
open GeneralDictionaryGroundCopy218Source
open GeneralDictionaryGroundCopy218Install (model parent_only)
open GeneralDictionaryMixedGround218FinalState235
open GeneralDictionaryMixedGround218FinalRegression235 (sites)
open GeneralDictionaryMixedGround218RootFrame236

theorem administrative_ready : GeneralNominalVersionedDiagnostic232.AdministrativeReady finalState root := by
 refine ⟨⟨_,by rw [sites.1]; exact List.mem_cons_self,rfl⟩,?_⟩
 intro first one _ last two same
 exact GeneralDictionaryMixedGround218PointStable235.merges_closed sites one two same

theorem safe : B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) registry finalState root := by
 have noRaw : ∀ slot, ¬ GeneralNominalCycleK2.RecursAt finalState.core.erased.current.context.state slot := by
   rw [final_context]
   exact GeneralDictionaryMixedGround218FinalRejection235.no_raw_recurs
 have acyclic := GeneralDictionaryMixedGround218FinalRejection235.acyclic
 refine ⟨known,?_,?_,?_⟩
 · rintro (old | (⟨index,cycle⟩ | ⟨site,present,same,index,cycle⟩))
   · obtain ⟨_,_,_,slot,_,cycle⟩ := old; exact noRaw slot cycle
   · exact acyclic _ cycle
   · exact acyclic _ cycle
 · rintro (old | ⟨candidate,framed,entry,member,cycle⟩)
   · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ := old; exact noRaw visited.1 cycle
   · exact acyclic _ cycle
 · rintro (⟨_,d,visible,role,_,unprepared⟩ | unclosed)
   · cases parent_only visible role
     apply unprepared
     rw [final_context]
     exact prepared
   · exact unclosed administrative_ready

theorem no_sharing_conflict : ¬ GeneralNominalVersionedDiagnostic232.SharingConflict registry finalState root := by
 rintro ⟨key,children,other,_,_,_,absent⟩
 have keyEq := (unique.2 key children other.1).1
 subst key
 exact absent ⟨model,final_model,plan,frame,GeneralNominalVersionedHeadSharing232.packet_holds plan model held⟩

theorem no_output_conflict : ¬ GeneralNominalVersionedDiagnostic232.OutputConflict registry finalState root 0 := by
 rintro ⟨_,absent⟩
 apply absent
 refine ⟨model,final_model,⟨_,unique⟩,plan,frame,?_,GeneralNominalVersionedDiagnostic232.head_equations held,?_⟩
 · exact GeneralNominalVersionedMixedReady235.ready ⟨rfl,source_checked⟩ reachable frame
 · exact GeneralDictionaryMixedGround218RootCommitted235.classes sites plan model

theorem no_merged_conflict : ¬ GeneralNominalVersionedMergedConflict232.MergedOutputConflict finalState root :=
 GeneralNominalVersionedMergedConflict232.models_exclude_conflict final_model
   (fun focus _ => GeneralDictionaryMixedGround218FinalPending235.equal_outputs focus)
   (GeneralDictionaryMixedGround218FinalPending235.equal_outputs root)

theorem selected : GeneralNominalVersionedMixedSourceBoundary234.Local sourceRegistry finalState root
 (.selected 0 [GeneralDictionaryGroundCopy218Reinstall.newChild.occurrence]) := by
 have chosen : GeneralNominalVersionedMixedSourceBoundary234.Local sourceRegistry finalState root
     (.selected 0 (GeneralNominalVersionedFrame231.children packet)) :=
   .ordinary no_sharing_conflict (.ordinary no_merged_conflict (.selected safe unique no_output_conflict))
 rw [children_eq] at chosen
 exact chosen
end Yulang.GeneralDictionaryMixedGround218RootSelected236
