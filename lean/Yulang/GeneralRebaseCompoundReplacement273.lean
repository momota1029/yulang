import Yulang.GeneralRebaseCompoundRowsMeaning273
import Yulang.GeneralDictionaryCompoundFeasible238

set_option maxRecDepth 30000
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseCompoundReplacement273
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryCompoundPoint238 (point allocated reserved ordinary)
open GeneralDictionaryCompoundSource238 (child declaration)
open GeneralDictionaryCompoundObstruction238 (oldPlan currentPlan)
open GeneralDictionaryCompoundPointModel238 (extended)
open GeneralDictionaryCompoundPacket238 (actual)
open GeneralDictionaryJournalRefinement228Source (roles root snapshot)
open GeneralNominalVersionedPlans231
open GeneralNominalVersionedPacketFrame236 (headSources head_models_iff)
open GeneralDictionaryCompoundPointHead238 (freshName Values)
open GeneralDictionaryCompoundSites238 (signature childSite)
open GeneralRebaseCompoundSourceTypes273 (Body)

abbrev lower := GeneralDictionaryCompoundModel238.names 0
abbrev upper := GeneralDictionaryCompoundModel238.names 1
abbrev center := GeneralDictionaryCompoundModel238.names 2
abbrev shape : Ty := variant 0 .emptyRecord

def patch (baseModel : Assignment) : Assignment :=
 fun n => (if n = lower then shape else (baseModel n).1,(baseModel n).2)

theorem untouched (baseModel : Assignment) (id : Nat) (outside : id ≠ lower) :
 patch baseModel id = baseModel id := by
 unfold patch
 simp [outside]

theorem public_patch (baseModel : Assignment) :
 GeneralRebaseCompoundRows273.Agrees (patch baseModel) baseModel := by
 refine ⟨?_,fun _ => rfl⟩
 intro i small
 apply untouched
 have high : 4 < lower := GeneralDictionaryCompoundPacket238.fresh_large 3
 omega

theorem changed (baseModel : Assignment) : (patch baseModel lower).1 = shape := by simp [patch]

theorem lower_not_head : lower ∉ headSources currentPlan.packet := by decide +kernel

theorem current_head : HeadModels currentPlan.packet (patch extended) :=
 (head_models_iff currentPlan.packet
  (fun id member => (untouched extended id (fun same => lower_not_head (same ▸ member))).symm)).mp
  GeneralDictionaryCompoundPrepared238.head_model

theorem lower_not_head_schema :
 lower ∉ GeneralNominalVersionedHeadFrame236.schemaSources currentPlan currentPlan.headSchema := by decide +kernel

theorem current_head_schema : SchemaHolds currentPlan currentPlan.headSchema (patch extended) :=
 (GeneralNominalVersionedHeadFrame236.schema_iff currentPlan currentPlan.headSchema
  (fun id member => (untouched extended id (fun same => lower_not_head_schema (same ▸ member))).symm)).mp
  (GeneralDictionaryCompoundReplay238.actual_head extended GeneralDictionaryCompoundPointModel238.model)

theorem values : Values (patch extended) := by
 have v := GeneralDictionaryCompoundPrepared238.values
 exact ⟨by rw [untouched _ _ (by decide +kernel)]; exact v.zero,
   by rw [untouched _ _ (by decide +kernel)]; exact v.two,
   by rw [untouched _ _ (by decide +kernel)]; exact v.actual,
   by rw [untouched _ _ (by decide +kernel)]; exact v.output,
   by rw [untouched _ _ (by decide +kernel)]; exact v.lower,
   by rw [untouched _ _ (by decide +kernel)]; exact v.upper⟩

theorem upper_value : (patch extended upper).1 = shape := by
 rw [untouched _ _ (by decide +kernel),
   GeneralDictionaryCompoundPointModel238.old_value upper (by simp [upper,GeneralDictionaryCompoundPointModel238.pool,GeneralDictionaryCompoundVersionedModel238.pool])]
 exact GeneralDictionaryCompoundVersionedPacket238.child_value 1

theorem center_value : (patch extended center).1 = shape := by
 rw [untouched _ _ (by decide +kernel),
   GeneralDictionaryCompoundPointModel238.old_value center (by simp [center,GeneralDictionaryCompoundPointModel238.pool,GeneralDictionaryCompoundVersionedModel238.pool])]
 exact GeneralDictionaryCompoundVersionedPacket238.child_value 2

theorem emitted_same : emittedSchema currentPlan = emittedSchema oldPlan := by
 unfold emittedSchema emittedRequests
 apply congrArg (GeneralNominalCenteredHeadMatSchemas.generated
   GeneralDictionaryCompoundSource238.registry.constructors GeneralDictionaryJournalRefinement228Source.interpretation)
 apply congrArg (fun right => GeneralNominalMaterialization.rootRequests declaration root ++ right)
 exact GeneralDictionaryCompoundVersionedPacket238.emitted_capture_independent _ _ _

theorem lower_mode :
 variables currentPlan (patch extended) .lower 0 = .emptyRecord := by
 rw [GeneralNominalVersionedExpressionFrame236.variable_value]
 change ((patch extended) ((GeneralNominalVersionedFrame231.capture currentPlan.packet).inputs 0).1).1 = _
 rw [GeneralDictionaryCompoundPointHead238.capture_exact]
 exact values.lower

theorem upper_mode :
 variables currentPlan (patch extended) .upper 0 = .emptyRecord := by
 rw [GeneralNominalVersionedExpressionFrame236.variable_value]
 change ((patch extended) ((GeneralNominalVersionedFrame231.capture currentPlan.packet).inputs 0).2).1 = _
 rw [GeneralDictionaryCompoundPointHead238.capture_exact]
 exact values.upper

theorem actual_mode :
 variables currentPlan (patch extended) .actual 0 = .emptyRecord := by
 rw [GeneralNominalVersionedExpressionFrame236.variable_value]
 change ((patch extended) (GeneralNominalVersionedFrame231.binder currentPlan 0)).1 = _
 rw [GeneralDictionaryCompoundReplay238.binder_exact]
 exact values.actual

theorem outputs : Outputs currentPlan (patch extended) := by
 unfold Outputs
 rw [emitted_same,GeneralDictionaryCompoundVersionedPacket238.emitted_schema,GeneralDictionaryCompoundTotal238.emitted_schema]
 intro e member
 rcases List.mem_cons.mp member with rfl | next
 · change Equivalent (patch extended 4).1 GeneralDictionaryOptionalOutput229.value
   rw [values.output]; exact ⟨subtype_refl _,subtype_refl _⟩
 · rcases List.mem_cons.mp next with rfl | last
   · change Equivalent (patch extended lower).1 (variant 0 (variables currentPlan (patch extended) .lower 0))
     rw [changed,lower_mode]; exact ⟨subtype_refl _,subtype_refl _⟩
   · cases List.mem_singleton.mp last
     change Equivalent (patch extended upper).1 (variant 0 (variables currentPlan (patch extended) .upper 0))
     rw [upper_value,upper_mode]; exact ⟨subtype_refl _,subtype_refl _⟩

theorem current_child (valid : child.Signature roles) :
 (GeneralNominalVersionedFrame231.childSite currentPlan child valid).Holds (patch extended) ∧
 (childSchema currentPlan child valid).Holds (variables currentPlan (patch extended)) (patch extended) := by
 constructor
 · intro index
   have zero : index = 0 := Fin.ext (by have h := index.isLt; change index.val < 1 at h; exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ h))
   subst index
   change Subtype (patch extended lower).1 (patch extended center).1 ∧
     Subtype (patch extended center).1 (patch extended upper).1
   rw [changed,upper_value,center_value]
   exact ⟨subtype_refl _,subtype_refl _⟩
 · rw [GeneralDictionaryCompoundReplay238.child_schema,childSchema_eq,
     GeneralDictionaryCompoundTotal238.child_schema]
   intro item member
   cases List.mem_singleton.mp member
   change Equivalent (patch extended center).1 (variant 0 (variables currentPlan (patch extended) .actual 0))
   rw [center_value,actual_mode]
   exact ⟨subtype_refl _,subtype_refl _⟩

theorem current_capture (name : Nat)
 (needed : name ∈ declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed currentPlan.packet name) :
 GeneralNominalCaptureMerges.Fits (patch extended)
   ((GeneralNominalVersionedFrame231.capture currentPlan.packet).inputs name)
   (patch extended (GeneralNominalVersionedFrame231.binder currentPlan name)).1 := by
 have isZero : name = 0 := by
   rcases needed with named | needed
   · simpa [GeneralDeclarations.Declaration.inputNames,GeneralDeclarationPatterns.variablesArgs,
       GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
       GeneralDeclarationPatterns.Pattern.variables] using named
   · obtain ⟨clause,member,needed⟩ := needed
     cases List.mem_singleton.mp member
     simpa [GeneralDeclarationPatterns.variablesArgs,GeneralDeclarationPatterns.Pattern.variables,
       GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize] using needed
 subst name
 rw [GeneralDictionaryCompoundPointHead238.capture_exact,GeneralDictionaryCompoundReplay238.binder_exact]
 unfold GeneralNominalCaptureMerges.Fits
 rw [values.lower,values.upper,values.actual]
 exact ⟨subtype_refl _,subtype_refl _⟩

theorem holds : Holds currentPlan (patch extended) := by
 rw [GeneralNominalVersionedPacketFrame236.holds_shape]
 refine ⟨current_head,GeneralNominalCenters.point_root_holds _ _
   GeneralDictionaryJournalRefinement228Source.root_point _,current_capture,current_head_schema,?_,?_,outputs⟩
 · intro e present _
   exact outputs e present
 · intro clause member signature
   cases List.mem_singleton.mp member
   exact current_child signature

theorem class_holds : GeneralNominalVersionedEffects231.ClassEffects point.core root currentPlan (patch extended) := by
 constructor
 · intro output member body found
   cases GeneralDictionaryCompoundFeasible238.request_exact root output member
   have explicit : body = .explicit ⟨0,0,GeneralDictionaryOptionalExpression229.pattern⟩ := Option.some.inj found |>.symm
   subst body
   intro e present
   cases List.mem_singleton.mp present
   change Equivalent (patch extended 4).1 GeneralDictionaryOptionalOutput229.value
   rw [values.output]
   exact ⟨subtype_refl _,subtype_refl _⟩
 · intro first one last two _
   cases GeneralDictionaryCompoundFeasible238.request_exact root first one
   cases GeneralDictionaryCompoundFeasible238.request_exact root last two
   exact ⟨subtype_refl _,subtype_refl _⟩

theorem original_point_does_not_hold :
 ¬ GeneralNominalVersionedJournal232.Models point (patch extended) :=
 fun model => GeneralDictionaryCompoundObstruction238.no_current_packet (patch extended) model holds

/-- At the same literal original source types and all rows, the old terminal
view and the replacement packet have full witnesses, but cannot be combined.
The latter checks every current packet field and live output. -/
theorem one_coordinate_replacement :
 GeneralNominalVersionedJournal232.Models point extended ∧
 GeneralRebaseCompoundRows273.Agrees (patch extended) extended ∧
 Holds currentPlan (patch extended) ∧
 GeneralNominalVersionedEffects231.ClassEffects point.core root currentPlan (patch extended) ∧
 ¬ GeneralNominalVersionedJournal232.Models point (patch extended) :=
 ⟨GeneralDictionaryCompoundPointModel238.model,public_patch extended,holds,class_holds,original_point_does_not_hold⟩

end Yulang.GeneralRebaseCompoundReplacement273
