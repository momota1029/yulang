import Yulang.GeneralDictionaryNonpointStrictOutput
import Yulang.GeneralDictionaryNestedBranchTransport

/-! An actual certified improving revision for the strict nonpoint fixture.
The initial source explicitly contains equality of the two outer argument
sources. Certification derives its semantic content from these ordinary atoms;
it is not assumed from one positive model. -/
set_option linter.unusedSimpArgs false
namespace Yulang.GeneralDictionaryNonpointCertified
open GeneralDictionaryNonpointStrict
open GeneralNominalReobservationSteps GeneralNominalSaturationState
open GeneralNominalRecursiveInspection GeneralDictionarySemanticCollapse
open GeneralNominalRecursiveCandidates CommonNominalFullCarrier
abbrev lowerUpper : PresenceNormalForm.Atom Nat := .tyLe (.var 1) (.var 2)
abbrev upperLower : PresenceNormalForm.Atom Nat := .tyLe (.var 2) (.var 1)
abbrev source : GeneralNominalState.State :=
 {GeneralDictionaryNonpointStrict.source with ordinary := [lowerUpper,upperLower]}
abbrev context : Context := ⟨source,interpretation⟩
abbrev tracked := GeneralNominalSupport.initial context root
abbrev start : State roles := ⟨context,[],[GeneralNominalDemandMerging.pointSite root],[],[]⟩
noncomputable def revision : Revision start where
 entries := GeneralDictionaryNonpointStrict.revision.entries
 catalogue := GeneralDictionaryNonpointStrict.revision.catalogue
 opaqueHeads := GeneralDictionaryNonpointStrict.revision.opaqueHeads
 domain := GeneralDictionaryNonpointStrict.revision.domain
noncomputable def shape : Shape revision where
 root := 0
 lower := 1
 upper := 2
 distinct := by decide +kernel
 oldOuter := outer
 newOuter := point
 left := inner
 right := right
 oldRoot := rfl
 newRoot := by rfl
 oldLower := rfl
 newLower := by rfl
 oldUpper := rfl
 sameOuter := rfl
 sameInner := rfl
 first := (3,4)
 last := (4,4)
 oldArgs := rfl
 newArgs := rfl
 leftArgs := rfl
 rightArgs := rfl
 binder := 7

private theorem source_equivalent (m : GeneralNominalCommonBridge.Assignment)
 (valid : GeneralNominalState.Models source m) : Equivalent (m 1).1 (m 2).1 :=
 ⟨valid.2.2 lowerUpper (by simp [source,GeneralNominalState.extend]),
  valid.2.2 upperLower (by simp [source,GeneralNominalState.extend])⟩
private theorem current_equivalent (m : GeneralNominalCommonBridge.Assignment)
 (valid : GeneralNominalState.Models revision.snapshot m) : Equivalent (m 1).1 (m 2).1 :=
 ⟨valid.2.2 lowerUpper (by simp [Revision.snapshot,source,GeneralNominalState.extend]),
  valid.2.2 upperLower (by simp [Revision.snapshot,source,GeneralNominalState.extend])⟩
private theorem outer_iff (m : GeneralNominalCommonBridge.Assignment)
 (equal : Equivalent (m 1).1 (m 2).1) :
 GeneralNominalState.Denotes source.base m 0 point ↔
 GeneralNominalState.Denotes source.base m 0 outer := by
 constructor
 · rintro ⟨values,fits,denotes⟩
   change GeneralNominalState.FitsAll source.base m [.type (1,1)] values at fits
   cases fits with
   | cons head tail =>
     cases tail
     rename_i value
     cases value with
     | inr => cases head
     | inl value => exact ⟨[.inl value],.cons ⟨head.1,subtype_trans head.2 equal.1⟩ .nil,denotes⟩
 · rintro ⟨values,fits,denotes⟩
   change GeneralNominalState.FitsAll source.base m [.type (1,2)] values at fits
   cases fits with
   | cons head tail =>
     cases tail
     rename_i value
     cases value with
     | inr => cases head
     | inl value => exact ⟨[.inl value],.cons ⟨head.1,subtype_trans head.2 equal.2⟩ .nil,denotes⟩

theorem raw_models (m : GeneralNominalCommonBridge.Assignment) :
 GeneralNominalState.Models revision.snapshot m ↔ GeneralNominalState.Models source m := by
 constructor
 · intro valid
   have eq := current_equivalent m valid
   refine ⟨valid.1,?_,valid.2.2⟩
   intro slot descriptor found
   by_cases zero : slot = (0 : Fin 5)
   · subst slot
     have same : outer = descriptor := Option.some.inj found
     subst descriptor
     exact (outer_iff m eq).mp (valid.2.1 (0 : Fin 5) point (by rfl))
   · have ne : slot.val ≠ 0 := fun h => zero (Fin.ext h)
     apply valid.2.1 slot descriptor
     change (if slot.val = 0 then some point else GeneralDictionaryNonpointStrict.source.nominals slot) = some descriptor
     rw [ite_eq_right ne]
     exact found
 · intro valid
   have eq := source_equivalent m valid
   refine ⟨valid.1,?_,valid.2.2⟩
   intro slot descriptor found
   by_cases zero : slot = (0 : Fin 5)
   · subst slot
     have same : point = descriptor := Option.some.inj found
     subst descriptor
     exact (outer_iff m eq).mpr (valid.2.1 0 outer rfl)
   · apply valid.2.1 slot descriptor
     have ne : slot.val ≠ 0 := fun h => zero (Fin.ext h)
     change (if slot.val = 0 then some point else GeneralDictionaryNonpointStrict.source.nominals slot) = some descriptor at found
     rw [ite_eq_right ne] at found
     exact found

theorem certified : Certified revision where
 raw := fun m => (raw_models m).mp
 exact := by
   intro m
   change (_ ∧ _) ↔ (_ ∧ _)
   exact and_congr_left (fun _ => raw_models m)

theorem improves : Improves revision := by
 constructor
 · rintro slot ⟨descriptor,found,pointed⟩
   by_cases zero : slot = (0 : Fin 5)
   · subst slot
     exact ⟨point,by rfl,by intro p h; cases List.mem_singleton.mp h; rfl⟩
   · have ne : slot.val ≠ 0 := fun h => zero (Fin.ext h)
     refine ⟨descriptor,?_,pointed⟩
     change (if slot.val = 0 then some point else GeneralDictionaryNonpointStrict.source.nominals slot) = some descriptor
     rw [ite_eq_right ne]
     exact found
 · refine ⟨0,?_,point,by rfl,?_⟩
   · rintro ⟨descriptor,found,pointed⟩
     have same : outer = descriptor := Option.some.inj found
     subst descriptor
     exact (by decide +kernel : (1 : Fin 5) ≠ 2) (pointed (.type (1,2)) (by simp))
   · intro p h; cases List.mem_singleton.mp h; rfl

theorem source_models : GeneralNominalState.Models source model := by
 change GeneralNominalState.Models (GeneralNominalState.extend GeneralDictionaryNonpointStrict.source [] [lowerUpper,upperLower]) model
 apply (GeneralNominalState.extend_models ..).mpr
 refine ⟨GeneralDictionaryNonpointStrict.source_models,?_⟩
 intro atom member
 simp only [List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl
 all_goals exact subtype_refl _

theorem revised_models : GeneralNominalState.Models revision.snapshot model :=
 (raw_models model).mpr source_models

theorem initial_source : GeneralNominalSourceFormation.InitialSource registry context root := by
 refine ⟨rfl,⟨rfl,?_⟩,?_,?_,?_,rfl⟩
 · intro name primitive found; cases found
 · constructor
   · intro index
     change (0 : Nat) ∈ GeneralNominalState.sources source ∧ (0 : Nat) ∈ GeneralNominalState.sources source
     exact ⟨by decide +kernel,by decide +kernel⟩
   · intro output member; cases member
 · intro m valid index
   exact subtype_refl _
 · intro identity member
   have h := GeneralNominalAllocation.member_le_max _ _ member
   have eq : (GeneralNominalState.sources source).foldr max 0 = source.seed := by decide +kernel
   rw [eq] at h
   exact h

noncomputable abbrev after : GeneralNominalSupport.Tracked roles := {tracked with current := revision.result}

theorem actual_value_step : GeneralNominalValueSteps.Step registry root tracked after :=
 ⟨root,.root,.administrative root revision.result (.reobserve root revision certified improves)⟩

theorem formed : GeneralNominalValueSteps.SourceFormed registry root after :=
 .update (.initial context initial_source) actual_value_step

theorem reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root after :=
 ⟨tracked,⟨context,initial_source,rfl⟩,.tail .refl actual_value_step⟩

theorem result_models : Models after.current model :=
 (certified.exact model).mpr ((initial_models context root model).mpr source_models)

theorem positive_transition :
 B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root after ∧
 GeneralNominalValueSteps.SourceFormed registry root after ∧ Models after.current model ∧
 Improves revision ∧ shape.first.1 ≠ shape.first.2 :=
 ⟨reachable,formed,result_models,improves,by decide +kernel⟩

abbrev bounds : List (GeneralNominalInspection.Bounds source) := [(0,0)]

theorem queries : GeneralNominalInspection.queries source interpretation declaration = [query shape] :=
 GeneralDictionaryNonpointStrict.queries

theorem report_exact : report context declaration bounds =
 GeneralDictionarySemanticCollapseBranch.oldRootReport shape :=
 (GeneralDictionarySemanticCollapseBranch.reports shape declaration queries).1

theorem private_models : GeneralNominalState.Models
 (privateState registry context root declaration bounds) model := by
 unfold privateState
 apply (GeneralNominalState.extend_models ..).mpr
 constructor
 · rw [report_exact]
   apply (GeneralNominalAllocation.propagate_models ..).mpr
   have previous := (GeneralNominalAllocation.propagate_models ..).mp GeneralDictionaryNonpointStrict.old_propagation
   exact ⟨source_models,previous.2⟩
 · have old := (GeneralNominalState.extend_models ..).mp GeneralDictionaryNonpointStrict.private_models |>.2
   rw [report_exact]
   rw [GeneralDictionaryNonpointStrict.report_exact] at old
   exact old

theorem generated_empty : generated registry context root declaration checked bounds = {} := by
 unfold generated
 rw [GeneralDictionarySemanticCollapseBranch.terminal_requests _ _ _ _ _ _ rfl]
 rfl

theorem old_branch : BranchModels registry context root declaration checked bounds model := by
 refine ⟨private_models,?_,?_⟩
 · rw [report_exact]
   have h := GeneralDictionaryNonpointStrict.old_projection
   change ProjectionModels GeneralDictionaryNonpointStrict.start.context.state
     (inspect GeneralDictionaryNonpointStrict.start.context.state (query GeneralDictionaryNonpointStrict.shape)
       (GeneralDictionaryNonpointStrict.shape.root,GeneralDictionaryNonpointStrict.shape.root) none) model at h
   rw [before_exact] at h
   let r := GeneralNominalRefinements.extended GeneralDictionaryNonpointStrict.source [] [lowerUpper,upperLower]
   have transported := (GeneralDictionaryNestedBranchTransport.projection_map r _ model).mpr h
   change ProjectionModels source (beforeReport shape) model
   have reports : beforeReport shape =
       GeneralDictionaryNestedRefinement.mapReport r.base.embed
         (beforeReport GeneralDictionaryNonpointStrict.shape) := by
     rfl
   rw [reports]
   exact transported
 · rw [generated_empty]
   exact GeneralNominalMaterialization.empty_models _ _ _ _ _

theorem current_branch : BranchModels registry
 (GeneralDictionarySemanticCollapseBranch.currentContext revision) root declaration checked bounds model := by
 apply GeneralDictionaryNonpointBranch.branch shape registry root declaration checked queries rfl rfl
 · change ∀ entry ∈ (generated registry context root declaration checked bounds).variables, _
   rw [generated_empty]
   intro entry member; cases member
 · exact old_branch
 · exact revised_models

theorem reachable_branch_replay :
 GeneralNominalValueSteps.Step registry root tracked after ∧
 B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root after ∧
 BranchModels registry context root declaration checked bounds model ∧
 BranchModels registry (GeneralDictionarySemanticCollapseBranch.currentContext revision) root declaration checked bounds model ∧
 ¬ Equivalent (model loId).1 (model 3).1 :=
 ⟨actual_value_step,reachable,old_branch,current_branch,merged_lower_not_equivalent⟩
end Yulang.GeneralDictionaryNonpointCertified
