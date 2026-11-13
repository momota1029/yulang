import Yulang.GeneralDictionaryNonpointBranch
import Yulang.GeneralDictionarySemanticCollapseBranchExample

/-! Positive nonpoint-leaf replay: both retained endpoints differ in source ID
and semantic value (bottom/int). This witnesses old/new private BranchModels,
not certification or operational reachability of this new descriptor revision. -/
set_option linter.unusedSimpArgs false
namespace Yulang.GeneralDictionaryNonpointExample
open GeneralDictionarySemanticCollapse GeneralNominalReobservationSteps
open GeneralNominalSaturationState GeneralNominalRecursiveInspection
open GeneralNominalAllocation GeneralNominalRecursiveCandidates
open GeneralDeclarations GeneralDeclarationPatterns
open CommonNominalFullCarrier
abbrev base : GeneralSourceState.State where
 slots := 5
 source := Fin.val
 source_injective := fun _ _ h => Fin.ext h
 rowSource := Fin.val
 ordinary := []
 kinds := 0
 shapes := Fin.elim0
 shapes_injective := by intro i; exact Fin.elim0 i
 heads := fun _ => .unresolved
 intervals := []
 heads_sound := by intro _ _ _ _ impossible; cases impossible
 intervals_sound := by intro _ _ _ impossible; cases impossible
abbrev view : GeneralNormalizedObservation.Snapshot base where
 kinds := 0
 shapes := Fin.elim0
 shapes_injective := by intro i; exact Fin.elim0 i
 canonical := by intro i; exact Fin.elim0 i
 heads := fun _ => .deferred .unresolved
 checked := by intro _ _ impossible; cases impossible
abbrev outer : GeneralNominalState.Descriptor 5 := ⟨0,⟨[.type],0⟩,[.type (1,2)],rfl⟩
abbrev point : GeneralNominalState.Descriptor 5 := ⟨0,⟨[.type],0⟩,[.type (1,1)],rfl⟩
abbrev inner : GeneralNominalState.Descriptor 5 := ⟨0,⟨[.type],0⟩,[.type (3,4)],rfl⟩
abbrev source : GeneralNominalState.State where
 base := base
 view := view
 constructors := GeneralDeclarationExamples.constructors
 nominals := fun slot => if slot = (0 : Fin 5) then some outer else if slot = 1 ∨ slot = 2 then some inner else none
 catalogue := by
   intro slot descriptor found
   split at found
   · cases Option.some.inj found; rfl
   · split at found
     · cases Option.some.inj found; rfl
     · cases found
 bodies_opaque := by intro _ _ _; rfl
 seed := 4
abbrev interpretation := GeneralDictionarySemanticCollapseExample.interpretation
abbrev roles := GeneralDeclarationExamples.roles
abbrev root : GeneralSourceDictionaries.Occurrence roles := GeneralDictionarySemanticCollapseExample.root
abbrev start : State roles := ⟨⟨source,interpretation⟩,[],[GeneralNominalDemandMerging.pointSite root],[],[]⟩
noncomputable def revision : Revision start where
 entries := fun slot => if slot.val = 0 then some point else source.nominals slot
 catalogue := by
   intro slot descriptor found
   split at found
   · cases Option.some.inj found; rfl
   · exact source.catalogue slot descriptor found
 opaqueHeads := by intro _ _ _; rfl
 domain := by
   intro slot
   by_cases zero : slot = (0 : Fin 5)
   · subst slot; simp [source]
   · have ne : slot.val ≠ 0 := fun h => zero (Fin.ext h)
     simp [ne,zero]
noncomputable def shape : Shape revision where
 root := 0
 lower := 1
 upper := 2
 distinct := by decide +kernel
 oldOuter := outer
 newOuter := point
 left := inner
 right := inner
 oldRoot := rfl
 newRoot := by rfl
 oldLower := rfl
 newLower := by rfl
 oldUpper := rfl
 sameOuter := rfl
 sameInner := rfl
 first := (3,4)
 last := (3,4)
 oldArgs := rfl
 newArgs := rfl
 leftArgs := rfl
 rightArgs := rfl
 binder := 7
abbrev declaration : Declaration := GeneralDictionarySemanticCollapseBranchExample.declaration
abbrev registry : Registry := ⟨source.constructors,roles,[declaration]⟩
abbrev context := start.context
abbrev bounds : List (GeneralNominalInspection.Bounds source) := [(0,0)]
abbrev loKey := origin root.identity declaration.id 0 7 0
abbrev hiKey := origin root.identity declaration.id 1 7 0
abbrev loId := GeneralNominalAllocation.source source registry root.identity loKey
abbrev hiId := GeneralNominalAllocation.source source registry root.identity hiKey
abbrev leafValue : Ty := .base .int
abbrev innerValue : Ty := nominal 0 [.inl leafValue]
abbrev model : GeneralNominalCommonBridge.Assignment := fun identity =>
 (if identity = 0 then nominal 0 [.inl innerValue]
  else if identity = 1 ∨ identity = 2 then innerValue
  else if identity = 3 ∨ identity = loId then .bottom else leafValue,Common.rowEmpty)
private theorem lo_above : 4 < loId := GeneralNominalIdentities.source_above_seed _ _
private theorem hi_above : 4 < hiId := GeneralNominalIdentities.source_above_seed _ _
private theorem hi_ne_lo : hiId ≠ loId := by
 intro h
 have eq := (GeneralNominalIdentities.source_identity source.seed hiKey loKey).mp h
 have : (1 : Nat) = 0 := congrArg (fun p => p.2.2.1) eq
 cases this
theorem at_lower : (model 3).1 = .bottom := rfl
theorem at_upper : (model 4).1 = leafValue := by
 have ne : 4 ≠ loId := by have := lo_above; omega
 simp [model,ne]
 rfl
theorem at_merge_lower : (model loId).1 = .bottom := by
 have h := lo_above
 simp [model,show loId ≠ 0 by omega,show loId ≠ 1 by omega,show loId ≠ 2 by omega]
 rfl
theorem at_merge_upper : (model hiId).1 = leafValue := by
 have h := hi_above
 simp [model,hi_ne_lo,show hiId ≠ 0 by omega,show hiId ≠ 1 by omega,
   show hiId ≠ 2 by omega,show hiId ≠ 3 by omega]
 rfl
theorem bottom_leaf : Subtype .bottom leafValue :=
 (CommonNominalFullModelMap.subtype_exact .bottom (.base .int)).mpr (CommonBoundCoalescing.bottom_le _)

theorem source_models : GeneralNominalState.Models source model := by
 refine ⟨⟨PresenceNormalForm.all_nil _ _,?_,?_⟩,?_,PresenceNormalForm.all_nil _ _⟩
 · intro _ _ impossible; cases impossible
 · intro _ impossible; cases impossible
 · intro slot descriptor found
   change (if slot = (0 : Fin 5) then some outer else if slot = 1 ∨ slot = 2 then some inner else none) = some descriptor at found
   split at found
   · rename_i zero
     subst slot
     cases Option.some.inj found
     exact ⟨[.inl innerValue],.cons ⟨subtype_refl _,subtype_refl _⟩ .nil,
       subtype_refl _,subtype_refl _⟩
   · split at found
     · rename_i _ oneOrTwo
       cases Option.some.inj found
       rcases oneOrTwo with rfl | rfl
       all_goals
         refine ⟨[.inl leafValue],.cons ?_ .nil,subtype_refl _,subtype_refl _⟩
         change Subtype (model 3).1 leafValue ∧ Subtype leafValue (model 4).1
         rw [at_lower,at_upper]
         exact ⟨bottom_leaf,subtype_refl _⟩
     · cases found

theorem revised_models : GeneralNominalState.Models revision.snapshot model := by
 refine ⟨source_models.1,?_,source_models.2.2⟩
 intro slot descriptor found
 by_cases zero : slot = (0 : Fin 5)
 · subst slot
   have same : point = descriptor := Option.some.inj found
   subst descriptor
   exact ⟨[.inl innerValue],.cons ⟨subtype_refl _,subtype_refl _⟩ .nil,
     subtype_refl _,subtype_refl _⟩
 · apply source_models.2.1 slot descriptor
   have ne : slot.val ≠ 0 := fun h => zero (Fin.ext h)
   change (if slot.val = 0 then some point else source.nominals slot) = some descriptor at found
   rw [ite_eq_right ne] at found
   exact found

theorem observed_parent : Observes model (parent shape) innerValue :=
 .nominal (.source 0) ⟨subtype_refl _,subtype_refl _⟩ rfl
theorem observed_leaf : Observes model (leaf shape) leafValue :=
 .nominal observed_parent ⟨subtype_refl _,subtype_refl _⟩ rfl
private theorem parent_unique (actual : Ty) (seen : Observes model (parent shape) actual) :
 Equivalent actual innerValue :=
 nominal_observation_unique model (.argument (.source 0) 0 0) actual innerValue seen observed_parent
theorem leaf_unique (actual : Ty) (seen : Observes model (leaf shape) actual) :
 Equivalent actual leafValue :=
 nominal_observation_unique model (.argument (.argument (.source 0) 0 0) 0 0)
   actual leafValue seen observed_leaf
theorem leaf_fit (actual : Ty) (seen : Observes model (leaf shape) actual) :
 Fits source model ((3 : Fin 5),4) actual := by
 change Subtype (model 3).1 actual ∧ Subtype actual (model 4).1
 rw [at_lower,at_upper]
 exact ⟨subtype_trans bottom_leaf (leaf_unique actual seen).2,(leaf_unique actual seen).1⟩

theorem old_projection : ProjectionModels source
 (inspect source (query shape) (0,0) none) model := by
 change ProjectionModels start.context.state
   (inspect start.context.state (query shape) (shape.root,shape.root) none) model
 rw [before_exact shape]
 refine ⟨?_,?_,?_,?_⟩
 · intro anchor member
   simp only [beforeReport,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl
   · refine ⟨⟨innerValue,observed_parent⟩,?_⟩
     intro a seen
     exact ⟨(parent_unique a seen).2,(parent_unique a seen).1⟩
   · exact ⟨⟨leafValue,observed_leaf⟩,leaf_fit⟩
   · exact ⟨⟨leafValue,observed_leaf⟩,leaf_fit⟩
 · intro test member actual seen
   cases List.mem_singleton.mp member
   exact ⟨[.inl leafValue],rfl,parent_unique actual seen⟩
 · intro first hf last hl _ ref found actual seen
   simp only [beforeReport,List.mem_cons,List.not_mem_nil,or_false] at hf hl
   rcases hf with rfl | rfl <;> rcases hl with rfl | rfl
   all_goals cases Option.some.inj found
   all_goals exact leaf_fit actual seen
 · intro first hf last hl _ a b ha hb x y hx hy
   simp only [beforeReport,List.mem_cons,List.not_mem_nil,or_false] at hf hl
   rcases hf with rfl | rfl <;> rcases hl with rfl | rfl
   all_goals cases Option.some.inj ha; cases Option.some.inj hb
   all_goals exact ⟨subtype_trans (leaf_unique x hx).1 (leaf_unique y hy).2,
     subtype_trans (leaf_unique y hy).1 (leaf_unique x hx).2⟩

theorem checked : DeclarationChecked registry.constructors roles declaration :=
 GeneralDictionarySemanticCollapseBranchExample.checked

theorem queries : GeneralNominalInspection.queries source interpretation declaration = [query shape] := by
 simp [GeneralNominalInspection.queries,declaration,GeneralDictionarySemanticCollapseBranchExample.declaration,
   Declaration.normalHead,normalizeArgs,normalize,GeneralNominalInspection.translate,interpretation,
   GeneralDictionarySemanticCollapseExample.interpretation,source,GeneralDeclarationExamples.constructors,query,shape]

theorem old_propagation : GeneralNominalState.Models
 (propagate source registry root.identity declaration [(7,3,4),(7,3,4)]) model := by
 apply (propagate_models ..).mpr
 refine ⟨source_models,?_,?_⟩
 · intro first hf last hl same
   simp at hf hl
   subst first; subst last
   change Subtype (model 3).1 (model 4).1
   rw [at_lower,at_upper]; exact bottom_leaf
 · simp only [merges,show declaration.inputNames = [7] from rfl,List.flatMap_cons,List.flatMap_nil,List.append_nil]
   simp only [occurrences,List.filter_cons,beq_self_eq_true,List.filter_nil,List.map_cons,List.map_nil,ite_true]
   rw [PresenceNormalForm.all_append]
   constructor
   · apply (GeneralNominalCaptureMerges.equations_exact ..).mpr
     change Equivalent (model loId).1 (.union (model 3).1 (model 3).1)
     rw [at_merge_lower,at_lower]
     exact ⟨(common_union_is_join _ _ _).mp (subtype_refl _) |>.1,
       (common_union_is_join _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩⟩
   · apply (GeneralNominalCaptureMerges.equations_exact ..).mpr
     change Equivalent (model hiId).1 (.inter (model 4).1 (model 4).1)
     rw [at_merge_upper,at_upper]
     exact ⟨(common_inter_is_meet _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩,
       (common_inter_is_meet _ _ _).mp (subtype_refl _) |>.1⟩

theorem report_exact : report context declaration bounds =
 GeneralDictionarySemanticCollapseBranch.oldRootReport shape := by
 exact (GeneralDictionarySemanticCollapseBranch.reports shape declaration queries).1

theorem private_models : GeneralNominalState.Models
 (privateState registry context root declaration bounds) model := by
 unfold privateState
 apply (GeneralNominalState.extend_models ..).mpr
 constructor
 · rw [report_exact]
   exact old_propagation
 · unfold selfChecks
   rw [report_exact]
   change PresenceNormalForm.All CommonNominalFullCarrier.model model
    ([(0,0),(0,0),(1,2),(3,4),(3,4)].map fun pair =>
      PresenceNormalForm.Atom.tyLe (.var pair.1) (.var pair.2))
   intro atom member
   simp only [List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl | rfl | rfl
   · exact subtype_refl _
   · exact subtype_refl _
   · exact subtype_refl _
   all_goals change Subtype (model 3).1 (model 4).1; rw [at_lower,at_upper]; exact bottom_leaf

theorem generated_empty : generated registry context root declaration checked bounds = {} := by
 unfold generated
 rw [GeneralDictionarySemanticCollapseBranch.terminal_requests _ _ _ _ _ _ rfl]
 rfl

theorem old_branch : BranchModels registry context root declaration checked bounds model := by
 refine ⟨private_models,?_,?_⟩
 · rw [report_exact]
   have h := old_projection
   change ProjectionModels start.context.state (inspect start.context.state (query shape) (shape.root,shape.root) none) model at h
   rw [before_exact] at h
   exact h
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

theorem nonpoint_leaf : shape.first.1 ≠ shape.first.2 ∧ (model 3).1 ≠ (model 4).1 := by
 refine ⟨by decide +kernel,?_⟩
 rw [at_lower,at_upper]
 intro h; cases h

theorem positive_replay :
 BranchModels registry context root declaration checked bounds model ∧
 BranchModels registry (GeneralDictionarySemanticCollapseBranch.currentContext revision) root declaration checked bounds model ∧
 shape.first.1 ≠ shape.first.2 ∧ (model 3).1 ≠ (model 4).1 :=
 ⟨old_branch,current_branch,nonpoint_leaf⟩
end Yulang.GeneralDictionaryNonpointExample
