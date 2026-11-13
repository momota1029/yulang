import Yulang.GeneralDictionarySemanticCollapse
import Yulang.GeneralNominalIntervalExamples
import Yulang.GeneralNominalValueSteps

/-! A positive certified improving revision drops a duplicate nested capture.
Both inner endpoints have the same nominal descriptor, so all source models
already identify them semantically although their source IDs differ. -/
namespace Yulang.GeneralDictionarySemanticCollapseExample
open GeneralDictionarySemanticCollapse GeneralNominalReobservationSteps
open GeneralNominalSaturationState GeneralNominalRecursiveInspection
open GeneralDeclarationExamples (roles constructors)
open CommonNominalFullCarrier

abbrev outer : GeneralNominalState.Descriptor 4 := ⟨0,⟨[.type],0⟩,[.type (1,2)],rfl⟩
abbrev point : GeneralNominalState.Descriptor 4 := ⟨0,⟨[.type],0⟩,[.type (1,1)],rfl⟩
abbrev inner : GeneralNominalState.Descriptor 4 := ⟨0,⟨[.type],0⟩,[.type (3,3)],rfl⟩
abbrev source : GeneralNominalState.State where
 base := GeneralNominalIntervalExamples.base
 view := GeneralNominalIntervalExamples.view
 constructors := constructors
 nominals := fun slot => if slot = (0 : Fin 4) then some outer else if slot = 1 ∨ slot = 2 then some inner else none
 catalogue := by
   intro slot descriptor found
   split at found
   · cases Option.some.inj found; rfl
   · split at found
     · cases Option.some.inj found; rfl
     · cases found
 bodies_opaque := by intro _ _ _; rfl
 seed := 3
abbrev interpretation : GeneralNominalInspection.Interpretation where
 primitives := fun _ => none
 invariantNominal := fun _ => true
 disjoint := by intro _ _; rfl
abbrev root : GeneralSourceDictionaries.Occurrence roles :=
 ⟨0,⟨0,fun _ => (0,0),[],by intro _ h; cases h⟩⟩
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
   by_cases zero : slot = (0 : Fin 4)
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
 first := (3,3)
 last := (3,3)
 oldArgs := rfl
 newArgs := rfl
 leftArgs := rfl
 rightArgs := rfl
 binder := 7

private theorem inner_equal (model : GeneralNominalCommonBridge.Assignment)
 (one : GeneralNominalState.Denotes source.base model 1 inner)
 (two : GeneralNominalState.Denotes source.base model 2 inner) :
 Equivalent (model 1).1 (model 2).1 := by
 have first := (GeneralNominalState.denotes_singleton_exact source.base model 1 3 inner rfl).mp one
 have last := (GeneralNominalState.denotes_singleton_exact source.base model 2 3 inner rfl).mp two
 exact ⟨subtype_trans first.1 last.2,subtype_trans last.1 first.2⟩

private theorem outer_iff (model : GeneralNominalCommonBridge.Assignment)
 (equal : Equivalent (model 1).1 (model 2).1) :
 GeneralNominalState.Denotes source.base model 0 point ↔
 GeneralNominalState.Denotes source.base model 0 outer := by
 constructor
 · rintro ⟨values,fits,denotes⟩
   change GeneralNominalState.FitsAll source.base model [.type (1,1)] values at fits
   cases fits with
   | cons head tail =>
     cases tail
     rename_i value
     cases value with
     | inr => cases head
     | inl value => exact ⟨[.inl value],.cons ⟨head.1,subtype_trans head.2 equal.1⟩ .nil,denotes⟩
 · rintro ⟨values,fits,denotes⟩
   change GeneralNominalState.FitsAll source.base model [.type (1,2)] values at fits
   cases fits with
   | cons head tail =>
     cases tail
     rename_i value
     cases value with
     | inr => cases head
     | inl value => exact ⟨[.inl value],.cons ⟨head.1,subtype_trans head.2 equal.2⟩ .nil,denotes⟩

theorem raw_models (model : GeneralNominalCommonBridge.Assignment) :
 GeneralNominalState.Models revision.snapshot model ↔ GeneralNominalState.Models source model := by
 constructor
 · intro valid
   have eq := inner_equal model (valid.2.1 (1 : Fin 4) inner (by rfl)) (valid.2.1 (2 : Fin 4) inner (by rfl))
   refine ⟨valid.1,?_,valid.2.2⟩
   intro slot descriptor found
   by_cases zero : slot = (0 : Fin 4)
   · subst slot
     have same : outer = descriptor := Option.some.inj found
     subst descriptor
     exact (outer_iff model eq).mp (valid.2.1 (0 : Fin 4) point (by rfl))
   · have ne : slot.val ≠ 0 := fun h => zero (Fin.ext h)
     exact valid.2.1 slot descriptor (by simpa [Revision.snapshot,revision,ne] using found)
 · intro valid
   have eq := inner_equal model (valid.2.1 (1 : Fin 4) inner rfl) (valid.2.1 (2 : Fin 4) inner rfl)
   refine ⟨valid.1,?_,valid.2.2⟩
   intro slot descriptor found
   by_cases zero : slot = (0 : Fin 4)
   · subst slot
     have same : point = descriptor := Option.some.inj found
     subst descriptor
     exact (outer_iff model eq).mpr (valid.2.1 0 outer rfl)
   · apply valid.2.1 slot descriptor
     have ne : slot.val ≠ 0 := fun h => zero (Fin.ext h)
     change (if slot.val = 0 then some point else source.nominals slot) = some descriptor at found
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
   by_cases zero : slot = (0 : Fin 4)
   · subst slot
     exact ⟨point,by rfl,by intro p h; cases List.mem_singleton.mp h; rfl⟩
   · have ne : slot.val ≠ 0 := fun h => zero (Fin.ext h)
     exact ⟨descriptor,by simpa [Revision.snapshot,revision,ne] using found,pointed⟩
 · refine ⟨0,?_,point,by rfl,?_⟩
   · rintro ⟨descriptor,found,pointed⟩
     have same : outer = descriptor := Option.some.inj found
     subst descriptor
     exact (by decide +kernel : (1 : Fin 4) ≠ 2)
       (pointed (.type (1,2)) (by simp))
   · intro p h; cases List.mem_singleton.mp h; rfl

abbrev leafValue : Ty := .base .int
abbrev innerValue : Ty := nominal 0 [.inl leafValue]
abbrev model : GeneralNominalCommonBridge.Assignment := fun identity =>
 (if identity = 0 then nominal 0 [.inl innerValue]
  else if identity = 1 ∨ identity = 2 then innerValue else leafValue,Common.rowEmpty)

theorem source_models : GeneralNominalState.Models source model := by
 refine ⟨⟨PresenceNormalForm.all_nil _ _,?_,?_⟩,?_,PresenceNormalForm.all_nil _ _⟩
 · intro _ _ impossible; cases impossible
 · intro _ impossible; cases impossible
 · intro slot descriptor found
   change (if slot = (0 : Fin 4) then some outer else if slot = 1 ∨ slot = 2 then some inner else none) = some descriptor at found
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
       all_goals exact ⟨[.inl leafValue],.cons ⟨subtype_refl _,subtype_refl _⟩ .nil,
         subtype_refl _,subtype_refl _⟩
     · cases found

theorem revised_models : GeneralNominalState.Models revision.snapshot model :=
 (raw_models model).mpr source_models

theorem observed_parent : Observes model (parent shape) innerValue := by
 exact .nominal (.source 0) ⟨subtype_refl _,subtype_refl _⟩ rfl

theorem observed_leaf : Observes model (leaf shape) leafValue := by
 exact .nominal observed_parent ⟨subtype_refl _,subtype_refl _⟩ rfl

theorem parent_unique (actual : Ty) (seen : Observes model (parent shape) actual) :
 Equivalent actual innerValue :=
 nominal_observation_unique model (.argument (.source 0) 0 0) actual innerValue seen observed_parent

theorem leaf_unique (actual : Ty) (seen : Observes model (leaf shape) actual) :
 Equivalent actual leafValue :=
 nominal_observation_unique model (.argument (.argument (.source 0) 0 0) 0 0)
   actual leafValue seen observed_leaf

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
   · refine ⟨⟨leafValue,observed_leaf⟩,?_⟩
     intro a seen
     exact ⟨(leaf_unique a seen).2,(leaf_unique a seen).1⟩
   · refine ⟨⟨leafValue,observed_leaf⟩,?_⟩
     intro a seen
     exact ⟨(leaf_unique a seen).2,(leaf_unique a seen).1⟩
 · intro test member actual seen
   cases List.mem_singleton.mp member
   exact ⟨[.inl leafValue],rfl,parent_unique actual seen⟩
 · intro first hf last hl _ ref origin actual seen
   simp only [beforeReport,List.mem_cons,List.not_mem_nil,or_false] at hf hl
   rcases hf with rfl | rfl <;> rcases hl with rfl | rfl
   all_goals cases Option.some.inj origin
   all_goals exact ⟨(leaf_unique actual seen).2,(leaf_unique actual seen).1⟩
 · intro first hf last hl _ a b ha hb x y hx hy
   simp only [beforeReport,List.mem_cons,List.not_mem_nil,or_false] at hf hl
   rcases hf with rfl | rfl <;> rcases hl with rfl | rfl
   all_goals cases Option.some.inj ha; cases Option.some.inj hb
   all_goals exact ⟨subtype_trans (leaf_unique x hx).1 (leaf_unique y hy).2,
     subtype_trans (leaf_unique y hy).1 (leaf_unique x hx).2⟩

theorem new_projection : ProjectionModels revision.snapshot
 (inspect revision.snapshot (query shape) ((0 : Fin 4),(0 : Fin 4)) none) model :=
 current_projection shape model revised_models old_projection

theorem actual_reobserve : GeneralNominalReobservationSteps.Step registry root start revision.result :=
 ⟨root,.root,.reobserve root revision certified improves⟩

theorem duplicate_binding_collapse :
 bindings source (inspect source (query shape) (0,0) none) = [(7,3,3),(7,3,3)] ∧
 bindings revision.snapshot (inspect revision.snapshot (query shape) ((0 : Fin 4),(0 : Fin 4)) none) = [(7,3,3)] :=
 ⟨bindings_before shape,bindings_after shape⟩

theorem start_models : Models start model :=
 (initial_models ⟨source,interpretation⟩ root model).mpr source_models

theorem result_models : Models revision.result model :=
 (certified.exact model).mpr start_models

theorem positive_collapse (registry : GeneralDeclarations.Registry) :
 GeneralNominalReobservationSteps.Step registry root start revision.result ∧
 Improves revision ∧ Models start model ∧ Models revision.result model ∧
 ProjectionModels source (inspect source (query shape) (0,0) none) model ∧
 ProjectionModels revision.snapshot
   (inspect revision.snapshot (query shape) ((0 : Fin 4),(0 : Fin 4)) none) model :=
 ⟨actual_reobserve,improves,start_models,result_models,old_projection,new_projection⟩

abbrev tracked : GeneralNominalSupport.Tracked roles :=
 ⟨⟨source,interpretation⟩,start,[]⟩
noncomputable abbrev revisedTracked : GeneralNominalSupport.Tracked roles :=
 {tracked with current := revision.result}

theorem initial_source : GeneralNominalSourceFormation.InitialSource
 GeneralDeclarationExamples.registry ⟨source,interpretation⟩ root := by
 refine ⟨rfl,⟨rfl,?_⟩,?_,?_,?_,rfl⟩
 · intro name primitive found; cases found
 · constructor
   · intro index
     change (0 : Nat) ∈ GeneralNominalState.sources source ∧ (0 : Nat) ∈ GeneralNominalState.sources source
     exact ⟨by decide +kernel,by decide +kernel⟩
   · intro output member; cases member
 · intro model valid index
   exact subtype_refl _
 · intro identity member
   simp [GeneralNominalState.sources,List.ofFn_succ] at member
   change identity ≤ 3
   omega

theorem actual_value_step : GeneralNominalValueSteps.Step GeneralDeclarationExamples.registry
 root tracked revisedTracked :=
 ⟨root,.root,.administrative root revision.result (.reobserve root revision certified improves)⟩

theorem value_formed : GeneralNominalValueSteps.SourceFormed GeneralDeclarationExamples.registry
 root revisedTracked :=
 .update (.initial ⟨source,interpretation⟩ initial_source) actual_value_step

theorem value_positive_collapse :
 GeneralNominalValueSteps.SourceFormed GeneralDeclarationExamples.registry root revisedTracked ∧
 Models revisedTracked.current model ∧
 (inspect source (query shape) (0,0) none).captures.length = 2 ∧
 (inspect revision.snapshot (query shape) ((0 : Fin 4),(0 : Fin 4)) none).captures.length = 1 :=
 ⟨value_formed,result_models,capture_count_drops shape⟩

end Yulang.GeneralDictionarySemanticCollapseExample
