import Yulang.GeneralNominalRefreshFork

/-! Applicability in the two model-equivalent refreshed snapshots. The precise
observation selects the concrete nested nominal leaf; the wider observation
blocks inspection at its upper endpoint. -/
namespace Yulang.GeneralNominalRefreshForkClassification

open GeneralNominalRefreshFork GeneralDeclarations GeneralDeclarationPatterns
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralSourceDictionaries GeneralNominalSaturationState CommonNominalFullCarrier
open GeneralDeclarationExamples (roles)

theorem list_congr {first last : Ty} (same : Equivalent first last) :
    Equivalent (list first) (list last) := by
  have direction {a b : Ty} (equiv : Equivalent a b) : Subtype (list a) (list b) := by
    apply (nominal_regular_invariant_exact ..).mpr
    refine ⟨rfl,rfl,?_⟩
    intro index x y one two
    cases index with
    | zero =>
      have hx := Option.some.inj one; have hy := Option.some.inj two
      subst x; subst y; exact equiv
    | succ index => simp at one
  exact ⟨direction same,direction ⟨same.2,same.1⟩⟩

theorem point_nominal (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (state choice) m) (slot target : Fin 5)
    (recorded : (state choice).nominals slot = some (descriptor (target,target))) :
    Equivalent (m slot.val).1 (list (m target.val).1) := by
  obtain ⟨values,fits,equal⟩ := valid.2.1 slot _ recorded
  change GeneralNominalState.FitsAll base m [.type (target,target)] values at fits
  cases fits with
  | @cons parameter value parameters values head tail =>
    cases tail
    cases value with
    | inr => cases head
    | inl value =>
      have congruence := list_congr (first := value) (last := (m target.val).1) ⟨head.2,head.1⟩
      exact ⟨subtype_trans equal.1 congruence.1,subtype_trans congruence.2 equal.2⟩

abbrev outer : Origin := .nominal (.source 0) 0 0
abbrev inner : Origin := .nominal outer 0 0
abbrev calculated : Report (state (some false)) where
  inspected := [(0,0),(2,2),(3,3)]
  checked := [(0,0),(0,0),(2,2),(3,3)]
  anchors := [(outer,(2,2)),(inner,(3,3))]
  tests := [(outer,.nominal 0 1),(inner,.scalar .int)]

theorem point_report : report (context (some false)) declaration [(0,0)] = calculated := by
  simp [report,GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,inspectMany,inspect,
    typeArguments,Report.visit,Report.append,calculated,state,view]
  rw [inspectMany.eq_2,inspectMany.eq_1,inspect.eq_5]
  simp [typeArguments,Report.visit,Report.append]
  rw [inspectMany.eq_2,inspectMany.eq_1,inspect.eq_3]
  simp [Report.visit,Report.append]

theorem wide_blocked : (report (context (some true)) declaration [(0,0)]).blocked = [(2,4)] := by
  simp [report,GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,inspectMany,inspect,
    typeArguments,Report.visit,Report.append,state,view]
  rw [inspectMany.eq_2,inspectMany.eq_1,inspect.eq_5]
  simp [typeArguments,Report.visit,Report.append,block]

theorem located (choice : Option Bool) : arguments (context choice) root = some [(0,0)] := by
  change arguments (context none) root = some [(0,0)]
  decide +kernel

theorem children_empty (choice : Option Bool) (checked : DeclarationChecked registry.constructors roles declaration)
    (bindings : GeneralNominalAllocation.Bindings) :
    GeneralNominalAllocation.children (state choice) registry root declaration checked bindings = [] := by
  unfold GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil]
  rfl

theorem schema_empty (choice : Option Bool) (checked : DeclarationChecked registry.constructors roles declaration) :
    generated registry (context choice) root declaration checked [(0,0)] = {} := by
  unfold generated GeneralNominalMaterialization.requests GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil]
  rfl

theorem point_projections (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (state (some false)) m) :
    ProjectionModels (state (some false)) calculated m := by
  have outerSeen : Observes m outer (m 2).1 :=
    .nominal (.source 0) (point_nominal m valid 0 2 rfl) rfl
  have innerSeen : Observes m inner (m 3).1 :=
    .nominal outerSeen (point_nominal m valid 2 3 rfl) rfl
  have outerEqual (actual : Ty) (seen : Observes m outer actual) : Equivalent actual (m 2).1 :=
    nominal_observation_unique m (.argument (.source 0) 0 0) actual (m 2).1 seen outerSeen
  have innerEqual (actual : Ty) (seen : Observes m inner actual) : Equivalent actual (m 3).1 :=
    nominal_observation_unique m (.argument (.argument (.source 0) 0 0) 0 0) actual (m 3).1 seen innerSeen
  refine ⟨?_,?_,?_,?_⟩
  · intro anchor member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact ⟨⟨_,outerSeen⟩,fun actual seen => ⟨(outerEqual actual seen).2,(outerEqual actual seen).1⟩⟩
    · exact ⟨⟨_,innerSeen⟩,fun actual seen => ⟨(innerEqual actual seen).2,(innerEqual actual seen).1⟩⟩
  · intro test member actual seen
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · have same := point_nominal m valid 2 3 rfl
      exact ⟨[.inl (m 3).1],rfl,subtype_trans (outerEqual actual seen).1 same.1,
        subtype_trans same.2 (outerEqual actual seen).2⟩
    · exact ⟨subtype_trans (innerEqual actual seen).1 (scalar_three m valid).1,
        subtype_trans (scalar_three m valid).2 (innerEqual actual seen).2⟩
  · intro first member; cases member
  · intro first member; cases member

theorem point_branch (checked : DeclarationChecked registry.constructors roles declaration)
    (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (state (some false)) m) :
    BranchModels registry (context (some false)) root declaration checked [(0,0)] m := by
  refine ⟨?_,?_,?_⟩
  · unfold privateState
    rw [point_report]
    apply (GeneralNominalState.extend_models ..).mpr
    constructor
    · apply (GeneralNominalAllocation.propagate_models ..).mpr
      refine ⟨valid,?_,?_⟩
      · intro first member; cases member
      · exact PresenceNormalForm.all_nil _ _
    · intro atom member
      simp only [selfChecks,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> exact subtype_refl _
  · rw [point_report]; exact point_projections m valid
  · rw [schema_empty]; exact GeneralNominalMaterialization.empty_models ..

theorem fresh (choice : Option Bool) : GeneralNominalAllocation.Fresh (state choice) registry root.identity := by
  intro key member
  simp [GeneralNominalAllocation.keys,GeneralNominalAllocation.declarationKeys,
    declaration,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,
    variablesArgs,Pattern.variables] at member

theorem point_prepared : Prepared registry (context (some false)) root declaration declaration_checked := by
  refine ⟨metadata _,linked _,fresh _,[(0,0)],located _,?_,?_,model,?_⟩
  · rw [point_report]; exact ⟨rfl,rfl,rfl⟩
  · exact ⟨(by intro output member; cases member),(by rw [schema_empty])⟩
  · exact point_branch declaration_checked model (after_models false).1

theorem point_survivor : Survivor registry (context (some false)) root 90 [] := by
  refine ⟨?_,declaration,by simp,declaration_checked,rfl,rfl,[(0,0)],located _,point_prepared,?_⟩
  · rintro ⟨index,unknown⟩; exact unknown (zero_known false)
  · exact (children_empty ..).symm

theorem wide_not_prepared (checked : DeclarationChecked registry.constructors roles declaration) :
    ¬ Prepared registry (context (some true)) root declaration checked := by
  rintro ⟨_,_,_,bounds,found,finished,_⟩
  have same := Option.some.inj ((located _).symm.trans found)
  subst bounds
  have impossible := finished.1
  rw [wide_blocked] at impossible
  cases impossible

theorem wide_not_failed (checked : DeclarationChecked registry.constructors roles declaration) :
    ¬ Failed registry (context (some true)) root declaration checked := by
  rintro ⟨_,_,bounds,found,finished,_⟩
  have same := Option.some.inj ((located _).symm.trans found)
  subst bounds
  rw [wide_blocked] at finished
  cases finished

theorem wide_inspection_pending : InspectionPending registry (context (some true)) root :=
  ⟨(by rintro ⟨index,unknown⟩; exact unknown (zero_known true)),declaration,by simp,declaration_checked,rfl,
    wide_not_failed declaration_checked,wide_not_prepared declaration_checked⟩

end Yulang.GeneralNominalRefreshForkClassification
