import Yulang.GeneralNominalRecursiveExamples
import Yulang.GeneralNominalStructuralProjectionLaws

/-! A candidate must inspect the anonymous record below an opaque nominal
head. The projection is the actual argument, not an arbitrary interval bound. -/
namespace Yulang.GeneralNominalMixedCandidateExample

open GeneralDeclarations GeneralDeclarationPatterns
open GeneralDeclarationExamples (roles constructors)
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalMixedExamples
open CommonNominalFullCarrier

abbrev declaration : Declaration := ⟨31,0,[.app 0 [.record 7 (.var 0) (.app 4 [])]],[],[],[]⟩
abbrev registry : Registry := ⟨constructors,roles,[declaration]⟩
abbrev interpretation : GeneralNominalInspection.Interpretation :=
  ⟨fun key => if key = 4 then some .emptyRecord else none,fun key => key == 0,
    by intro key nominal; have zero : key = 0 := by simpa using nominal
       subst key; rfl⟩
abbrev context : Context := ⟨state,interpretation⟩
abbrev parameterOrigin := Origin.nominal (.source 1) 0 0
abbrev payloadOrigin := Origin.structural parameterOrigin (.record [7]) 0
abbrev calculated : Report state where
  captures := [⟨0,(1,1),some payloadOrigin⟩]
  inspected := [(1,1),(0,0)]
  checked := [(1,1),(1,1),(0,0),(1,1)]
  anchors := [(parameterOrigin,(0,0)),(payloadOrigin,(1,1))]
  tests := [(parameterOrigin,.structural (.record [7]))]

theorem checked : DeclarationChecked constructors roles declaration := by
  constructor
  · simp [Declaration.Signature,roles,GeneralDeclarationExamples.bareRole]
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors,
      GeneralDeclarationExamples.constructors]
  all_goals intro clause member; cases member

theorem calculated_report : report context declaration [(1,1)] = calculated := by
  unfold report
  have query : GeneralNominalInspection.queries state interpretation declaration =
      [.nominal 0 [.node (.record [7]) [.variables [0]]]] := by
    simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
      GeneralNominalInspection.translate,interpretation,hide]
  rw [query]
  simp [inspectMany,inspect,typeArguments,Report.visit,Report.append]
  rw [inspectMany.eq_2,inspectMany.eq_1,inspect.eq_4]
  simp [Report.visit,Report.append]
  have listed : List.ofFn (fun _ : Fin (state.view.shapes (0 : Fin 1)).arity => (1 : Fin 2)) = [1] := rfl
  rw [listed]
  simp only [List.zip_cons_cons,List.zip_nil_left]
  rw [inspectMany.eq_2,inspectMany.eq_1,inspect.eq_1]
  simp [Report.append,payloadOrigin]

theorem parameter_observed : Observes model parameterOrigin (value 0) :=
  .nominal (.source 1) list_equation rfl

theorem parameter_exact (actual : Ty) (seen : Observes model parameterOrigin actual) : Equivalent actual (value 0) :=
  nominal_observation_unique model (.argument (.source 1) 0 0) actual (value 0) seen parameter_observed

theorem payload_observed : Observes model payloadOrigin (value 1) := by
  apply Observes.structural parameter_observed (values := [value 1]) rfl
  · rw [GeneralNominalStructuralProjectionLaws.singleton_shape]
    exact record_equation
  · rfl

theorem payload_exact (actual : Ty) (seen : Observes model payloadOrigin actual) : Equivalent actual (value 1) :=
  GeneralNominalStructuralProjectionLaws.record_observation model parameterOrigin 7 actual (value 1)
    (fun x hx => ⟨subtype_trans (parameter_exact x hx).1 record_equation.1,
      subtype_trans record_equation.2 (parameter_exact x hx).2⟩) seen

theorem projection_models : ProjectionModels state calculated model := by
  refine ⟨?_,?_,?_,?_⟩
  · intro anchor member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact ⟨⟨value 0,parameter_observed⟩,fun x hx => ⟨(parameter_exact x hx).2,(parameter_exact x hx).1⟩⟩
    · exact ⟨⟨value 1,payload_observed⟩,fun x hx => ⟨(payload_exact x hx).2,(payload_exact x hx).1⟩⟩
  · intro test member actual seen
    have same := List.mem_singleton.mp member; subst test
    refine ⟨[value 1],rfl,?_⟩
    rw [GeneralNominalStructuralProjectionLaws.singleton_shape]
    exact ⟨subtype_trans (parameter_exact actual seen).1 record_equation.1,
      subtype_trans record_equation.2 (parameter_exact actual seen).2⟩
  · intro first one last two _ origin recorded actual seen
    have firstEq := List.mem_singleton.mp one; have lastEq := List.mem_singleton.mp two
    subst first; subst last
    have same := Option.some.inj recorded; subst origin
    exact ⟨(payload_exact actual seen).2,(payload_exact actual seen).1⟩
  · intro first one last two _ a b ha hb x y hx hy
    have firstEq := List.mem_singleton.mp one; have lastEq := List.mem_singleton.mp two
    subst first; subst last
    have ae := Option.some.inj ha; have be := Option.some.inj hb
    subst a; subst b
    exact ⟨subtype_trans (payload_exact x hx).1 (payload_exact y hy).2,
      subtype_trans (payload_exact y hy).1 (payload_exact x hx).2⟩

theorem private_models : GeneralNominalState.Models (privateState registry context showRoot declaration [(1,1)]) model := by
  unfold privateState
  rw [calculated_report]
  apply (GeneralNominalState.extend_models ..).mpr
  constructor
  · apply GeneralNominalUnaryCaptureFacts.propagated_models state registry showRoot.identity declaration 0 rfl model state_models
      (1,1) (subtype_refl _)
  · intro atom member
    simp only [selfChecks,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> exact subtype_refl _

theorem candidate_K2 : CandidateK2 registry context showRoot := by
  refine ⟨GeneralNominalRecursiveExamples.show_list_survivor.1,declaration,by simp,checked,rfl,?_,
    [(1,1)],by decide +kernel,(0,0),?_,anonymous_recursive⟩
  · refine ⟨?_,?_,GeneralNominalUnaryCaptureFacts.initial_fresh _ _ _ (by decide +kernel),
      [(1,1)],by decide +kernel,?_,model,private_models,?_⟩
    · refine ⟨rfl,?_⟩
      intro key primitive recorded
      by_cases four : key = 4
      · subst key
        have same : GeneralCandidateInspection.Primitive.emptyRecord = primitive := Option.some.inj recorded
        subst primitive
        exact ⟨⟨[],4⟩,rfl,rfl⟩
      · simp [four] at recorded
    · obtain ⟨_,_,_,_,_,_,_,_,prepared,_⟩ := GeneralNominalRecursiveExamples.show_list_survivor
      exact prepared.2.1
    · rw [calculated_report]; exact ⟨rfl,rfl,rfl⟩
    · rw [calculated_report]; exact projection_models
  · rw [calculated_report]; simp

end Yulang.GeneralNominalMixedCandidateExample
