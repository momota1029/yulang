import Yulang.GeneralNominalCenteredHeadMatInspectionSemantics

/-! Ground source labels initialize the total semantic relation. The root
centers are the source points, and no extra source contract is used. -/
namespace Yulang.GeneralNominalCenteredHeadMatSourceLabels
open GeneralDeclarationPatterns GeneralNominalInspection GeneralNominalClosedPatternNormal
open GeneralNominalCenteredHeadMatPatternSemantics
open GeneralNominalCenteredHeadMatCompilerSemantics (algebra)
open GeneralNominalCenteredHeadMatSemanticLabels
open GeneralNominalCenteredHeadMatInspectionSemantics (closed_value)
open GeneralNominalOriginTerms GeneralNominalFiniteMeaning GeneralNominalCompoundReadback
open GeneralNominalCenters GeneralSourceDictionaries
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent)
variable {labels : List Pattern}

mutual
  theorem translated_closed (pattern : Pattern)
      (known : ClosedQuery (translate constructors interpretation pattern)) : pattern.variables = [] := by
    cases pattern with
    | var | join => simp only [translate,ClosedQuery] at known
    | variant tag payload =>
        simp only [translate,ClosedQuery] at known
        have child := known.2.2 _ (List.mem_singleton_self _)
        split at child
        · simp only [ClosedQuery] at child
        · exact translated_closed payload child
    | app key arguments =>
        rw [translate.eq_def] at known
        dsimp only at known
        split at known
        · rfl
        · rfl
        · rfl
        · simp only [ClosedQuery] at known
          have first := translated_closed _ (known.2.2 _ (List.mem_cons_self ..))
          have last := translated_closed _ (known.2.2 _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
          simp only [Pattern.variables,variablesArgs,first,last,List.append_nil]
        · split at known
          · split at known
            · simp only [ClosedQuery] at known
              exact translated_args_closed _ (fun argument member =>
                known _ (List.mem_map.mpr ⟨⟨argument,member⟩,List.mem_attach ..,rfl⟩))
            · simp only [ClosedQuery] at known
          · simp only [ClosedQuery] at known
    | record label payload tail =>
        simp only [translate] at known
        split at known
        · rename_i labels children tailQuery
          have parts := sorted_fields label _ labels children (record_length tail tailQuery) known
          have one := translated_closed payload parts.1
          have rest := translated_closed tail (by rw [tailQuery]; exact parts.2.1)
          simp only [Pattern.variables,one,rest,List.append_nil]
        · simp only [ClosedQuery] at known
    termination_by sizeOf pattern

  theorem translated_args_closed (patterns : List Pattern)
      (known : ∀ pattern ∈ patterns, ClosedQuery (translate constructors interpretation pattern)) : variablesArgs patterns = [] := by
    cases patterns with
    | nil => rfl
    | cons head tail =>
        simp only [variablesArgs,translated_closed head (known head (List.mem_cons_self ..)),
          translated_args_closed tail (fun pattern member => known pattern (List.mem_cons_of_mem _ member)),List.append_nil]
    termination_by sizeOf patterns
end

theorem closed_counted (closed : GeneralNominalGroundAccessibility.ClosedTerm context pattern term)
    (equal : Equivalent value (denote (fun _ => .bottom) term)) :
    CountedMeaning (algebra context.state.constructors context.interpretation) value pattern := by
  have query : ClosedQuery (translate context.state.constructors context.interpretation (normalize pattern)) := by
    rw [closed.1]
    exact quote_closed term closed.2.1 closed.2.2
  exact ⟨translated_closed _ query,GeneralNominalClosedSubstitution.translated_covered _ query,
    eqv_trans equal (eqv_symm (closed_value closed))⟩

theorem point_root_inputs {roles : Roles.RoleDecls} {root : Occurrence roles}
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root labels)
    (valid : GeneralNominalState.Models context.state model) :
    Inputs (algebra context.state.constructors context.interpretation) model
      (rootSite context.state.seed root) labels := by
  obtain ⟨length,terms⟩ := ground
  refine ⟨length,?_⟩
  intro index
  obtain ⟨term,closed,meaning⟩ := terms index
  rw [point_center context.state.seed root index (point index)]
  exact closed_counted closed (meaning model valid)

theorem old_inputs {roles : Roles.RoleDecls} {site : Site roles}
    (known : GeneralNominalGroundAccessibility.Inputs context model site.observed labels) :
    Inputs (algebra context.state.constructors context.interpretation) model site labels := by
  obtain ⟨length,terms⟩ := known
  refine ⟨length,?_⟩
  intro index
  obtain ⟨term,closed,_,seen⟩ := terms index
  have retained : site.observed.inputs[index.val]? = some (some (.source (site.center index))) := by
    simp only [Site.observed,List.getElem?_ofFn,index.isLt,dite_eq_left]
  have actual := (seen _ retained).2 _ (.source _)
  exact closed_counted closed actual

end Yulang.GeneralNominalCenteredHeadMatSourceLabels
