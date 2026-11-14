import Yulang.GeneralNominalCenteredHeadMatSemanticLabels

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-! The old finite source labels have their ordinary carrier meanings in the
total pattern algebra. This bridge changes no observation or source guard. -/
namespace Yulang.GeneralNominalCenteredHeadMatInspectionSemantics
open GeneralDeclarationPatterns GeneralNominalInspection
open GeneralNominalCenteredHeadMatPatternSemantics
open GeneralNominalCenteredHeadMatCompilerSemantics (algebra)
open GeneralNominalClosedPatternNormal GeneralNominalFiniteMeaning
open GeneralNominalOriginTerms GeneralNominalCompoundReadback
open GeneralNominalStructuralReadback (recordValues)
open CommonNominalFullCarrier

mutual
  def queryValue : Query → Ty
    | .scalar base => .base base
    | .node shape children => GeneralNominalRecursiveInspection.shapeValue shape (queryValues children)
    | .nominal name children => nominal name ((queryValues children).map Sum.inl)
    | _ => .bottom
  def queryValues : List Query → List Ty
    | [] => []
    | first :: rest => queryValue first :: queryValues rest
end

theorem queryValues_map (queries : List Query) : queryValues queries = queries.map queryValue := by
  induction queries with
  | nil => rfl
  | cons first rest ih => simp only [queryValues,List.map_cons,ih]

theorem quote_value (term : Expr Nat) (closed : term.leaves = []) :
    queryValue (quote term) = denote (fun _ => .bottom) term := by
  induction term with
  | leaf name => simp [Expr.leaves] at closed
  | node test children ih =>
      have child (index : Fin (arity test)) : queryValue (quote (children index)) = denote (fun _ => .bottom) (children index) := by
        apply ih index
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro name member
        have parent : name ∈ (Expr.node test children).leaves := by
          simp only [Expr.leaves,List.mem_flatten,List.mem_ofFn]
          exact ⟨_,⟨index,rfl⟩,member⟩
        rw [closed] at parent
        cases parent
      cases test with
      | scalar => rfl
      | structural shape =>
          simp only [quote,queryValue,queryValues_map,List.map_ofFn,Function.comp_def,denote,build,child]
      | nominal name count =>
          simp only [quote,queryValue,queryValues_map,List.map_ofFn,Function.comp_def,denote,build,child]

theorem record_permutation (permutation : first.Perm last)
    (unique : (first.map Prod.fst).Nodup) : Equivalent (recordValues first) (recordValues last) := by
  induction permutation with
  | nil => exact eqv_refl _
  | cons entry permutation ih =>
      exact record_congr entry.1 (eqv_refl _) (ih (List.nodup_cons.mp unique).2)
  | swap first last rest =>
      have different : first.1 ≠ last.1 := by
        intro same
        exact (List.nodup_cons.mp unique).1 (List.mem_cons.mpr (Or.inl same.symm))
      exact GeneralNominalCommonBridge.swap _ _ (Ne.symm different) _ _ _
  | trans one two ihOne ihTwo =>
      exact eqv_trans (ihOne unique) (ihTwo ((one.map Prod.fst).nodup_iff.mp unique))

theorem sorted_record_value (label : Nat) (payload : Query) (labels : List Nat) (children : List Query)
    (length : children.length = labels.length)
    (unique : (label :: labels).Nodup) :
    Equivalent
      (record label (queryValue payload) (GeneralNominalRecursiveInspection.shapeValue (.record labels) (queryValues children)))
      (queryValue (.node (.record
        ((((label,payload) :: labels.zip children).mergeSort (fun first last => first.1 ≤ last.1)).map Prod.fst))
        ((((label,payload) :: labels.zip children).mergeSort (fun first last => first.1 ≤ last.1)).map Prod.snd))) := by
  let fields := (label,payload) :: labels.zip children
  let sorted := fields.mergeSort (fun first last => first.1 ≤ last.1)
  have zipped (entries : List (Nat × Query)) :
      (entries.map Prod.fst).zip (queryValues (entries.map Prod.snd)) =
        entries.map (fun field => (field.1,queryValue field.2)) := by
    induction entries with
    | nil => rfl
    | cons entry rest ih => simp only [List.map_cons,queryValues,List.zip_cons_cons,ih]
  have tail : labels.zip (queryValues children) =
      (labels.zip children).map (fun field => (field.1,queryValue field.2)) := by
    rw [queryValues_map,List.zip_map_right]
    rfl
  rw [GeneralNominalRecordInversion.record_shape labels (queryValues children)
    (by simp [queryValues_map,length])]
  change Equivalent _ (GeneralNominalRecursiveInspection.shapeValue (.record (sorted.map Prod.fst)) (queryValues (sorted.map Prod.snd)))
  rw [GeneralNominalRecordInversion.record_shape _ _ (by simp [queryValues_map]),zipped,tail]
  change Equivalent (recordValues (fields.map (fun field => (field.1,queryValue field.2)))) _
  apply record_permutation ((List.mergeSort_perm fields _).symm.map _)
  simpa only [fields,List.map_map,Function.comp_def,List.map_cons,List.map_fst_zip (Nat.le_of_eq length.symm)] using unique

mutual
  theorem translated_value (pattern : Pattern)
      (known : ClosedQuery (translate constructors interpretation pattern)) :
      Equivalent (eval (algebra constructors interpretation) variables pattern)
        (queryValue (translate constructors interpretation pattern)) := by
    cases pattern with
    | var | join => simp only [translate,ClosedQuery] at known
    | variant tag payload =>
        have query : translate constructors interpretation (.variant tag payload) =
            .node (.variant tag) [translate constructors interpretation payload] := by
          simp only [translate]
          split
          · simp only [translate,ClosedQuery] at known
            have child := known.2.2 _ (List.mem_singleton_self _)
            rename_i names found
            rw [found] at child
            simp only [ClosedQuery] at child
          · rfl
        rw [query] at known ⊢
        simp only [ClosedQuery] at known
        exact variant_congr tag (translated_value payload (known.2.2 _ (List.mem_singleton_self _)))
    | app key arguments =>
        rw [translate.eq_def] at known ⊢
        dsimp only at known ⊢
        split at known
        · rename_i base primitive
          simp_all [eval,evals,algebra,GeneralNominalCenteredHeadMatCompilerSemantics.application,
            GeneralNominalCenteredHeadMatExpressions.primitiveValue,queryValue,eqv_refl]
        · rename_i primitive
          simp_all [eval,evals,algebra,GeneralNominalCenteredHeadMatCompilerSemantics.application,
            GeneralNominalCenteredHeadMatExpressions.primitiveValue,queryValue,queryValues,eqv_refl]
          exact eqv_refl _
        · rename_i primitive
          simp_all [eval,evals,algebra,GeneralNominalCenteredHeadMatCompilerSemantics.application,
            GeneralNominalCenteredHeadMatExpressions.primitiveValue,queryValue,queryValues,eqv_refl]
          exact eqv_refl _
        · rename_i first last primitive
          simp only [ClosedQuery] at known
          have one := translated_value (variables := variables) first (known.2.2 _ (List.mem_cons_self ..))
          have two := translated_value (variables := variables) last (known.2.2 _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
          simp only [eval,evals,algebra,GeneralNominalCenteredHeadMatCompilerSemantics.application,
            primitive,GeneralNominalCenteredHeadMatExpressions.primitiveValue,queryValue,queryValues]
          exact ⟨(common_pair_iff ..).mpr ⟨one.1,two.1⟩,(common_pair_iff ..).mpr ⟨one.2,two.2⟩⟩
        · split at known
          · rename_i declaration declared
            split at known
            · rename_i accepted
              have primitive := interpretation.disjoint key (((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp accepted).1).1)
              simp only [ClosedQuery] at known
              simp only [eval,algebra,GeneralNominalCenteredHeadMatCompilerSemantics.application,primitive,declared,
                ite_eq_left accepted,queryValue,List.attach_map_val] at known ⊢
              apply GeneralNominalCenteredHeadMatCompilerSemantics.nominal_congr
              exact translated_values _ (fun pattern member => known _ (List.mem_map.mpr ⟨pattern,member,rfl⟩))
            · simp only [ClosedQuery] at known
          · simp only [ClosedQuery] at known
    | record label payload tail =>
        rw [translate.eq_def] at known ⊢
        dsimp only at known ⊢
        split at known
        · rename_i labels children tailQuery
          have split := sorted_fields label _ labels children (record_length tail tailQuery) known
          have one := translated_value (variables := variables) payload split.1
          have two := translated_value (variables := variables) tail (by rw [tailQuery]; exact split.2.1)
          rw [tailQuery] at two
          have tailFacts := split.2.1
          simp only [ClosedQuery] at tailFacts
          exact eqv_trans (record_congr label one two)
            (sorted_record_value label _ labels children (record_length tail tailQuery)
              (List.nodup_cons.mpr ⟨split.2.2,tailFacts.1⟩))
        · simp only [ClosedQuery] at known
    termination_by sizeOf pattern

  theorem translated_values (patterns : List Pattern)
      (known : ∀ pattern ∈ patterns, ClosedQuery (translate constructors interpretation pattern)) :
      GeneralNominalMatchedAssembly.Aligned Equivalent
        (evals (algebra constructors interpretation) variables patterns)
        (queryValues (patterns.map (translate constructors interpretation))) := by
    cases patterns with
    | nil => exact .nil
    | cons first rest =>
        exact .cons (translated_value first (known first (List.mem_cons_self ..)))
          (translated_values rest (fun pattern member => known pattern (List.mem_cons_of_mem first member)))
    termination_by sizeOf patterns
end

theorem closed_value (closed : GeneralNominalGroundAccessibility.ClosedTerm context pattern term) :
    Equivalent (eval (algebra context.state.constructors context.interpretation) variables (normalize pattern))
      (denote (fun _ => .bottom) term) := by
  have known := translated_value (variables := variables) (normalize pattern)
    (by rw [closed.1]; exact quote_closed term closed.2.1 closed.2.2)
  rwa [closed.1,quote_value term closed.2.1] at known

end Yulang.GeneralNominalCenteredHeadMatInspectionSemantics
