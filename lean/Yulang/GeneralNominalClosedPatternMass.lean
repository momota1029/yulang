import Yulang.GeneralNominalClosedPatternNormal

/-! The checker counts a record spine, including its empty tail. Finite
query weights retain this cost through field sorting and source reification. -/
namespace Yulang.GeneralNominalClosedPatternMass
open GeneralDeclarationPatterns GeneralNominalInspection
open GeneralNominalOriginTerms GeneralNominalCompoundReadback
open GeneralNominalClosedPatternNormal GeneralNominalGroundAccessibility

def queryMass : Query → Nat
  | .variables _ | .deferred _ => 0
  | .scalar _ => 1
  | .node shape children =>
      (match shape with | .record labels => labels.length+1 | _ => 1) + (children.map queryMass).sum
  | .nominal _ children => 1 + (children.map queryMass).sum

def weight (term : Expr Nat) : Nat := queryMass (quote term)

theorem record_sort_mass (label : Nat) (payload : Query) (labels : List Nat) (children : List Query)
    (length : children.length = labels.length) :
    queryMass (.node (.record
      ((((label,payload) :: labels.zip children).mergeSort (fun first last => first.1 ≤ last.1)).map Prod.fst))
      ((((label,payload) :: labels.zip children).mergeSort (fun first last => first.1 ≤ last.1)).map Prod.snd)) =
      1 + queryMass payload + queryMass (.node (.record labels) children) := by
  have permutation := List.Perm.map (fun field : Nat × Query => queryMass field.2)
    (List.mergeSort_perm ((label,payload) :: labels.zip children) (fun first last => first.1 ≤ last.1))
  have sum := List.Perm.sum_nat permutation
  have mapped : ((labels.zip children).map fun field => queryMass field.2) = children.map queryMass := by
    simpa only [List.map_map,Function.comp_def] using congrArg (List.map queryMass)
      (List.map_snd_zip (Nat.le_of_eq length))
  simp only [List.map_cons,List.sum_cons,mapped] at sum
  simp only [queryMass,List.length_map,List.length_mergeSort,List.length_cons,List.length_zip,
    length,Nat.min_self,List.map_map,Function.comp_def,sum]
  omega

mutual
  theorem translated_mass (pattern : Pattern) (known : ClosedQuery (translate constructors interpretation pattern)) :
      pattern.encode.size = queryMass (translate constructors interpretation pattern) := by
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
      have child := translated_mass payload (known.2.2 _ (List.mem_singleton_self _))
      simp only [Pattern.encode,Roles.Term.size,Roles.argsSize,queryMass,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,child]
    | app key arguments =>
      rw [translate.eq_def] at known ⊢
      dsimp only at known ⊢
      split at known
      · simp_all only [Pattern.encode,Roles.Term.size,encodeArgs,Roles.argsSize,queryMass]
      · simp_all only [Pattern.encode,Roles.Term.size,encodeArgs,Roles.argsSize,queryMass,List.length_nil,List.map_nil,List.sum_nil,Nat.zero_add,Nat.add_zero]
      · simp_all only [Pattern.encode,Roles.Term.size,encodeArgs,Roles.argsSize,queryMass,List.map_nil,List.sum_nil,Nat.add_zero]
      · simp only [ClosedQuery] at known
        have first := translated_mass _ (known.2.2 _ (List.mem_cons_self ..))
        have last := translated_mass _ (known.2.2 _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
        simp_all only [Pattern.encode,Roles.Term.size,encodeArgs,Roles.argsSize,queryMass,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
      · split at known
        · split at known
          · simp only [ClosedQuery] at known
            have parts := translated_args_mass _ (constructors := constructors) (interpretation := interpretation)
              (fun pattern member => known _ (List.mem_map.mpr ⟨⟨pattern,member⟩,List.mem_attach ..,rfl⟩))
            simp_all only [Pattern.encode,Roles.Term.size,ite_true,queryMass,List.map_map,Function.comp_def,List.attach_map_val]
          · simp only [ClosedQuery] at known
        · simp only [ClosedQuery] at known
    | record label payload tail =>
      rw [translate.eq_def] at known ⊢
      dsimp only at known ⊢
      split at known
      · rename_i labels children tailQuery
        have split := sorted_fields label _ labels children (record_length tail tailQuery) known
        have one := translated_mass payload split.1
        have two := translated_mass tail (by rw [tailQuery]; exact split.2.1)
        rw [tailQuery] at two
        simp only [record_sort_mass label _ labels children (record_length tail tailQuery),
          Pattern.encode,Roles.Term.size,Roles.argsSize,one,two,Nat.add_zero]
        omega
      · simp only [ClosedQuery] at known
    termination_by sizeOf pattern

  theorem translated_args_mass (patterns : List Pattern)
      (known : ∀ pattern ∈ patterns, ClosedQuery (translate constructors interpretation pattern)) :
      Roles.argsSize (encodeArgs patterns) =
        (patterns.map fun pattern => queryMass (translate constructors interpretation pattern)).sum := by
    cases patterns with
    | nil => rfl
    | cons head tail =>
      simp only [encodeArgs,Roles.argsSize,List.map_cons,List.sum_cons,
        translated_mass head (known head (List.mem_cons_self ..)),
        translated_args_mass tail (fun pattern member => known pattern (List.mem_cons_of_mem head member))]
    termination_by sizeOf patterns
end

theorem closed_mass (known : ClosedTerm context pattern term) :
    GeneralNominalPatersonLineage.mass [pattern] = weight term := by
  have measured := translated_mass (normalize pattern) (by rw [known.1]; exact quote_closed term known.2.1 known.2.2)
  simpa only [GeneralNominalPatersonLineage.mass,counted,normalizeArgs,encodeArgs,Roles.argsSize,
    Nat.add_zero,known.1,weight] using measured

end Yulang.GeneralNominalClosedPatternMass
