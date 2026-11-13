import Yulang.GeneralNominalCaptureAssembly

/-! Constructor-wise matching accounts for the whole head, including each
variable occurrence and the complete canonical record spine. -/
set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralNominalHeadMatchMass
open GeneralDeclarationPatterns GeneralNominalInspection
open GeneralNominalOriginTerms GeneralNominalCompoundReadback
open GeneralNominalClosedPatternNormal GeneralNominalClosedPatternMass
open GeneralNominalGroundAccessibility GeneralPatternGroundSubstitution

def weighted (capture : Nat → Nat) : Query → Nat
  | .variables names => (names.map capture).sum
  | .deferred _ => 0
  | .scalar _ => 1
  | .node shape children =>
      (match shape with | .record labels => labels.length+1 | _ => 1) +
        (children.map (weighted capture)).sum
  | .nominal _ children => 1 + (children.map (weighted capture)).sum

def Complete : Query → Prop
  | .deferred _ => False
  | .variables _ | .scalar _ => True
  | .node _ children | .nominal _ children => ∀ child ∈ children, Complete child

theorem sorted_weight (capture : Nat → Nat) (label : Nat) (payload : Query)
    (labels : List Nat) (children : List Query) (length : children.length = labels.length) :
    weighted capture (.node (.record
      ((((label,payload) :: labels.zip children).mergeSort (fun first last => first.1 ≤ last.1)).map Prod.fst))
      ((((label,payload) :: labels.zip children).mergeSort (fun first last => first.1 ≤ last.1)).map Prod.snd)) =
      1 + weighted capture payload + weighted capture (.node (.record labels) children) := by
  have permutation := List.Perm.map (fun field : Nat × Query => weighted capture field.2)
    (List.mergeSort_perm ((label,payload) :: labels.zip children) (fun first last => first.1 ≤ last.1))
  have sum := List.Perm.sum_nat permutation
  have mapped : ((labels.zip children).map fun field => weighted capture field.2) = children.map (weighted capture) := by
    simpa only [List.map_map,Function.comp_def] using congrArg (List.map (weighted capture))
      (List.map_snd_zip (Nat.le_of_eq length))
  simp only [List.map_cons,List.sum_cons,mapped] at sum
  simp only [weighted,List.length_map,List.length_mergeSort,List.length_cons,List.length_zip,
    length,Nat.min_self,List.map_map,Function.comp_def,sum]
  omega

mutual
  theorem translated_count (pattern : Pattern) (covered : GeneralDeclarationPatterns.covered pattern = true)
      (complete : Complete (translate constructors interpretation pattern)) (capture : Roles.Subst) :
      (pattern.encode.subst capture).size =
        weighted (fun name => (capture name).size) (translate constructors interpretation pattern) := by
    cases pattern with
    | var name => simp [Pattern.encode,Roles.Term.subst,translate,weighted]
    | join => cases covered
    | variant tag payload =>
      have query : translate constructors interpretation (.variant tag payload) =
          .node (.variant tag) [translate constructors interpretation payload] := by
        simp only [translate]
        split
        · rename_i names found
          obtain ⟨name,rfl,rfl⟩ := covered_plain_names payload covered found
          simp only [translate]
        · rfl
      rw [query] at complete ⊢
      simp only [Complete] at complete
      have child := translated_count payload covered (complete _ (List.mem_singleton_self _)) capture
      simp only [Pattern.encode,Roles.Term.subst,Roles.substArgs,Roles.Term.size,Roles.argsSize,
        weighted,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,child,Nat.add_zero]
    | app key arguments =>
      rw [translate.eq_def] at complete ⊢
      dsimp only at complete ⊢
      split at complete
      · simp_all only [Pattern.encode,Roles.Term.subst,Roles.substArgs,Roles.Term.size,encodeArgs,Roles.argsSize,weighted]
      · simp_all only [Pattern.encode,Roles.Term.subst,Roles.substArgs,Roles.Term.size,encodeArgs,Roles.argsSize,
          weighted,List.length_nil,List.map_nil,List.sum_nil,Nat.zero_add,Nat.add_zero]
      · simp_all only [Pattern.encode,Roles.Term.subst,Roles.substArgs,Roles.Term.size,encodeArgs,Roles.argsSize,
          weighted,List.map_nil,List.sum_nil,Nat.add_zero]
      · rename_i firstPattern lastPattern primitive
        simp only [Complete] at complete
        have parts : GeneralDeclarationPatterns.covered firstPattern = true ∧ GeneralDeclarationPatterns.covered lastPattern = true := by
          simpa only [GeneralDeclarationPatterns.covered,coveredArgs,Bool.and_eq_true,Bool.true_and,and_true] using covered
        have first := translated_count _ parts.1 (complete _ (List.mem_cons_self ..)) capture
        have last := translated_count _ parts.2 (complete _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))) capture
        simp_all only [Pattern.encode,Roles.Term.subst,Roles.substArgs,Roles.Term.size,encodeArgs,Roles.argsSize,
          weighted,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
      · split at complete
        · split at complete
          · simp only [Complete] at complete
            have parts := translated_counts _ covered
              (fun pattern member => complete _ (List.mem_map.mpr ⟨⟨pattern,member⟩,List.mem_attach ..,rfl⟩)) capture
            simp_all only [Pattern.encode,Roles.Term.subst,Roles.Term.size,ite_true,weighted,
              List.map_map,Function.comp_def,List.attach_map_val]
          · simp only [Complete] at complete
        · simp only [Complete] at complete
    | record label payload tail =>
      have parts : GeneralDeclarationPatterns.covered payload = true ∧ GeneralDeclarationPatterns.covered tail = true := by
        simpa only [GeneralDeclarationPatterns.covered,Bool.and_eq_true] using covered
      rw [translate.eq_def] at complete ⊢
      dsimp only at complete ⊢
      split at complete
      · rename_i labels children tailQuery
        simp only [Complete] at complete
        have field (entry : Nat × Query) (member : entry ∈ (label,translate constructors interpretation payload) :: labels.zip children) :
            Complete entry.2 := complete entry.2 (List.mem_map.mpr ⟨entry,List.mem_mergeSort.mpr member,rfl⟩)
        have first := translated_count payload parts.1 (field _ (List.mem_cons_self ..)) capture
        have tailComplete : Complete (translate constructors interpretation tail) := by
          rw [tailQuery]
          simp only [Complete]
          intro child member
          have mapped := List.map_snd_zip (Nat.le_of_eq (record_length tail tailQuery))
          rw [← mapped] at member
          obtain ⟨entry,present,rfl⟩ := List.mem_map.mp member
          exact field entry (List.mem_cons_of_mem _ present)
        have rest := translated_count tail parts.2 tailComplete capture
        rw [tailQuery] at rest
        simp only [sorted_weight _ label _ labels children (record_length tail tailQuery),
          Pattern.encode,Roles.Term.subst,Roles.substArgs,Roles.Term.size,Roles.argsSize,first,rest,Nat.add_zero]
        omega
      · simp only [Complete] at complete
    termination_by sizeOf pattern

  theorem translated_counts (patterns : List Pattern) (covered : coveredArgs patterns = true)
      (complete : ∀ pattern ∈ patterns, Complete (translate constructors interpretation pattern)) (capture : Roles.Subst) :
      Roles.argsSize (Roles.substArgs capture (encodeArgs patterns)) =
        (patterns.map fun pattern => weighted (fun name => (capture name).size) (translate constructors interpretation pattern)).sum := by
    cases patterns with
    | nil => rfl
    | cons head tail =>
      have parts : GeneralDeclarationPatterns.covered head = true ∧ coveredArgs tail = true := by
        simpa only [coveredArgs,Bool.and_eq_true] using covered
      simp only [encodeArgs,Roles.substArgs,Roles.argsSize,List.map_cons,List.sum_cons,
        translated_count head parts.1 (complete head (List.mem_cons_self ..)) capture,
        translated_counts tail parts.2 (fun pattern member => complete pattern (List.mem_cons_of_mem _ member)) capture]
    termination_by sizeOf patterns
end

inductive Matches (relation : Nat → Expr Nat → Prop) : Query → Expr Nat → Prop
  | capture (matched : relation name term) : Matches relation (.variables [name]) term
  | scalar (children : Fin (arity (.scalar base)) → Expr Nat) :
      Matches relation (.scalar base) (.node (.scalar base) children)
  | structural (shape : GeneralNormalizedObservation.Shape) (queries : Fin shape.arity → Query)
      (children : Fin (arity (.structural shape)) → Expr Nat)
      (matched : ∀ index, Matches relation (queries index) (children index)) :
      Matches relation (.node shape (List.ofFn queries)) (.node (.structural shape) children)
  | nominal (name count : Nat) (queries : Fin count → Query) (children : Fin (arity (.nominal name count)) → Expr Nat)
      (matched : ∀ index, Matches relation (queries index) (children index)) :
      Matches relation (.nominal name (List.ofFn queries)) (.node (.nominal name count) children)

private theorem sums_le (n : Nat) (first last : Fin n → Nat) (below : ∀ index, first index ≤ last index) :
    (List.ofFn first).sum ≤ (List.ofFn last).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ,List.sum_cons]
    exact Nat.add_le_add (below 0) (ih _ _ (fun index => below index.succ))

theorem matched_mass (matched : Matches relation query term)
    (bounded : ∀ name term, relation name term → capture name ≤ weight term) :
    weighted capture query ≤ weight term := by
  induction matched with
  | capture matched => simpa only [weighted,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using bounded _ _ matched
  | scalar => simp only [weighted,weight,quote,queryMass]; exact Nat.le_refl 1
  | structural shape queries children matched ih =>
    have total := sums_le shape.arity _ _ ih
    cases shape <;>
      simp only [weighted,weight,quote,queryMass,List.map_ofFn,Function.comp_def] <;>
      apply Nat.add_le_add_left <;> exact total
  | nominal name count queries children matched ih =>
    simp only [weighted,weight,quote,queryMass,List.map_ofFn,Function.comp_def]
    apply Nat.add_le_add_left
    exact sums_le count _ _ ih


theorem matched_mass_eq (matched : Matches relation query term)
    (equal : ∀ name term, relation name term → capture name = weight term) :
    weighted capture query = weight term := by
  induction matched with
  | capture matched => simpa only [weighted,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using equal _ _ matched
  | scalar => simp only [weighted,weight,quote,queryMass]
  | structural shape queries children matched ih =>
    have total := congrArg (fun f : Fin shape.arity → Nat => (List.ofFn f).sum) (funext ih)
    cases shape <;>
      simp only [weighted,weight,quote,queryMass,List.map_ofFn,Function.comp_def] <;>
      congr 1 <;> exact total
  | nominal name count queries children matched ih =>
    have total := congrArg (fun f : Fin count → Nat => (List.ofFn f).sum) (funext ih)
    simp only [weighted,weight,quote,queryMass,List.map_ofFn,Function.comp_def]
    exact congrArg (fun size => 1 + size) total

theorem instantiated_bound (pattern : Pattern) (covered : GeneralDeclarationPatterns.covered pattern = true)
    (complete : Complete (translate context.state.constructors context.interpretation pattern))
    (closed : ClosedTerm context label term)
    (matched : Matches relation (translate context.state.constructors context.interpretation pattern) term)
    (capture : Nat → Pattern)
    (bounded : ∀ name term, relation name term → (normalize (capture name)).encode.size ≤ weight term) :
    GeneralNominalPatersonLineage.mass [pattern.subst capture] ≤ GeneralNominalPatersonLineage.mass [label] := by
  have upper := (GeneralPatternConservativeSubstitution.substitution_bounds pattern covered capture).2
  rw [translated_count pattern covered complete] at upper
  have matched := matched_mass matched bounded
  rw [closed_mass closed]
  simpa only [GeneralNominalPatersonLineage.mass,counted,normalizeArgs,encodeArgs,Roles.argsSize,Nat.add_zero] using
    Nat.le_trans upper matched

end Yulang.GeneralNominalHeadMatchMass
