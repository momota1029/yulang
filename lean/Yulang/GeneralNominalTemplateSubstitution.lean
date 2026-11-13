import Yulang.GeneralNominalHeadMatchMass

/-! Substitution follows supported record spines and preserves their sorted
field positions. Coverage is required at the normalized template boundary. -/
namespace Yulang.GeneralNominalTemplateSubstitution
open GeneralDeclarationPatterns GeneralNominalInspection
open GeneralNominalHeadMatchMass GeneralPatternGroundSubstitution
open GeneralNominalClosedPatternNormal

mutual
  theorem subst_covered (pattern : Pattern) (complete : covered pattern = true)
      (capture : Nat → Pattern) (images : ∀ name, covered (capture name) = true) :
      covered (pattern.subst capture) = true := by
    cases pattern with
    | var name => exact images name
    | join => cases complete
    | app key arguments => exact args_subst_covered arguments complete capture images
    | variant tag payload => exact subst_covered payload complete capture images
    | record label payload tail =>
      have parts : covered payload = true ∧ covered tail = true := by simpa only [covered,Bool.and_eq_true] using complete
      exact (Bool.and_eq_true ..).mpr ⟨subst_covered payload parts.1 capture images,subst_covered tail parts.2 capture images⟩
  theorem args_subst_covered (patterns : List Pattern) (complete : coveredArgs patterns = true)
      (capture : Nat → Pattern) (images : ∀ name, covered (capture name) = true) :
      coveredArgs (substArgs capture patterns) = true := by
    cases patterns with
    | nil => rfl
    | cons head tail =>
      have parts : covered head = true ∧ coveredArgs tail = true := by simpa only [coveredArgs,Bool.and_eq_true] using complete
      exact (Bool.and_eq_true ..).mpr ⟨subst_covered head parts.1 capture images,args_subst_covered tail parts.2 capture images⟩
end

theorem variant_query (payload : Pattern) (complete : covered payload = true) :
    translate constructors interpretation (.variant tag payload) =
      .node (.variant tag) [translate constructors interpretation payload] := by
  simp only [translate]
  split
  · rename_i names found
    obtain ⟨name,rfl,rfl⟩ := covered_plain_names payload complete found
    simp only [translate]
  · rfl

def fill (capture : Nat → Query) : Query → Query
  | .variables [name] => capture name
  | .variables names => .variables names
  | .scalar base => .scalar base
  | .deferred source => .deferred source
  | .node shape children => .node shape (children.map (fill capture))
  | .nominal name children => .nominal name (children.map (fill capture))

theorem zip_fill (labels : List Nat) (children : List Query) (capture : Nat → Query) :
    (labels.zip children).map (fun entry => (entry.1,fill capture entry.2)) = labels.zip (children.map (fill capture)) := by
  induction labels generalizing children with
  | nil => simp
  | cons head tail ih => cases children <;> simp [ih]

theorem sorted_fill (label : Nat) (payload : Query) (labels : List Nat) (children : List Query) (capture : Nat → Query) :
    fill capture (.node (.record
      ((((label,payload) :: labels.zip children).mergeSort (fun first last => first.1 ≤ last.1)).map Prod.fst))
      ((((label,payload) :: labels.zip children).mergeSort (fun first last => first.1 ≤ last.1)).map Prod.snd)) =
    .node (.record
      ((((label,fill capture payload) :: labels.zip (children.map (fill capture))).mergeSort (fun first last => first.1 ≤ last.1)).map Prod.fst))
      ((((label,fill capture payload) :: labels.zip (children.map (fill capture))).mergeSort (fun first last => first.1 ≤ last.1)).map Prod.snd) := by
  have sorted := List.map_mergeSort (l := (label,payload) :: labels.zip children)
    (f := fun entry => (entry.1,fill capture entry.2))
    (r := fun first last => first.1 ≤ last.1) (s := fun first last => first.1 ≤ last.1)
    (fun _ _ _ _ => rfl)
  simp only [List.map_cons,zip_fill] at sorted
  rw [← sorted]
  simp only [fill,List.map_map,Function.comp_def]

theorem record_complete (label : Nat) (payload : Query) (labels : List Nat) (children : List Query)
    (length : children.length = labels.length)
    (complete : Complete (.node (.record
      ((((label,payload) :: labels.zip children).mergeSort (fun first last => first.1 ≤ last.1)).map Prod.fst))
      ((((label,payload) :: labels.zip children).mergeSort (fun first last => first.1 ≤ last.1)).map Prod.snd))) :
    Complete payload ∧ Complete (.node (.record labels) children) := by
  simp only [Complete] at complete ⊢
  have field (entry : Nat × Query) (member : entry ∈ (label,payload) :: labels.zip children) : Complete entry.2 :=
    complete entry.2 (List.mem_map.mpr ⟨entry,List.mem_mergeSort.mpr member,rfl⟩)
  refine ⟨field _ (List.mem_cons_self ..),?_⟩
  intro child member
  rw [← List.map_snd_zip (Nat.le_of_eq length)] at member
  obtain ⟨entry,present,rfl⟩ := List.mem_map.mp member
  exact field entry (List.mem_cons_of_mem _ present)

theorem subst_length (capture : Nat → Pattern) (patterns : List Pattern) :
    (substArgs capture patterns).length = patterns.length := by
  induction patterns <;> simp_all [substArgs]

mutual
  theorem translate_substitution (pattern : Pattern) (covered : GeneralDeclarationPatterns.covered pattern = true)
      (complete : Complete (translate constructors interpretation pattern))
      (capture : Nat → Pattern) (images : ∀ name, GeneralDeclarationPatterns.covered (capture name) = true) :
      translate constructors interpretation (pattern.subst capture) =
        fill (fun name => translate constructors interpretation (capture name)) (translate constructors interpretation pattern) := by
    cases pattern with
    | var name => simp only [Pattern.subst,translate,fill]
    | join => cases covered
    | variant tag payload =>
      rw [variant_query payload covered] at complete ⊢
      simp only [Complete] at complete
      simp only [Pattern.subst,variant_query (payload.subst capture) (subst_covered payload covered capture images),
        fill,List.map_cons,List.map_nil]
      rw [translate_substitution payload covered (complete _ (List.mem_singleton_self _)) capture images]
    | app key arguments =>
      rw [translate.eq_def] at complete
      dsimp only at complete
      split at complete
      · rename_i base primitive
        have evaluated : translate constructors interpretation (.app key []) = .scalar base := by
          rw [translate.eq_def]; simp only [primitive]
        simp only [Pattern.subst,substArgs,evaluated,fill]
      · rename_i primitive
        simp only [Pattern.subst,substArgs,translate,primitive,fill,List.map_nil]
      · rename_i primitive
        simp only [Pattern.subst,substArgs,translate,primitive,fill,List.map_nil]
      · rename_i first last primitive
        have parts : GeneralDeclarationPatterns.covered first = true ∧ GeneralDeclarationPatterns.covered last = true := by
          simpa only [GeneralDeclarationPatterns.covered,coveredArgs,Bool.and_eq_true,and_true] using covered
        simp only [Complete] at complete
        have one := translate_substitution first parts.1 (complete _ (List.mem_cons_self ..)) capture images
        have two := translate_substitution last parts.2 (complete _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))) capture images
        simp only [Pattern.subst,substArgs,translate,primitive,fill,List.map_cons,List.map_nil,one,two]
      · split at complete
        · rename_i declaration recorded
          split at complete
          · rename_i accepted
            have inv : interpretation.invariantNominal key = true := by
              simpa only [Bool.and_eq_true] using (show interpretation.invariantNominal key = true from
                ((Bool.and_eq_true ..).mp ((Bool.and_eq_true ..).mp accepted).1).1)
            have primitive := interpretation.disjoint key inv
            have parts := translate_substitutions _ covered
              (fun pattern member => (show ∀ child ∈ _, Complete child from by simpa only [Complete] using complete)
                _ (List.mem_map.mpr ⟨⟨pattern,member⟩,List.mem_attach ..,rfl⟩)) capture images
            simp only [Pattern.subst,translate,recorded,accepted,ite_true,fill,
              List.map_map,Function.comp_def,List.attach_map_val]
            rw [translate.eq_def]
            simp only [primitive,recorded,subst_length,accepted,ite_true]
            simpa only [List.map_map,Function.comp_def,List.attach_map_val] using congrArg (Query.nominal declaration.name) parts
          · simp only [Complete] at complete
        · simp only [Complete] at complete
    | record label payload tail =>
      have parts : GeneralDeclarationPatterns.covered payload = true ∧ GeneralDeclarationPatterns.covered tail = true := by
        simpa only [GeneralDeclarationPatterns.covered,Bool.and_eq_true] using covered
      rw [translate.eq_def] at complete
      dsimp only at complete
      split at complete
      · rename_i labels children tailQuery
        have supported := record_complete label _ labels children (record_length tail tailQuery) complete
        have first := translate_substitution payload parts.1 supported.1 capture images
        have last := translate_substitution tail parts.2 (by rw [tailQuery]; exact supported.2) capture images
        rw [tailQuery] at last
        simpa only [Pattern.subst,translate,tailQuery,last,first,fill] using
          (sorted_fill label (translate constructors interpretation payload) labels children
            (fun name => translate constructors interpretation (capture name))).symm
      · simp only [Complete] at complete
    termination_by sizeOf pattern

  theorem translate_substitutions (patterns : List Pattern) (covered : coveredArgs patterns = true)
      (complete : ∀ pattern ∈ patterns, Complete (translate constructors interpretation pattern))
      (capture : Nat → Pattern) (images : ∀ name, GeneralDeclarationPatterns.covered (capture name) = true) :
      (substArgs capture patterns).map (translate constructors interpretation) =
        (patterns.map (translate constructors interpretation)).map
          (fill (fun name => translate constructors interpretation (capture name))) := by
    cases patterns with
    | nil => rfl
    | cons head tail =>
      have parts : GeneralDeclarationPatterns.covered head = true ∧ coveredArgs tail = true := by
        simpa only [coveredArgs,Bool.and_eq_true] using covered
      simp only [substArgs,List.map_cons,
        translate_substitution head parts.1 (complete head (List.mem_cons_self ..)) capture images,
        translate_substitutions tail parts.2 (fun pattern member => complete pattern (List.mem_cons_of_mem _ member)) capture images]
    termination_by sizeOf patterns
end

end Yulang.GeneralNominalTemplateSubstitution
