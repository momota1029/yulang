import Yulang.GeneralNominalIndexedHoleReadback
import Yulang.GeneralNominalGroundHeadMatching

/-! Source-key-preserving labels with opaque leaves. Record normalization,
canonical sorting, and template filling do not require closed leaf values. -/
namespace Yulang.GeneralNominalOpenPatternLabels
open GeneralDeclarationPatterns GeneralNominalInspection
open GeneralNominalOriginTerms GeneralNominalCompoundReadback
open GeneralNominalReadbackFunctionality GeneralNominalHeadMatchMass
open GeneralNominalTemplateSubstitution GeneralNominalClosedSubstitution

def OpenQuery : Query → Prop
  | .scalar _ => True
  | .node shape children =>
      (match shape with | .record labels => labels.Nodup | _ => True) ∧
      children.length = shape.arity ∧ ∀ child ∈ children, OpenQuery child
  | .nominal _ children => ∀ child ∈ children, OpenQuery child
  | .variables [_name] => True
  | _ => False

theorem quote_open (term : Expr Nat) (canonical : Canonical term) : OpenQuery (quote term) := by
  induction term with
  | leaf name => simp only [quote,OpenQuery]
  | node test children ih =>
    have parts (index : Fin (arity test)) : OpenQuery (quote (children index)) := ih index (canonical.2 index)
    cases test with
    | scalar base => simp only [quote,OpenQuery]
    | nominal name count =>
      simp only [quote,OpenQuery]
      intro child member
      obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
      exact parts index
    | structural shape =>
      simp only [quote]
      rw [OpenQuery.eq_def]
      dsimp only
      refine ⟨?_,List.length_ofFn ..,?_⟩
      · cases shape with
        | record labels => exact canonical.1.imp (fun less => Nat.ne_of_lt less)
        | pair | variant | exactEmpty => trivial
      · intro child member
        obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
        exact parts index

theorem record_length (pattern : Pattern)
    (translated : translate constructors interpretation pattern = .node (.record labels) children) :
    children.length = labels.length := by
  cases pattern with
  | var | variant | join => simp only [translate] at translated; cases translated
  | record label payload tail =>
    simp only [translate] at translated
    split at translated
    · cases translated
      simp only [List.length_map]
    · cases translated
  | app key arguments =>
    rw [translate.eq_def] at translated
    dsimp only at translated
    split at translated
    · cases translated
    · cases translated; rfl
    · cases translated
    · cases translated
    · split at translated
      · split at translated <;> cases translated
      · cases translated

theorem hide_absent (pattern : Pattern)
    (translated : translate constructors interpretation pattern = .node (.record labels) children)
    (absent : label ∉ labels) : hide label pattern = pattern := by
  cases pattern with
  | var | variant | join | app => rfl
  | record key payload tail =>
    simp only [translate] at translated
    split at translated
    · rename_i names queries tailQuery
      have length := record_length tail tailQuery
      cases translated
      have absentFields : label ∉ (key :: names) := by
        intro member
        have mapped : key :: names = ((key,translate constructors interpretation payload) :: names.zip queries).map Prod.fst := by
          simp only [List.map_cons,List.map_fst_zip (Nat.le_of_eq length.symm)]
        rw [mapped] at member
        obtain ⟨field,present,equal⟩ := List.mem_map.mp member
        exact absent (List.mem_map.mpr ⟨field,List.mem_mergeSort.mpr present,equal⟩)
      have different : label ≠ key := by intro equal; exact absentFields (by simp [equal])
      have tailAbsent : label ∉ names := fun member => absentFields (List.mem_cons_of_mem _ member)
      simp only [hide,different,ite_false,hide_absent tail tailQuery tailAbsent]
    · cases translated

theorem sorted_fields (label : Nat) (payload : Query) (labels : List Nat) (children : List Query)
    (length : children.length = labels.length)
    (known : OpenQuery (.node (.record
      ((((label,payload) :: labels.zip children).mergeSort (fun first last => first.1 ≤ last.1)).map Prod.fst))
      ((((label,payload) :: labels.zip children).mergeSort (fun first last => first.1 ≤ last.1)).map Prod.snd))) :
    OpenQuery payload ∧ OpenQuery (.node (.record labels) children) ∧ label ∉ labels := by
  simp only [OpenQuery] at known ⊢
  have nodup := (List.Perm.nodup_iff (List.Perm.map Prod.fst (List.mergeSort_perm
    ((label,payload) :: labels.zip children) (fun first last => first.1 ≤ last.1)))).mp known.1
  have nodup : (label :: labels).Nodup := by
    simpa only [List.map_cons,List.map_fst_zip (Nat.le_of_eq length.symm)] using nodup
  have field (entry : Nat × Query) (member : entry ∈ (label,payload) :: labels.zip children) : OpenQuery entry.2 :=
    known.2.2 entry.2 (List.mem_map.mpr ⟨entry,List.mem_mergeSort.mpr member,rfl⟩)
  refine ⟨field _ (List.mem_cons_self ..),⟨(List.nodup_cons.mp nodup).2,length,?_⟩,(List.nodup_cons.mp nodup).1⟩
  intro child member
  have mapped : children = (labels.zip children).map Prod.snd := (List.map_snd_zip (Nat.le_of_eq length)).symm
  rw [mapped] at member
  obtain ⟨entry,present,equal⟩ := List.mem_map.mp member
  exact equal ▸ field entry (List.mem_cons_of_mem _ present)

mutual
  theorem translated_normal (pattern : Pattern) (covered : GeneralDeclarationPatterns.covered pattern = true)
      (known : OpenQuery (translate constructors interpretation pattern)) :
      normalize pattern = pattern := by
    cases pattern with
    | var => rfl
    | join => cases covered
    | variant tag payload =>
      rw [GeneralNominalTemplateSubstitution.variant_query payload covered] at known
      simp only [OpenQuery] at known
      exact congrArg (Pattern.variant tag) (translated_normal payload covered
        (known.2.2 _ (List.mem_singleton_self _)))
    | app key arguments =>
      rw [translate.eq_def] at known
      dsimp only at known
      split at known
      · rfl
      · rfl
      · rfl
      · rename_i firstPattern lastPattern primitive
        simp only [OpenQuery] at known
        simp only [normalize,normalizeArgs]
        have parts : GeneralDeclarationPatterns.covered firstPattern = true ∧ GeneralDeclarationPatterns.covered lastPattern = true := by
          simpa only [GeneralDeclarationPatterns.covered,coveredArgs,Bool.and_eq_true,and_true] using covered
        have first := translated_normal _ parts.1 (known.2.2 _ (List.mem_cons_self ..))
        have last := translated_normal _ parts.2 (known.2.2 _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
        rw [first,last]
      · split at known
        · split at known
          · simp only [OpenQuery] at known
            apply congrArg (Pattern.app key)
            apply args_normal (constructors := constructors) (interpretation := interpretation) _ covered
            intro argument member
            exact known _ (List.mem_map.mpr ⟨⟨argument,member⟩,List.mem_attach ..,rfl⟩)
          · simp only [OpenQuery] at known
        · simp only [OpenQuery] at known
    | record label payload tail =>
      simp only [translate] at known
      split at known
      · rename_i labels children tailQuery
        have split := sorted_fields label _ labels children (record_length tail tailQuery) known
        have parts : GeneralDeclarationPatterns.covered payload = true ∧ GeneralDeclarationPatterns.covered tail = true :=
          (Bool.and_eq_true ..).mp covered
        have payloadNormal := translated_normal payload parts.1 split.1
        have tailNormal := translated_normal tail parts.2 (by rw [tailQuery]; exact split.2.1)
        simp only [normalize,payloadNormal,tailNormal,hide_absent tail tailQuery split.2.2]
      · simp only [OpenQuery] at known
    termination_by sizeOf pattern

  theorem args_normal (patterns : List Pattern) (covered : coveredArgs patterns = true)
      (known : ∀ pattern ∈ patterns, OpenQuery (translate constructors interpretation pattern)) :
      normalizeArgs patterns = patterns := by
    cases patterns with
    | nil => rfl
    | cons head tail =>
      have parts : GeneralDeclarationPatterns.covered head = true ∧ coveredArgs tail = true := (Bool.and_eq_true ..).mp covered
      simp only [normalizeArgs,translated_normal head parts.1 (known head (List.mem_cons_self ..)),
        args_normal tail parts.2 (fun pattern member => known pattern (List.mem_cons_of_mem head member))]
    termination_by sizeOf patterns
end


def Label (context : GeneralNominalCandidates.Context) (pattern : Pattern) (term : Expr Nat) : Prop :=
  covered pattern = true ∧ translate context.state.constructors context.interpretation pattern = quote term ∧ Canonical term

theorem label_normal (label : Label context pattern term) : normalize pattern = pattern :=
  translated_normal pattern label.1 (by rw [label.2.1]; exact quote_open term label.2.2)

theorem quote_complete (term : Expr Nat) : Complete (quote term) := by
  induction term with
  | leaf => simp only [quote,Complete]
  | node test children ih =>
    cases test with
    | scalar => simp only [quote,Complete]
    | structural | nominal =>
      simp only [quote,Complete]
      intro child member
      obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
      exact ih index

/-- Filling retains the original constructor keys and variable identities.
The emitter's normalization has no further effect on this supported label. -/
theorem filled_label (label : Label context pattern term) (capture : Nat → Pattern)
    (replacement : Nat → Expr Nat) (images : ∀ name, Label context (capture name) (replacement name)) :
    Label context (normalize (pattern.subst capture)) (term.bind replacement) := by
  have covered := subst_covered pattern label.1 capture (fun name => (images name).1)
  have complete : Complete (translate context.state.constructors context.interpretation pattern) := by
    rw [label.2.1]; exact quote_complete term
  have translated := translate_substitution pattern label.1 complete capture (fun name => (images name).1)
  rw [label.2.1] at translated
  have aligned : (fun name => translate context.state.constructors context.interpretation (capture name)) =
      (fun name => quote (replacement name)) := funext (fun name => (images name).2.1)
  rw [aligned,← quote_bind] at translated
  have canonical := canonical_bind term label.2.2 replacement (fun name _ => (images name).2.2)
  have normal := translated_normal (pattern.subst capture) covered (by rw [translated]; exact quote_open _ canonical)
  rw [normal]
  exact ⟨covered,translated,canonical⟩

def weight (term : Expr Nat) : Nat := weighted (fun _ => 1) (quote term)

mutual
  theorem identity_subst (term : Roles.Term) : term.subst Roles.Term.var = term := by
    cases term with
    | var => rfl
    | app key arguments => exact congrArg (Roles.Term.app key) (identity_args arguments)
  theorem identity_args (terms : List Roles.Term) : Roles.substArgs Roles.Term.var terms = terms := by
    cases terms with
    | nil => rfl
    | cons head tail => simp only [Roles.substArgs,identity_subst head,identity_args tail]
end

theorem label_mass (label : Label context pattern term) :
    GeneralNominalPatersonLineage.mass [pattern] = weight term := by
  have complete : Complete (translate context.state.constructors context.interpretation pattern) := by
    rw [label.2.1]; exact quote_complete term
  have exactMass := translated_count pattern label.1 complete Roles.Term.var
  rw [identity_subst,label.2.1] at exactMass
  simpa only [GeneralNominalPatersonLineage.mass,counted,normalizeArgs,label_normal label,
    encodeArgs,Roles.argsSize,Nat.add_zero,weight,Roles.Term.size] using exactMass

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
  | scalar => simp only [weighted,weight,quote,weighted]; exact Nat.le_refl 1
  | structural shape queries children matched ih =>
    have total := sums_le shape.arity _ _ ih
    cases shape <;>
      simp only [weighted,weight,quote,weighted,List.map_ofFn,Function.comp_def] <;>
      apply Nat.add_le_add_left <;> exact total
  | nominal name count queries children matched ih =>
    simp only [weighted,weight,quote,weighted,List.map_ofFn,Function.comp_def]
    apply Nat.add_le_add_left
    exact sums_le count _ _ ih


theorem matched_mass_eq (matched : Matches relation query term)
    (equal : ∀ name term, relation name term → capture name = weight term) :
    weighted capture query = weight term := by
  induction matched with
  | capture matched => simpa only [weighted,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using equal _ _ matched
  | scalar => simp only [weighted,weight,quote,weighted]
  | structural shape queries children matched ih =>
    have total := congrArg (fun f : Fin shape.arity → Nat => (List.ofFn f).sum) (funext ih)
    cases shape <;>
      simp only [weighted,weight,quote,weighted,List.map_ofFn,Function.comp_def] <;>
      congr 1 <;> exact total
  | nominal name count queries children matched ih =>
    have total := congrArg (fun f : Fin count → Nat => (List.ofFn f).sum) (funext ih)
    simp only [weighted,weight,quote,weighted,List.map_ofFn,Function.comp_def]
    exact congrArg (fun size => 1 + size) total

theorem instantiated_bound (pattern : Pattern) (covered : GeneralDeclarationPatterns.covered pattern = true)
    (complete : Complete (translate context.state.constructors context.interpretation pattern))
    (known : Label context label term)
    (matched : Matches relation (translate context.state.constructors context.interpretation pattern) term)
    (capture : Nat → Pattern)
    (bounded : ∀ name term, relation name term → (normalize (capture name)).encode.size ≤ weight term) :
    GeneralNominalPatersonLineage.mass [pattern.subst capture] ≤ GeneralNominalPatersonLineage.mass [label] := by
  have upper := (GeneralPatternConservativeSubstitution.substitution_bounds pattern covered capture).2
  rw [translated_count pattern covered complete] at upper
  have matched := matched_mass matched bounded
  rw [label_mass known]
  simpa only [GeneralNominalPatersonLineage.mass,counted,normalizeArgs,encodeArgs,Roles.argsSize,Nat.add_zero] using
    Nat.le_trans upper matched

end Yulang.GeneralNominalOpenPatternLabels
