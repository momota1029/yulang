import Yulang.GeneralNominalSourcePatternParts

/-! A closed canonical translated pattern is stable under normalization.
This lets finite projections reuse source syntax, including record payloads. -/
namespace Yulang.GeneralNominalClosedPatternNormal
open GeneralDeclarationPatterns GeneralNominalInspection
open GeneralNominalOriginTerms GeneralNominalCompoundReadback
open GeneralNominalReadbackFunctionality

def ClosedQuery : Query → Prop
  | .scalar _ => True
  | .node shape children =>
      (match shape with | .record labels => labels.Nodup | _ => True) ∧
      children.length = shape.arity ∧ ∀ child ∈ children, ClosedQuery child
  | .nominal _ children => ∀ child ∈ children, ClosedQuery child
  | _ => False

theorem quote_closed (term : Expr Nat) (closed : term.leaves = []) (canonical : Canonical term) :
    ClosedQuery (quote term) := by
  induction term with
  | leaf name => simp [Expr.leaves] at closed
  | node test children ih =>
    have parts (index : Fin (arity test)) : ClosedQuery (quote (children index)) := by
      apply ih index _ (canonical.2 index)
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro name member
      have parent : name ∈ (Expr.node test children).leaves := by
        simp only [Expr.leaves,List.mem_flatten,List.mem_ofFn]
        exact ⟨_,⟨index,rfl⟩,member⟩
      rw [closed] at parent
      cases parent
    cases test with
    | scalar base => simp only [quote,ClosedQuery]
    | nominal name count =>
      simp only [quote,ClosedQuery]
      intro child member
      obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
      exact parts index
    | structural shape =>
      simp only [quote]
      rw [ClosedQuery.eq_def]
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
    (known : ClosedQuery (.node (.record
      ((((label,payload) :: labels.zip children).mergeSort (fun first last => first.1 ≤ last.1)).map Prod.fst))
      ((((label,payload) :: labels.zip children).mergeSort (fun first last => first.1 ≤ last.1)).map Prod.snd))) :
    ClosedQuery payload ∧ ClosedQuery (.node (.record labels) children) ∧ label ∉ labels := by
  simp only [ClosedQuery] at known ⊢
  have nodup := (List.Perm.nodup_iff (List.Perm.map Prod.fst (List.mergeSort_perm
    ((label,payload) :: labels.zip children) (fun first last => first.1 ≤ last.1)))).mp known.1
  have nodup : (label :: labels).Nodup := by
    simpa only [List.map_cons,List.map_fst_zip (Nat.le_of_eq length.symm)] using nodup
  have field (entry : Nat × Query) (member : entry ∈ (label,payload) :: labels.zip children) : ClosedQuery entry.2 :=
    known.2.2 entry.2 (List.mem_map.mpr ⟨entry,List.mem_mergeSort.mpr member,rfl⟩)
  refine ⟨field _ (List.mem_cons_self ..),⟨(List.nodup_cons.mp nodup).2,length,?_⟩,(List.nodup_cons.mp nodup).1⟩
  intro child member
  have mapped : children = (labels.zip children).map Prod.snd := (List.map_snd_zip (Nat.le_of_eq length)).symm
  rw [mapped] at member
  obtain ⟨entry,present,equal⟩ := List.mem_map.mp member
  exact equal ▸ field entry (List.mem_cons_of_mem _ present)

mutual
  theorem translated_normal (pattern : Pattern) (known : ClosedQuery (translate constructors interpretation pattern)) :
      normalize pattern = pattern := by
    cases pattern with
    | var => rfl
    | join => simp only [translate,ClosedQuery] at known
    | variant tag payload =>
      simp only [translate,ClosedQuery] at known
      have child := known.2.2 _ (List.mem_singleton_self _)
      split at child
      · simp only [ClosedQuery] at child
      · exact congrArg (Pattern.variant tag) (translated_normal payload child)
    | app key arguments =>
      rw [translate.eq_def] at known
      dsimp only at known
      split at known
      · rfl
      · rfl
      · rfl
      · simp only [ClosedQuery] at known
        simp only [normalize,normalizeArgs]
        have first := translated_normal _ (known.2.2 _ (List.mem_cons_self ..))
        have last := translated_normal _ (known.2.2 _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
        rw [first,last]
      · split at known
        · split at known
          · simp only [ClosedQuery] at known
            apply congrArg (Pattern.app key)
            apply args_normal (constructors := constructors) (interpretation := interpretation)
            intro argument member
            exact known _ (List.mem_map.mpr ⟨⟨argument,member⟩,List.mem_attach ..,rfl⟩)
          · simp only [ClosedQuery] at known
        · simp only [ClosedQuery] at known
    | record label payload tail =>
      simp only [translate] at known
      split at known
      · rename_i labels children tailQuery
        have split := sorted_fields label _ labels children (record_length tail tailQuery) known
        have payloadNormal := translated_normal payload split.1
        have tailNormal := translated_normal tail (by rw [tailQuery]; exact split.2.1)
        simp only [normalize,payloadNormal,tailNormal,hide_absent tail tailQuery split.2.2]
      · simp only [ClosedQuery] at known
    termination_by sizeOf pattern

  theorem args_normal (patterns : List Pattern)
      (known : ∀ pattern ∈ patterns, ClosedQuery (translate constructors interpretation pattern)) :
      normalizeArgs patterns = patterns := by
    cases patterns with
    | nil => rfl
    | cons head tail =>
      simp only [normalizeArgs,translated_normal head (known head (List.mem_cons_self ..)),
        args_normal tail (fun pattern member => known pattern (List.mem_cons_of_mem head member))]
    termination_by sizeOf patterns
end

theorem followed_canonical (path : GeneralNominalFiniteMeaning.Follows root term endpoint part)
    (canonical : Canonical term) : Canonical part := by
  induction path with
  | root => exact canonical
  | child test children index prior ih => exact ih.2 index

theorem closed_reification (path : GeneralNominalFiniteMeaning.Follows root term endpoint part)
    (known : GeneralNominalGroundAccessibility.ClosedTerm context pattern term) :
    ∃ source, GeneralNominalSourcePatternParts.Part (normalize pattern) source ∧
      normalize source = source ∧ GeneralNominalGroundAccessibility.ClosedTerm context source part := by
  obtain ⟨source,member,translated⟩ := GeneralNominalSourcePatternParts.followed_source path known.1 known.2.1
  have closed := GeneralNominalFiniteMeaning.followed_closed path known.2.1
  have canonical := followed_canonical path known.2.2
  have normal := translated_normal source (by rw [translated]; exact quote_closed part closed canonical)
  exact ⟨source,member,normal,by rw [GeneralNominalGroundAccessibility.ClosedTerm,normal]; exact ⟨translated,closed,canonical⟩⟩

end Yulang.GeneralNominalClosedPatternNormal
