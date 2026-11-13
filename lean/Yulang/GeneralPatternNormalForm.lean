import Yulang.GeneralNominalTemplateSubstitution

/-! Covered normalization yields recursively stable templates. Record-spine
labels are distinct, even when declaration syntax originally hid fields. -/
namespace Yulang.GeneralPatternNormalForm
open GeneralDeclarationPatterns

def fields : Pattern → List Nat
  | .record label _ tail => label :: fields tail
  | _ => []

def Normal : Pattern → Prop
  | .var _ => True
  | .app _ arguments => ∀ pattern ∈ arguments, Normal pattern
  | .variant _ payload => Normal payload
  | .record label payload tail => Normal payload ∧ Normal tail ∧ label ∉ fields tail
  | .join _ _ => False

theorem fields_hide (label : Nat) (pattern : Pattern) :
    fields (hide label pattern) = (fields pattern).filter (fun key => key != label) := by
  cases pattern with
  | record key payload tail =>
    by_cases same : label = key
    · subst key; simpa [hide,fields] using fields_hide label tail
    · simp [hide,fields,same,Ne.symm same,fields_hide label tail]
  | _ => rfl

theorem hide_normal (label : Nat) (pattern : Pattern) (normal : Normal pattern) : Normal (hide label pattern) := by
  cases pattern with
  | record key payload tail =>
    simp only [Normal] at normal
    by_cases same : label = key
    · simpa only [hide,same,ite_true] using hide_normal label tail normal.2.1
    · simp only [hide,same,ite_false,Normal]
      refine ⟨normal.1,hide_normal label tail normal.2.1,?_⟩
      rw [fields_hide]
      exact fun member => normal.2.2 ((List.mem_filter.mp member).1)
  | _ => exact normal

theorem hide_absent (label : Nat) (pattern : Pattern) (absent : label ∉ fields pattern) : hide label pattern = pattern := by
  cases pattern with
  | record key payload tail =>
    have different : label ≠ key := fun same => absent (by simp [fields,same])
    have tailAbsent : label ∉ fields tail := fun member => absent (List.mem_cons_of_mem _ member)
    simp only [hide,different,ite_false,hide_absent label tail tailAbsent]
  | _ => rfl

mutual
  theorem fixed (pattern : Pattern) (normal : Normal pattern) : normalize pattern = pattern := by
    cases pattern with
    | var => rfl
    | join => simp only [Normal] at normal
    | app key arguments =>
      simp only [Normal] at normal
      exact congrArg (Pattern.app key) (args_fixed arguments normal)
    | variant tag payload =>
      simp only [Normal] at normal
      exact congrArg (Pattern.variant tag) (fixed payload normal)
    | record label payload tail =>
      simp only [Normal] at normal
      simp only [normalize,fixed payload normal.1,fixed tail normal.2.1,hide_absent label tail normal.2.2]
  theorem args_fixed (patterns : List Pattern) (normal : ∀ pattern ∈ patterns, Normal pattern) : normalizeArgs patterns = patterns := by
    cases patterns with
    | nil => rfl
    | cons head tail =>
      simp only [normalizeArgs,fixed head (normal head (List.mem_cons_self ..)),
        args_fixed tail (fun pattern member => normal pattern (List.mem_cons_of_mem _ member))]
end

mutual
  theorem normalized (pattern : Pattern) (complete : covered pattern = true) : Normal (normalize pattern) := by
    cases pattern with
    | var => simp only [normalize,Normal]
    | join => cases complete
    | app key arguments =>
      simp only [normalize,Normal]
      exact args_normalized arguments complete
    | variant tag payload =>
      simp only [normalize,Normal]
      exact normalized payload complete
    | record label payload tail =>
      have parts : covered payload = true ∧ covered tail = true := by simpa only [covered,Bool.and_eq_true] using complete
      simp only [normalize,Normal]
      refine ⟨normalized payload parts.1,hide_normal label _ (normalized tail parts.2),?_⟩
      rw [fields_hide]
      simp
  theorem args_normalized (patterns : List Pattern) (complete : coveredArgs patterns = true) :
      ∀ pattern ∈ normalizeArgs patterns, Normal pattern := by
    cases patterns with
    | nil => intro pattern member; cases member
    | cons head tail =>
      have parts : covered head = true ∧ coveredArgs tail = true := by simpa only [coveredArgs,Bool.and_eq_true] using complete
      intro pattern member
      rcases List.mem_cons.mp member with rfl | member
      · exact normalized head parts.1
      · exact args_normalized tail parts.2 pattern member
end

mutual
  theorem covered_normal (pattern : Pattern) (normal : Normal pattern) : covered pattern = true := by
    cases pattern with
    | var => rfl
    | join => simp only [Normal] at normal
    | app key arguments =>
      simp only [Normal] at normal
      exact covered_args_normal arguments normal
    | variant tag payload =>
      simp only [Normal] at normal
      exact covered_normal payload normal
    | record label payload tail =>
      simp only [Normal] at normal
      simp only [covered,covered_normal payload normal.1,covered_normal tail normal.2.1,Bool.and_self]
  theorem covered_args_normal (patterns : List Pattern) (normal : ∀ pattern ∈ patterns, Normal pattern) : coveredArgs patterns = true := by
    cases patterns with
    | nil => rfl
    | cons head tail =>
      simp only [coveredArgs,covered_normal head (normal head (List.mem_cons_self ..)),
        covered_args_normal tail (fun pattern member => normal pattern (List.mem_cons_of_mem _ member)),Bool.and_self]
end

theorem fields_unique (pattern : Pattern) (normal : Normal pattern) : (fields pattern).Nodup := by
  cases pattern with
  | record label payload tail =>
    simp only [Normal] at normal
    exact List.nodup_cons.mpr ⟨normal.2.2,fields_unique tail normal.2.1⟩
  | _ => exact List.nodup_nil

theorem idempotent_covered (pattern : Pattern) (complete : covered pattern = true) :
    normalize (normalize pattern) = normalize pattern := fixed _ (normalized pattern complete)

end Yulang.GeneralPatternNormalForm
