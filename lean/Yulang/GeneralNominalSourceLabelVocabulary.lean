import Yulang.GeneralNominalUniformReportDispatch

/-! A finite source-key vocabulary survives subterm extraction, covered
normalization and shared substitution. The source-syntax inventory uses this
fixed vocabulary, including its list/record bookkeeping markers. -/
namespace Yulang.GeneralNominalSourceLabelVocabulary
open GeneralDeclarationPatterns GeneralNominalSourcePatternParts
open GeneralNominalOriginTerms GeneralNominalRecursiveInspection GeneralNominalSharedEnumeration
open GeneralNominalHoleElimination

inductive Scoped (keys : List Nat) : Pattern → Prop
  | var (name) : Scoped keys (.var name)
  | app : key ∈ keys → (∀ pattern ∈ arguments, Scoped keys pattern) → Scoped keys (.app key arguments)
  | record : key ∈ keys → Scoped keys payload → Scoped keys tail → Scoped keys (.record key payload tail)
  | variant : key ∈ keys → Scoped keys payload → Scoped keys (.variant key payload)
  | join : Scoped keys first → Scoped keys last → Scoped keys (.join first last)

theorem part_scoped (part : Part first last) (scope : Scoped keys first) : Scoped keys last := by
  induction part with
  | refl => exact scope
  | argument member part ih => cases scope with | app present children => exact ih (children _ member)
  | payload part ih => cases scope with | record present payload tail => exact ih payload
  | tail part ih => cases scope with | record present payload tail => exact ih tail
  | variant part ih => cases scope with | variant present payload => exact ih payload
  | first part ih => cases scope with | join first last => exact ih first
  | last part ih => cases scope with | join first last => exact ih last

theorem hide_scoped (scope : Scoped keys pattern) : Scoped keys (hide label pattern) := by
  cases scope with
  | record present payload tail =>
    simp only [hide]
    split
    · exact hide_scoped tail
    · exact .record present payload (hide_scoped tail)
  | var name => exact .var name
  | app present arguments => exact .app present arguments
  | variant present payload => exact .variant present payload
  | join first last => exact .join first last
termination_by sizeOf pattern

mutual
  theorem normalized_scoped (pattern : Pattern) (covered : GeneralDeclarationPatterns.covered pattern = true)
      (scope : Scoped keys pattern) : Scoped keys (normalize pattern) := by
    cases scope with
    | var => exact .var _
    | app present arguments => exact .app present (normalized_args_scoped _ covered arguments)
    | record present payload tail =>
      have pieces := (Bool.and_eq_true ..).mp covered
      exact .record present (normalized_scoped _ pieces.1 payload) (hide_scoped (normalized_scoped _ pieces.2 tail))
    | variant present payload => exact .variant present (normalized_scoped _ covered payload)
    | join => cases covered
  theorem normalized_args_scoped (patterns : List Pattern) (covered : coveredArgs patterns = true)
      (scope : ∀ pattern ∈ patterns, Scoped keys pattern) :
      ∀ pattern ∈ normalizeArgs patterns, Scoped keys pattern := by
    cases patterns with
    | nil => intro pattern member; cases member
    | cons head tail =>
      have pieces := (Bool.and_eq_true ..).mp covered
      intro pattern member
      rcases List.mem_cons.mp member with rfl | member
      · exact normalized_scoped head pieces.1 (scope head (List.mem_cons_self ..))
      · exact normalized_args_scoped tail pieces.2 (fun p mem => scope p (List.mem_cons_of_mem _ mem)) pattern member
end

mutual
  theorem subst_scoped (pattern : Pattern) (scope : Scoped keys pattern)
      (substitution : Nat → Pattern) (images : ∀ name, Scoped keys (substitution name)) :
      Scoped keys (pattern.subst substitution) := by
    cases scope with
    | var name => exact images name
    | app present arguments => exact .app present (args_subst_scoped _ arguments substitution images)
    | record present payload tail => exact .record present (subst_scoped _ payload substitution images) (subst_scoped _ tail substitution images)
    | variant present payload => exact .variant present (subst_scoped _ payload substitution images)
    | join first last => exact .join (subst_scoped _ first substitution images) (subst_scoped _ last substitution images)
  theorem args_subst_scoped (patterns : List Pattern) (scope : ∀ pattern ∈ patterns, Scoped keys pattern)
      (substitution : Nat → Pattern) (images : ∀ name, Scoped keys (substitution name)) :
      ∀ pattern ∈ substArgs substitution patterns, Scoped keys pattern := by
    cases patterns with
    | nil => intro pattern member; cases member
    | cons head tail =>
      intro pattern member
      rcases List.mem_cons.mp member with rfl | member
      · exact subst_scoped head (scope head (List.mem_cons_self ..)) substitution images
      · exact args_subst_scoped tail (fun p mem => scope p (List.mem_cons_of_mem _ mem)) substitution images pattern member
end

theorem normalized_subst_scoped (covered : GeneralDeclarationPatterns.covered pattern = true)
    (scope : Scoped keys pattern) (substitution : Nat → Pattern)
    (images : ∀ name, Scoped keys (substitution name))
    (coveredImages : ∀ name, GeneralDeclarationPatterns.covered (substitution name) = true) :
    Scoped keys (normalize (pattern.subst substitution)) :=
  normalized_scoped _ (GeneralNominalTemplateSubstitution.subst_covered pattern covered substitution coveredImages)
    (subst_scoped pattern scope substitution images)

def tests (keys : List Nat) : List Test :=
  [.scalar .int,.structural .pair] ++ keys.flatMap (fun key =>
    [.nominal key 1,.structural (.record [key,key]),.structural (.variant key)])

private theorem binary (test : Test) (_arityTwo : arity test = 2)
    (children : Fin (arity test) → Expr Nat)
    (member : test ∈ tests keys)
    (one : Bounded remaining (tests keys) first a) (two : Bounded remaining (tests keys) last b)
    (values : ∀ i, children i = if i.val = 0 then a else b) :
    Bounded remaining (tests keys) (max first last + 1) (.node test children) := by
  apply Bounded.node _ _ member
  intro position
  rw [values]
  split
  · exact bounded_mono one (Nat.le_max_left ..)
  · exact bounded_mono two (Nat.le_max_right ..)

private theorem test_member (present : key ∈ keys) :
    Test.nominal key 1 ∈ tests keys ∧ Test.structural (.record [key,key]) ∈ tests keys ∧
      Test.structural (.variant key) ∈ tests keys := by
  have entries : [.nominal key 1,.structural (.record [key,key]),.structural (.variant key)] ⊆ tests keys := by
    intro test member
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨key,present,member⟩)
  exact ⟨entries (by simp),entries (by simp),entries (by simp)⟩

mutual
  theorem encoded_bounded (pattern : Pattern) (scope : Scoped keys pattern)
      (variables : GeneralPatternVariableProvenance.Uses (· ∈ remaining) pattern) :
      ∃ depth, Bounded remaining (tests keys) depth (GeneralNominalPatternInventory.encode pattern) := by
    cases scope with
    | var name => exact ⟨0,.leaf name 0 (variables name (List.mem_singleton_self _))⟩
    | app present arguments =>
      obtain ⟨depth,bounded⟩ := encoded_args_bounded _ arguments variables
      exact ⟨depth+1,.node _ _ (test_member present).1 (fun _ => bounded)⟩
    | record present payload tail =>
      obtain ⟨first,one⟩ := encoded_bounded _ payload (fun n mem => variables n (List.mem_append_left _ mem))
      obtain ⟨last,two⟩ := encoded_bounded _ tail (fun n mem => variables n (List.mem_append_right _ mem))
      exact ⟨_,binary _ rfl _ (test_member present).2.1 one two (fun _ => rfl)⟩
    | variant present payload =>
      obtain ⟨depth,bounded⟩ := encoded_bounded _ payload variables
      exact ⟨depth+1,.node _ _ (test_member present).2.2 (fun _ => bounded)⟩
    | join first last =>
      obtain ⟨first,one⟩ := encoded_bounded _ first (fun n mem => variables n (List.mem_append_left _ mem))
      obtain ⟨last,two⟩ := encoded_bounded _ last (fun n mem => variables n (List.mem_append_right _ mem))
      exact ⟨_,binary _ rfl _ (by simp [tests]) one two (fun _ => rfl)⟩
  theorem encoded_args_bounded (patterns : List Pattern) (scope : ∀ pattern ∈ patterns, Scoped keys pattern)
      (variables : ∀ name ∈ variablesArgs patterns, name ∈ remaining) :
      ∃ depth, Bounded remaining (tests keys) depth (GeneralNominalPatternInventory.encodeList patterns) := by
    cases patterns with
    | nil => exact ⟨1,.node _ _ (by simp [tests]) (fun index => Fin.elim0 index)⟩
    | cons head tail =>
      obtain ⟨first,one⟩ := encoded_bounded head (scope head (List.mem_cons_self ..))
        (fun n mem => variables n (List.mem_append_left _ mem))
      obtain ⟨last,two⟩ := encoded_args_bounded tail (fun p mem => scope p (List.mem_cons_of_mem _ mem))
        (fun n mem => variables n (List.mem_append_right _ mem))
      exact ⟨_,binary _ rfl _ (by simp [tests]) one two (fun _ => rfl)⟩
end


theorem scoped_mono (scope : Scoped first pattern) (included : first ⊆ last) : Scoped last pattern := by
  induction scope with
  | var name => exact .var name
  | app present children ih => exact .app (included present) ih
  | record present payload tail one two => exact .record (included present) one two
  | variant present payload ih => exact .variant (included present) ih
  | join first last one two => exact .join one two

mutual
  def collect : Pattern → List Nat
    | .var _ => []
    | .app key arguments => key :: collectArgs arguments
    | .record key payload tail => key :: (collect payload ++ collect tail)
    | .variant key payload => key :: collect payload
    | .join first last => collect first ++ collect last
  def collectArgs : List Pattern → List Nat
    | [] => []
    | head :: tail => collect head ++ collectArgs tail
end

mutual
  theorem collect_scoped (pattern : Pattern) : Scoped (collect pattern) pattern := by
    cases pattern with
    | var => exact .var _
    | app key arguments =>
      exact .app (List.mem_cons_self ..)
        (fun p mem => scoped_mono (collect_args_scoped arguments p mem) (fun _ h => List.mem_cons_of_mem _ h))
    | record key payload tail =>
      exact .record (List.mem_cons_self ..)
        (scoped_mono (collect_scoped payload) (fun _ h => List.mem_cons_of_mem _ (List.mem_append_left _ h)))
        (scoped_mono (collect_scoped tail) (fun _ h => List.mem_cons_of_mem _ (List.mem_append_right _ h)))
    | variant key payload =>
      exact .variant (List.mem_cons_self ..)
        (scoped_mono (collect_scoped payload) (fun _ h => List.mem_cons_of_mem _ h))
    | join first last =>
      exact .join
        (scoped_mono (collect_scoped first) (List.subset_append_left ..))
        (scoped_mono (collect_scoped last) (List.subset_append_right ..))
  theorem collect_args_scoped (patterns : List Pattern) : ∀ pattern ∈ patterns, Scoped (collectArgs patterns) pattern := by
    cases patterns with
    | nil => intro pattern member; cases member
    | cons head tail =>
      intro pattern member
      rcases List.mem_cons.mp member with equal | member
      · subst pattern
        exact scoped_mono (collect_scoped head) (List.subset_append_left ..)
      · exact scoped_mono (collect_args_scoped tail pattern member) (List.subset_append_right ..)
end

theorem part_uses (part : Part first last) (known : GeneralPatternVariableProvenance.Uses allowed first) :
    GeneralPatternVariableProvenance.Uses allowed last := by
  induction part with
  | refl => exact known
  | argument member part ih =>
    apply ih
    intro name present
    exact known name (GeneralNominalCanonicalTemplates.argument_variables _ _ member present)
  | payload part ih | first part ih => exact ih (fun n mem => known n (List.mem_append_left _ mem))
  | tail part ih | last part ih => exact ih (fun n mem => known n (List.mem_append_right _ mem))
  | variant part ih => exact ih known

def Allowed (keys remaining : List Nat) (pattern : Pattern) : Prop :=
  Scoped keys pattern ∧ GeneralPatternVariableProvenance.Uses (· ∈ remaining) pattern

theorem allowed_part (part : Part first last) (known : Allowed keys remaining first) : Allowed keys remaining last :=
  ⟨part_scoped part known.1,part_uses part known.2⟩

theorem bounded_closed (bounded : Bounded remaining vocabulary depth term) : Closed remaining term := by
  induction bounded with
  | leaf name depth present => intro n mem; cases List.mem_singleton.mp mem; exact present
  | node test children member bounded ih =>
    intro n mem
    obtain ⟨parts,present,member⟩ := List.mem_flatten.mp mem
    obtain ⟨position,rfl⟩ := List.mem_ofFn.mp present
    exact ih position n member

/-- The replacement code's finite bound is extracted from its source scope
and surviving variables. No separate numerical growth premise is needed. -/
theorem replacement_trace (inventory : Inventory) (present : hole ∈ inventory.holes)
    (allowed : Allowed keys (inventory.holes.erase hole) value) :
    ∃ extra, Trace (tests keys) (fun _ => extra) inventory
      (eliminate inventory hole (GeneralNominalPatternInventory.encode value) extra) 1 := by
  obtain ⟨extra,bounded⟩ := encoded_bounded value allowed.1 allowed.2
  exact ⟨extra,.next hole _ present (bounded_closed bounded) bounded (.refl _)⟩

/-- Once a finite starting syntax forest and its hole scope are provided,
every capture extracted from the complete two-endpoint report stays in that
same finite source-key vocabulary. -/
theorem scoped_report_dispatch {models : GeneralNominalCommonBridge.Assignment → Prop}
    (state : GeneralNominalState.State)
    {queryScope : GeneralNominalInspection.Query → Prop}
    (queryChildren : ∀ parent child, child ∈ GeneralNominalSourcePatternParts.queryChildren parent → queryScope parent → queryScope child)
    (inhabited : ∃ model, models model)
    (valid : ∀ model, models model → GeneralNominalState.Models state model)
    (queries : List GeneralNominalInspection.Query) (bounds : List (GeneralNominalInspection.Bounds state))
    (origins : Nat → Option Origin) (offset : Nat) (terms : List (Expr Nat))
    (tracked : ∀ query ∈ queries, queryScope query)
    (finished : Finished (inspectMany state queries bounds origins offset))
    (known : GeneralNominalUniformInspectionInputs.InputsAt models values state origins offset bounds terms)
    (sources : ∀ term ∈ terms, ∃ pattern,
      GeneralNominalUniformReportDispatch.Sourced context remaining (Allowed keys remaining) pattern term) :
    GeneralNominalUniformReportDispatch.Captures context remaining (Allowed keys remaining) models values
      (inspectMany state queries bounds origins offset) ∨
    ∃ hole ∈ remaining, GeneralNominalUniformReportDispatch.Exposed models values queryScope
      (inspectMany state queries bounds origins offset) hole :=
  GeneralNominalUniformReportDispatch.many_dispatch state inhabited valid (fun _ _ => allowed_part) queryChildren
    queries bounds origins offset terms tracked finished known sources

end Yulang.GeneralNominalSourceLabelVocabulary
