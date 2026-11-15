import Yulang.GeneralDictionaryDefaultModelGlue212

/-! Mode-sensitive expression support. Nominal arguments switch to actual,
including beneath lower/upper equations. No constructor injectivity is used. -/
namespace Yulang.GeneralDictionaryDefaultModeSupport212
open GeneralNominalCenteredHeadMatExpressions GeneralNominalCenteredHeadMatSchemas
open GeneralNominalCenteredHeadMatExtension (sources extend)
open GeneralNominalMaterialization (Mode)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree)
open CommonNominalFullCarrier

mutual
 def reads (resolve : Mode → Nat → Nat) (mode : Mode) : Expr → List Nat
  | .variable name => [resolve mode name]
  | .primitive _ args => readMany resolve mode args
  | .nominal _ args => readMany resolve .actual args
  | .record _ a b | .join a b => reads resolve mode a ++ reads resolve mode b
  | .variant _ a => reads resolve mode a
 def readMany (resolve : Mode → Nat → Nat) (mode : Mode) : List Expr → List Nat
  | [] => []
  | a :: rest => reads resolve mode a ++ readMany resolve mode rest
end

private theorem congr2 (f : α → β → γ) (one : a = b) (two : c = d) : f a c = f b d := by
 cases one; cases two; rfl

mutual
 theorem value_same (resolve : Mode → Nat → Nat) (mode : Mode) (expression : Expr)
     (same : Agree (reads resolve mode expression) first last) :
     value (sources resolve first) mode expression = value (sources resolve last) mode expression := by
  cases expression with
  | «variable» name => exact congrArg Prod.fst (same _ (List.mem_singleton_self _))
  | primitive constructor args => exact congrArg (primitiveValue constructor) (values_same resolve mode args same)
  | nominal name args => exact congrArg (fun args => nominal name (args.map Sum.inl)) (values_same resolve .actual args same)
  | record label a b =>
    exact congr2 (record label)
      (value_same resolve mode a (fun n h => same n (List.mem_append_left _ h)))
      (value_same resolve mode b (fun n h => same n (List.mem_append_right _ h)))
  | variant tag a => exact congrArg (variant tag) (value_same resolve mode a same)
  | join a b =>
    exact congr2 CommonNominalSyntax.Layer.union
      (value_same resolve mode a (fun n h => same n (List.mem_append_left _ h)))
      (value_same resolve mode b (fun n h => same n (List.mem_append_right _ h)))
 theorem values_same (resolve : Mode → Nat → Nat) (mode : Mode) (expressions : List Expr)
     (same : Agree (readMany resolve mode expressions) first last) :
     values (sources resolve first) mode expressions = values (sources resolve last) mode expressions := by
  cases expressions with
  | nil => rfl
  | cons a rest =>
    exact congr2 List.cons
      (value_same resolve mode a (fun n h => same n (List.mem_append_left _ h)))
      (values_same resolve mode rest (fun n h => same n (List.mem_append_right _ h)))
end

variable {schema : Schema} {before : Assignment}
 def Independent (resolve : Mode → Nat → Nat) (equations : List Equation) : Prop :=
  ∀ equation ∈ equations, ∀ name ∈ reads resolve equation.mode equation.expression,
    name ∉ equations.map Equation.target

 theorem extend_holds (unique : (schema.equations.map Equation.target).Nodup)
     (independent : Independent resolve schema.equations) :
     schema.Holds (sources resolve (extend resolve before schema.equations))
       (extend resolve before schema.equations) := by
  intro equation member
  have rhs := value_same resolve equation.mode equation.expression
    (first := extend resolve before schema.equations) (last := before)
    (fun name used => GeneralNominalCenteredHeadMatExtension.extend_outside (independent equation member name used))
  unfold Equation.Holds
  rw [rhs,GeneralNominalCenteredHeadMatExtension.extend_target unique member]
  exact ⟨subtype_refl _,subtype_refl _⟩

/-- Construct equations while retaining the complete corrected total journal.
Freshness is measured against snapshot AND live effects, not only raw Models. -/
 theorem journal_extension (state : GeneralNominalCenteredHeadMatStepJournal.State roles)
     (valid : GeneralNominalCenteredHeadMatStepJournal.Models state before)
     (unique : (schema.equations.map Equation.target).Nodup)
     (independent : Independent resolve schema.equations)
     (fresh : ∀ equation ∈ schema.equations,
       equation.target ∉ GeneralDictionaryDefaultJournalFrame212.journalSources state) :
     ∃ after, GeneralNominalCenteredHeadMatStepJournal.Models state after ∧
       schema.Holds (sources resolve after) after ∧
       Agree (GeneralDictionaryDefaultJournalFrame212.journalSources state) before after := by
  have same : Agree (GeneralDictionaryDefaultJournalFrame212.journalSources state) before
      (extend resolve before schema.equations) := by
    intro name member
    symm
    apply GeneralNominalCenteredHeadMatExtension.extend_outside
    rintro present
    obtain ⟨equation,within,rfl⟩ := List.mem_map.mp present
    exact fresh equation within member
  exact ⟨extend resolve before schema.equations,
    (GeneralDictionaryDefaultJournalFrame212.models_iff state same).mp valid,
    extend_holds unique independent,same⟩

 theorem nominal_lower_reads (resolve : Mode → Nat → Nat) :
     reads resolve .lower (.nominal tag [.variable name]) = [resolve .actual name] := rfl
 theorem primitive_lower_reads (resolve : Mode → Nat → Nat) :
     reads resolve .lower (.primitive constructor [.variable name]) = [resolve .lower name] := rfl

end Yulang.GeneralDictionaryDefaultModeSupport212
