import Yulang.CommonEffectMixedDeclarations

/-!
Finite declaration admission checks both the captured name table and each
operation-local sort. A captured source name must exist at its original
resolved position and have the kind expected by the signature occurrence.
The independent judgments below describe the ordinary kind rules; they do
not mention the Boolean checker or generated effect constraints.
-/
namespace Yulang.CommonEffectMixedKinds
open Core.PresenceGeneration (TyTerm RowTerm)
open CommonEffectKindedFormula (Names)
open CommonEffectMixedDeclarations (Declaration Declarations)

inductive Kind where
  | value
  | row
  deriving DecidableEq, Repr

def nameKind (captured : List Kind) : Nat ⊕ Names types rows → Option Kind
  | .inl name => captured[name]?
  | .inr (.inl _) => some .value
  | .inr (.inr _) => some .row

def checkRow (kinds : α → Option Kind) : RowTerm α → Bool
  | .var name => kinds name == some .row
  | .empty => true
  | .join first last => checkRow kinds first && checkRow kinds last

def checkType (kinds : α → Option Kind) : TyTerm α → Bool
  | .var name => kinds name == some .value
  | .base _ | .bottom | .top | .emptyRecord | .exactEmpty => true
  | .union first last | .inter first last | .pair first last | .record _ first last |
      .recordDefault _ first last => checkType kinds first && checkType kinds last
  | .required _ value | .variant _ value => checkType kinds value
  | .arrow input incoming output outgoing =>
      checkType kinds input && checkRow kinds incoming && checkType kinds output && checkRow kinds outgoing

inductive RowKinded (kinds : α → Option Kind) : RowTerm α → Prop where
  | var : kinds name = some .row → RowKinded kinds (.var name)
  | empty : RowKinded kinds .empty
  | join : RowKinded kinds first → RowKinded kinds last → RowKinded kinds (.join first last)

inductive TypeKinded (kinds : α → Option Kind) : TyTerm α → Prop where
  | var : kinds name = some .value → TypeKinded kinds (.var name)
  | base : TypeKinded kinds (.base base)
  | bottom : TypeKinded kinds .bottom
  | top : TypeKinded kinds .top
  | emptyRecord : TypeKinded kinds .emptyRecord
  | exactEmpty : TypeKinded kinds .exactEmpty
  | union : TypeKinded kinds first → TypeKinded kinds last → TypeKinded kinds (.union first last)
  | inter : TypeKinded kinds first → TypeKinded kinds last → TypeKinded kinds (.inter first last)
  | pair : TypeKinded kinds first → TypeKinded kinds last → TypeKinded kinds (.pair first last)
  | record : TypeKinded kinds first → TypeKinded kinds last → TypeKinded kinds (.record label first last)
  | recordDefault : TypeKinded kinds first → TypeKinded kinds last → TypeKinded kinds (.recordDefault label first last)
  | required : TypeKinded kinds value → TypeKinded kinds (.required label value)
  | variant : TypeKinded kinds value → TypeKinded kinds (.variant label value)
  | arrow : TypeKinded kinds input → RowKinded kinds incoming → TypeKinded kinds output →
      RowKinded kinds outgoing → TypeKinded kinds (.arrow input incoming output outgoing)

theorem check_row_exact (kinds : α → Option Kind) (row : RowTerm α) :
    checkRow kinds row = true ↔ RowKinded kinds row := by
  induction row with
  | var name =>
    simp only [checkRow, beq_iff_eq]
    exact ⟨RowKinded.var, fun h => by cases h; assumption⟩
  | empty => exact ⟨fun _ => .empty, fun _ => rfl⟩
  | join first last firstIH lastIH =>
    simp only [checkRow, Bool.and_eq_true, firstIH, lastIH]
    exact ⟨fun ⟨a, b⟩ => .join a b, fun h => by cases h; exact ⟨‹_›, ‹_›⟩⟩

theorem check_type_exact (kinds : α → Option Kind) (value : TyTerm α) :
    checkType kinds value = true ↔ TypeKinded kinds value := by
  induction value with
  | var name =>
    simp only [checkType, beq_iff_eq]
    exact ⟨TypeKinded.var, fun h => by cases h; assumption⟩
  | base base => exact ⟨fun _ => .base, fun _ => rfl⟩
  | bottom => exact ⟨fun _ => .bottom, fun _ => rfl⟩
  | top => exact ⟨fun _ => .top, fun _ => rfl⟩
  | emptyRecord => exact ⟨fun _ => .emptyRecord, fun _ => rfl⟩
  | exactEmpty => exact ⟨fun _ => .exactEmpty, fun _ => rfl⟩
  | union first last firstIH lastIH =>
    simp only [checkType, Bool.and_eq_true, firstIH, lastIH]
    exact ⟨fun ⟨a, b⟩ => .union a b, fun h => by cases h; exact ⟨‹_›, ‹_›⟩⟩
  | inter first last firstIH lastIH =>
    simp only [checkType, Bool.and_eq_true, firstIH, lastIH]
    exact ⟨fun ⟨a, b⟩ => .inter a b, fun h => by cases h; exact ⟨‹_›, ‹_›⟩⟩
  | pair first last firstIH lastIH =>
    simp only [checkType, Bool.and_eq_true, firstIH, lastIH]
    exact ⟨fun ⟨a, b⟩ => .pair a b, fun h => by cases h; exact ⟨‹_›, ‹_›⟩⟩
  | record label first last firstIH lastIH =>
    simp only [checkType, Bool.and_eq_true, firstIH, lastIH]
    exact ⟨fun ⟨a, b⟩ => .record a b, fun h => by cases h; exact ⟨‹_›, ‹_›⟩⟩
  | recordDefault label first last firstIH lastIH =>
    simp only [checkType, Bool.and_eq_true, firstIH, lastIH]
    exact ⟨fun ⟨a, b⟩ => .recordDefault a b, fun h => by cases h; exact ⟨‹_›, ‹_›⟩⟩
  | required label value ih =>
    simp only [checkType, ih]
    exact ⟨TypeKinded.required, fun h => by cases h; assumption⟩
  | variant label value ih =>
    simp only [checkType, ih]
    exact ⟨TypeKinded.variant, fun h => by cases h; assumption⟩
  | arrow input incoming output outgoing inputIH outputIH =>
    simp only [checkType, Bool.and_eq_true, inputIH, outputIH, check_row_exact]
    exact ⟨fun ⟨⟨⟨a, b⟩, c⟩, d⟩ => .arrow a b c d,
      fun h => by cases h; exact ⟨⟨⟨‹_›, ‹_›⟩, ‹_›⟩, ‹_›⟩⟩

def checkDeclaration (captured : List Kind) (declaration : Declaration Nat) : Bool :=
  checkType (nameKind captured) declaration.input && checkType (nameKind captured) declaration.output

def DeclarationKinded (captured : List Kind) (declaration : Declaration Nat) : Prop :=
  TypeKinded (nameKind captured) declaration.input ∧ TypeKinded (nameKind captured) declaration.output

def checkDeclarations (captured : List Kind) (declarations : Declarations Nat) : Bool :=
  declarations.all (checkDeclaration captured)

def DeclarationsKinded (captured : List Kind) (declarations : Declarations Nat) : Prop :=
  ∀ declaration ∈ declarations, DeclarationKinded captured declaration

/-- Every declared occurrence is checked against its original finite captured
table and its own local binders. Missing names and swapped kinds are rejected. -/
theorem check_declarations_exact (captured : List Kind) (declarations : Declarations Nat) :
    checkDeclarations captured declarations = true ↔ DeclarationsKinded captured declarations := by
  simp only [checkDeclarations, List.all_eq_true, checkDeclaration, Bool.and_eq_true,
    check_type_exact, DeclarationsKinded, DeclarationKinded]

end Yulang.CommonEffectMixedKinds
