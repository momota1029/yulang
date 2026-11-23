import Yulang.GeneralDeclarativeI65Capture366

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open Core.PresenceGeneration (TyTerm RowTerm)
open CommonRecursiveNominalIntervals (Endpoint Bounds Argument childContext effectiveParameter)
open CommonDeclaredNominalInspection (Parameter)
open GeneralDeclarativeWitnessConstructorModes357 (Use)
open GeneralDeclarativeWitnessSparseIntervals357 (names)
open GeneralDeclarativeWitnessModeCoverage357 (Covers)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeWhere319 (Capture)
open CommonNominalFullCarrier (Equivalent)

inductive Binding where
  | value (binder : Nat) (lo hi : TyTerm Nat)
  | row (binder : Nat) (lo hi : RowTerm Nat)

def Binding.Source (s : State) (capture : Nat → Capture) : Binding → Prop
  | .value n l h => ValueBind s (capture n) l h
  | .row n l h => RowBind s (capture n) l h

def Binding.Denotes (capture : Nat → Capture) (m : Model) : Binding → Prop
  | .value n l h =>
    Equivalent (valueAt m l) (m.assignment (capture n).lower).1 ∧
    Equivalent (valueAt m h) (m.assignment (capture n).upper).1
  | .row n l h =>
    (Common.rowLe (rowAt m l) (m.assignment (capture n).lower).2 ∧
     Common.rowLe (m.assignment (capture n).lower).2 (rowAt m l)) ∧
    (Common.rowLe (rowAt m h) (m.assignment (capture n).upper).2 ∧
     Common.rowLe (m.assignment (capture n).upper).2 (rowAt m h))

theorem Binding.source_sound {s : State} {capture : Nat → Capture} {leaf : Binding}
    (read : Binding.Source s capture leaf) (m : Model) (fit : Fits s m) :
    Binding.Denotes capture m leaf := by
  cases leaf with
  | value n l h => exact value_binding_sound read m fit
  | row n l h => exact row_binding_sound read m fit

/- Model-free direct authored native-pattern projection. Invariant
   positions keep both complete original bound pairs. A route is not
   a decision procedure for whether those bounds permit some other
   allowed shared bound in the language. Unused positions supply
   author/kind syntax but emit no capture. -/
mutual
inductive DeepRead (s : State) (capture : Nat → Capture) :
    Bool → Pattern → Endpoint Nat → Endpoint Nat → List Binding → Type where
  | bind : ValueBind s (capture n) l h →
      DeepRead s capture context (.var n) (.ordinary l) (.ordinary h) [.value n l h]
  | nominal {key : Nat} {ps : List Pattern} {params : List Parameter}
      (use : Use s.current.environment key ps.length) :
      names use.mode ps.length = some params →
      s.modes[key]? = some params →
      DeepArguments s capture context params ps before after found →
      DeepRead s capture context (.app key ps) (.nominal key before) (.nominal key after) found

inductive DeepArguments (s : State) (capture : Nat → Capture) :
    Bool → List Parameter → List Pattern → List (Argument Nat) → List (Argument Nat) → List Binding → Type where
  | nil : DeepArguments s capture context [] [] [] [] []
  | cons :
      DeepArgument s capture (childContext context parameter) (effectiveParameter context parameter)
        pat a b current →
      DeepArguments s capture context parameters pats as bs later →
      DeepArguments s capture context (parameter::parameters) (pat::pats) (a::as) (b::bs) (current ++ later)

inductive DeepArgument (s : State) (capture : Nat → Capture) :
    Bool → Parameter → Pattern → Argument Nat → Argument Nat → List Binding → Type where
  | covariantValue : DeepRead s capture context pat a b found →
      DeepArgument s capture context ⟨.value,.covariant⟩ pat (.inl (.point a)) (.inl (.point b)) found
  | contravariantValue : DeepRead s capture context pat b a found →
      DeepArgument s capture context ⟨.value,.contravariant⟩ pat (.inl (.point a)) (.inl (.point b)) found
  | invariantValue {a b : Bounds (Endpoint Nat)} :
      DeepRead s capture context pat a.lower a.upper left →
      DeepRead s capture context pat b.lower b.upper right →
      DeepArgument s capture context ⟨.value,.invariant⟩ pat (.inl a) (.inl b) (left ++ right)
  | unusedValue {a b : Bounds (Endpoint Nat)} : Covers s.current.environment pat →
      DeepArgument s capture context ⟨.value,.unused⟩ pat (.inl a) (.inl b) []
  | covariantRow {a b : RowTerm Nat} : RowBind s (capture n) a b →
      DeepArgument s capture context ⟨.row,.covariant⟩ (.var n) (.inr (.point a)) (.inr (.point b)) [.row n a b]
  | contravariantRow {a b : RowTerm Nat} : RowBind s (capture n) b a →
      DeepArgument s capture context ⟨.row,.contravariant⟩ (.var n) (.inr (.point a)) (.inr (.point b)) [.row n b a]
  | invariantRow {a b : Bounds (RowTerm Nat)} :
      RowBind s (capture n) a.lower a.upper → RowBind s (capture n) b.lower b.upper →
      DeepArgument s capture context ⟨.row,.invariant⟩ (.var n) (.inr a) (.inr b)
        [.row n a.lower a.upper,.row n b.lower b.upper]
  | unusedRow {a b : Bounds (RowTerm Nat)} : Covers s.current.environment pat →
      DeepArgument s capture context ⟨.row,.unused⟩ pat (.inr a) (.inr b) []
end

private theorem all_append {α : Type} {p : α → Prop} {as bs : List α}
    (a : ∀ x ∈ as,p x) (b : ∀ x ∈ bs,p x) : ∀ x ∈ as ++ bs,p x :=
  fun x h => (List.mem_append.mp h).elim (a x) (b x)

theorem deep_reads_retain_all_sources {s : State} {capture : Nat → Capture}
    {context : Bool} {p : Pattern} {a b : Endpoint Nat} {found : List Binding}
    (read : DeepRead s capture context p a b found) : ∀ leaf ∈ found, Binding.Source s capture leaf := by
  exact DeepRead.rec
    (motive_1 := fun _ _ _ _ found _ => ∀ leaf ∈ found,Binding.Source s capture leaf)
    (motive_2 := fun _ _ _ _ _ found _ => ∀ leaf ∈ found,Binding.Source s capture leaf)
    (motive_3 := fun _ _ _ _ _ found _ => ∀ leaf ∈ found,Binding.Source s capture leaf)
    (fun proof _ h => by cases List.mem_singleton.mp h; exact proof)
    (fun _ _ _ _ body => body)
    (fun _ h => by cases h)
    (fun _ _ h t => all_append h t)
    (fun _ h => h)
    (fun _ h => h)
    (fun _ _ a b => all_append a b)
    (fun _ _ h => by cases h)
    (fun proof _ h => by cases List.mem_singleton.mp h; exact proof)
    (fun proof _ h => by cases List.mem_singleton.mp h; exact proof)
    (fun a b _ h => by
      rcases List.mem_cons.mp h with first|rest
      · cases first; exact a
      · cases List.mem_singleton.mp rest; exact b)
    (fun _ _ h => by cases h)
    read

theorem deep_binding_means_same_model {s : State} {capture : Nat → Capture}
    {context : Bool} {p : Pattern} {a b : Endpoint Nat} {found : List Binding}
    (read : DeepRead s capture context p a b found)
    (m : Model) (fit : Fits s m) :
    ∀ leaf ∈ found, Binding.Denotes capture m leaf :=
  fun leaf present => Binding.source_sound (deep_reads_retain_all_sources read leaf present) m fit

end Yulang.GeneralDeclarativeI65
