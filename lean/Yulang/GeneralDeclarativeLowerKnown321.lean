import Yulang.GeneralDeclarativeSupportedReads321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeLowerKnown321
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeBounds319 (Bound)
open GeneralNominalCenteredHeadMatExpressions (Expr)

inductive Tag where
  | primitive (code : GeneralCandidateInspection.Primitive) (arity : Nat)
  | nominal (code arity : Nat)
  | record (label : Nat)
  | variant (label : Nat)

/-- Join is not itself a known constructor: e.g. X ∪ X can normalize to X.
This is the revealed-constructor fragment of normalized observations. -/
def constructorTag : Expr → Option Tag
  | .variable _ | .join _ _ => none
  | .primitive tag args => some (.primitive tag args.length)
  | .nominal tag args => some (.nominal tag args.length)
  | .record label _ _ => some (.record label)
  | .variant label _ => some (.variant label)

inductive Alias (s : State) : Nat → Nat → Prop where
  | bounds : Bound s.normal a b → Bound s.normal b a → Alias s a b
  | forward : (⟨a,.variable b⟩ : Equation) ∈ s.equations → Alias s a b
  | backward : (⟨b,.variable a⟩ : Equation) ∈ s.equations → Alias s a b
  | trans : Alias s a b → Alias s b c → Alias s a c

theorem alias_refl (a : Nat) : Alias s a a := .bounds (.refl a) (.refl a)

theorem alias_symm (h : Alias s a b) : Alias s b a := by
  induction h with
  | bounds h₁ h₂ => exact .bounds h₂ h₁
  | forward h => exact .backward h
  | backward h => exact .forward h
  | trans _ _ i j => exact .trans j i

/-- Use the lower endpoint, not the upper endpoint or an arbitrary witness
inside the interval. A supported alias may convey a constructor already
exposed by the lower endpoint. -/
def Knows (s : State) (name : Nat) (tag : Tag) : Prop :=
  ∃ row : Equation, row ∈ s.equations ∧ Alias s name row.left ∧ constructorTag row.right = some tag

def Ready (p : Supported s completed) (d : Demand) : Prop :=
  ∀ arg ∈ d.arguments, ∃ tag, Knows (restriction p) arg.lower tag

def Delayed (p : Supported s completed) (d : Demand) : Prop :=
  ∃ arg ∈ d.arguments, ∀ tag, ¬Knows (restriction p) arg.lower tag

theorem ready_iff_not_delayed (p : Supported s completed) (d : Demand) :
    Ready p d ↔ ¬Delayed p d := by
  classical
  constructor
  · intro ready
    rintro ⟨arg,there,none⟩
    obtain ⟨tag,visible⟩ := ready arg there
    exact none tag visible
  · intro noDelay arg there
    apply Classical.byContradiction
    intro none
    exact noDelay ⟨arg,there,fun tag knows => none ⟨tag,knows⟩⟩

theorem knows_alias (edge : Alias s name other) (known : Knows s other tag) : Knows s name tag := by
  obtain ⟨row,present,link,shape⟩ := known
  exact ⟨row,present,.trans edge link,shape⟩

theorem knows_row (present : (⟨name,code⟩ : Equation) ∈ s.equations)
    (shape : constructorTag code = some tag) : Knows s name tag :=
  ⟨_,present,alias_refl name,shape⟩

theorem alias_mono {s t : State} (ordinary : s.normal = t.normal) (rows : s.equations ⊆ t.equations)
    (h : Alias s a b) : Alias t a b := by
  induction h with
  | bounds h₁ h₂ => exact .bounds (ordinary ▸ h₁) (ordinary ▸ h₂)
  | forward h => exact .forward (rows h)
  | backward h => exact .backward (rows h)
  | trans _ _ i j => exact .trans i j

theorem knows_mono {s t : State} (ordinary : s.normal = t.normal) (rows : s.equations ⊆ t.equations)
    (h : Knows s name tag) : Knows t name tag := by
  obtain ⟨row,present,link,shape⟩ := h
  exact ⟨row,rows present,alias_mono ordinary rows link,shape⟩

end Yulang.GeneralDeclarativeLowerKnown321
