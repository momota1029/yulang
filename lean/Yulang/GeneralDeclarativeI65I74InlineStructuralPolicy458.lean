import Yulang.GeneralDeclarativeI65I74ClosedInlineField458
import Yulang.GeneralDeclarativeI65I74InlinePair458
import Yulang.GeneralDeclarativeI65I74InlineNominalPoint458
import Yulang.GeneralDeclarativeI65I74RoutedInlineVariantEntry458

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InlineStructuralPolicy458
open Yulang.GeneralDeclarativeI65
open AuthenticatedHop458 (Policy Wire CycleWire)
open GeneralDeclarativeHead320 (Equation)
open RecordTraversal455.MixedQA (Address)
open VariantInlinePolicy458 (InlineMeaning)

inductive Ticket where
  | older (w : VariantInlinePolicy458.Ticket)
  | pair (w : InlinePair458.Wire)
  | field (w : ClosedInlineField458.FieldWire)
  | nominal (w : InlineNominalPoint458.Wire)

def used : Ticket → Bool
  | .older _ => false
  | _ => true

def recordAt (s : GeneralDeclarativeI65.State) (root : Nat) (row : Equation)
    (addr : Address) (child : Nat) : Prop :=
  ∃ label, addr = .field label ∧ ClosedInlineField458.OriginalInlineField s root row label child

def checkRecord (s : GeneralDeclarativeI65.State) (root : Nat) (row : Equation)
    (addr : Address) (child : Nat) (w : ClosedInlineField458.FieldWire) : Bool :=
  match addr with
  | .field label => ClosedInlineField458.checkInlineField s root row label child w
  | _ => false

theorem record_at_iff_finite_ticket458 (s : GeneralDeclarativeI65.State) (root row addr child) :
    (∃ w, checkRecord s root row addr child w = true) ↔ recordAt s root row addr child := by
  constructor
  · rintro ⟨w,yes⟩
    cases addr <;> try cases yes
    case field label =>
      exact ⟨label,rfl,(ClosedInlineField458.same_authorised_visible_inline_field_iff_finite_wire458 ..).mp ⟨w,yes⟩⟩
  · rintro ⟨label,rfl,auth⟩
    obtain ⟨w,yes⟩ := (ClosedInlineField458.same_authorised_visible_inline_field_iff_finite_wire458 ..).mpr auth
    exact ⟨w,yes⟩

def NewAuthority (s : GeneralDeclarativeI65.State) (root : Nat) (row : Equation)
    (addr : Address) (child : Nat) : Prop :=
  InlinePair458.ChildReceipt s root row addr child ∨
    recordAt s root row addr child ∨ InlineNominalPoint458.NominalReceipt s root row addr child

def allows (s : GeneralDeclarativeI65.State) (root : Nat) (row : Equation)
    (addr : Address) (child : Nat) : Bool → Prop
  | false => ∃ use, VariantInlinePolicy458.allows s root row addr child use
  | true => NewAuthority s root row addr child

def checks (s : GeneralDeclarativeI65.State) (root : Nat) (row : Equation)
    (addr : Address) (child : Nat) : Ticket → Bool
  | .older w => VariantInlinePolicy458.checks s root row addr child w
  | .pair w => InlinePair458.check s root row addr child w
  | .field w => checkRecord s root row addr child w
  | .nominal w => InlineNominalPoint458.check s root row addr child w

theorem reflected_use_is_exact_old_or_actual_new_parent458 (s : GeneralDeclarativeI65.State)
    (root row addr child) (flag : Bool) :
    (∃ w, used w = flag ∧ checks s root row addr child w = true) ↔ allows s root row addr child flag := by
  constructor
  · rintro ⟨w,rfl,ok⟩
    cases w with
    | older w =>
      exact ⟨_,(VariantInlinePolicy458.exact_policy_ticket458 ..).mp ⟨w,rfl,ok⟩⟩
    | pair w =>
      exact Or.inl ((InlinePair458.actual_selected_inline_pair_has_finite_origin_wire458 ..).mp ⟨w,ok⟩)
    | field w => exact Or.inr (.inl ((record_at_iff_finite_ticket458 ..).mp ⟨w,ok⟩))
    | nominal w =>
      exact Or.inr (.inr ((InlineNominalPoint458.inline_point_exact_receipt_is_finite458 ..).mp ⟨w,ok⟩))
  · intro actual
    cases flag with
    | false =>
      obtain ⟨prev,auth⟩ := actual
      obtain ⟨w,_,yes⟩ := (VariantInlinePolicy458.exact_policy_ticket458 ..).mpr auth
      exact ⟨.older w,rfl,yes⟩
    | true =>
      rcases actual with pair|field|nominal
      · obtain ⟨w,yes⟩ :=
          (InlinePair458.actual_selected_inline_pair_has_finite_origin_wire458 ..).mpr pair
        exact ⟨.pair w,rfl,yes⟩
      · obtain ⟨w,yes⟩ := (record_at_iff_finite_ticket458 ..).mpr field
        exact ⟨.field w,rfl,yes⟩
      · obtain ⟨w,yes⟩ :=
          (InlineNominalPoint458.inline_point_exact_receipt_is_finite458 ..).mpr nominal
        exact ⟨.nominal w,rfl,yes⟩

def policy (s : GeneralDeclarativeI65.State) : Policy where
  Token := Ticket
  inline := used
  opens := allows s
  checks := checks s
  reflected := reflected_use_is_exact_old_or_actual_new_parent458 s

def emptyPolicy : Policy where
  Token := Ticket
  inline := used
  opens := fun _ _ _ _ _ => False
  checks := fun _ _ _ _ _ => false
  reflected := by intros; simp

def lift (s : GeneralDeclarativeI65.State) : Wire emptyPolicy → Wire (policy s)
  | .stop => .stop
  | .down w cut rest => .down ⟨w.row,w.alias,w.child,w.author⟩ cut (lift s rest)

def erase (s : GeneralDeclarativeI65.State) : Wire (policy s) → Wire emptyPolicy
  | .stop => .stop
  | .down w cut rest => .down ⟨w.row,w.alias,w.child,w.author⟩ cut (erase s rest)

theorem lift_erase458 (s : GeneralDeclarativeI65.State) (w : Wire (policy s)) : lift s (erase s w) = w := by
  induction w with
  | stop => rfl
  | down field cut rest ih =>
    cases field
    simp [lift,erase,ih]

def liftCycle (s : GeneralDeclarativeI65.State) (w : CycleWire emptyPolicy) :
    CycleWire (policy s) := ⟨lift s w.trail,w.cycle⟩

def eraseCycle (s : GeneralDeclarativeI65.State) (w : CycleWire (policy s)) :
    CycleWire emptyPolicy := ⟨erase s w.trail,w.cycle⟩

theorem lift_erase_cycle458 (s : GeneralDeclarativeI65.State) (w : CycleWire (policy s)) :
    liftCycle s (eraseCycle s w) = w := by
  cases w
  simp [liftCycle,eraseCycle,lift_erase458]

end Yulang.GeneralDeclarativeI65.I72.InlineStructuralPolicy458
