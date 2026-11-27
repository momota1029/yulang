import Yulang.GeneralDeclarativeI65I74AuthenticatedHop458

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.VariantInlinePolicy458
open Yulang.GeneralDeclarativeI65
open AuthenticatedHop458
open RecordTraversal455 RecordTraversal455.MixedQA
open RoutedNominalPoint456 (nominalOps)
open RoutedNominalMixed456 (MeaningOfOpen)
open InlineVariant458 (OriginalInlineVariant readRawVariant read_raw_variant_exact458)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeGraphRows321 (shapeOf observed structural)
open GeneralDeclarativeK2Graph321 (Shape)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeInspect321 (Inspects)
open GeneralNominalCenteredHeadMatExpressions (Expr)

inductive Ticket where
  | old (ordinal : Nat)
  | variantInline (w : InlineVariant458.Wire)

def used : Ticket → Bool
  | .old _ => false
  | .variantInline _ => true

def variantAt (row : Equation) (a : Address) (c : Nat) : Prop :=
  ∃ tag, a = .variant tag ∧ row.right = .variant tag (.variable c)

def checkVariantAt (row : Equation) (a : Address) (c : Nat) : Bool :=
  match readRawVariant row.right with
  | some (tag,child) => decide (a = .variant tag ∧ child = c)
  | none => false

theorem variant_at_exact458 (row : Equation) (a : Address) (c : Nat) :
    checkVariantAt row a c = true ↔ variantAt row a c := by
  constructor
  · intro h
    cases read : readRawVariant row.right with
    | none => simp [checkVariantAt,read] at h
    | some pair =>
      obtain ⟨tag,n⟩ := pair
      obtain ⟨place,rfl⟩ : a = .variant tag ∧ n = c := by simp [checkVariantAt,read] at h; exact h
      exact ⟨tag,place,(read_raw_variant_exact458 ..).mp read⟩
  · rintro ⟨tag,rfl,rhs⟩
    simp [checkVariantAt,(read_raw_variant_exact458 ..).mpr rhs]

def allows (s : GeneralDeclarativeI65.State) (root : Nat) (row : Equation)
    (a : Address) (c : Nat) : Bool → Prop
  | false => (nominalOps s).allowed root row
  | true => variantAt row a c ∧ OriginalInlineVariant s root row

def checks (s : GeneralDeclarativeI65.State) (root : Nat) (row : Equation)
    (a : Address) (c : Nat) : Ticket → Bool
  | .old ordinal => (nominalOps s).check root row ordinal
  | .variantInline w => checkVariantAt row a c && InlineVariant458.check s root row w

theorem exact_policy_ticket458 (s : GeneralDeclarativeI65.State) (root row a c) (usedHere : Bool) :
    (∃ w, used w = usedHere ∧ checks s root row a c w = true) ↔ allows s root row a c usedHere := by
  constructor
  · rintro ⟨w,rfl,ok⟩
    cases w with
    | old k => exact ((nominalOps s).exactCheck ..).mp ⟨k,ok⟩
    | variantInline w =>
      obtain ⟨atPlace,auth⟩ := Bool.and_eq_true_iff.mp ok
      exact ⟨(variant_at_exact458 ..).mp atPlace,
        (InlineVariant458.linked_inline_variant_has_finite_native_origin_witness458 ..).mp ⟨w,auth⟩⟩
  · intro actual
    cases usedHere with
    | false =>
      obtain ⟨n,yes⟩ := ((nominalOps s).exactCheck ..).mpr actual
      exact ⟨.old n,rfl,yes⟩
    | true =>
      obtain ⟨w,receipt⟩ :=
        (InlineVariant458.linked_inline_variant_has_finite_native_origin_witness458 ..).mpr actual.2
      exact ⟨.variantInline w,rfl,Bool.and_eq_true_iff.mpr
        ⟨(variant_at_exact458 ..).mpr actual.1,receipt⟩⟩

def policy (s : GeneralDeclarativeI65.State) : Policy where
  Token := Ticket
  inline := used
  opens := allows s
  checks := checks s
  reflected := exact_policy_ticket458 s

/-- Index-erasure only. The witness has data, not an authoring proof. -/
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

theorem lift_erase458 (s : GeneralDeclarativeI65.State) (w : Wire (policy s)) :
    lift s (erase s w) = w := by
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

def InlineMeaning (s : GeneralDeclarativeI65.State) (m : I72.Model)
    (root : Nat) (row : Equation) (a : Address) (c : Nat) : Prop :=
  variantAt row a c ∧ OriginalInlineVariant s root row ∧
    ∃ tag term, m.nativeSyntax row.left = some (.ordinary (.variant tag term)) ∧
      ∃ o ∈ s.origins, OriginRoute s o c ∧
        GeneralDeclarativeLowerKnown321.Alias s.current.ordinary c o.slot ∧
        m.nativeSyntax o.slot = some (.ordinary term)

theorem inline_meaning_keeps_the_same_raw_child_and_two_native_reads458
    {s root row a c} (form : variantAt row a c) (authority : OriginalInlineVariant s root row)
    (m : I72.Model) (fit : GeneralDeclarativeI65.Fits s m) : InlineMeaning s m root row a c := by
  obtain ⟨tag,child,term,raw,modelParent,orig,member,route,alias,modelChild⟩ :=
    InlineVariant458.original_paired_inline_variant_receipt_is_exact_in_every_fit458 authority m fit
  obtain ⟨same,tagged,actual⟩ := form
  have names := Expr.variant.inj (raw.symm.trans actual)
  have assigned := Expr.variable.inj names.2
  subst child
  exact ⟨⟨same,tagged,actual⟩,authority,tag,term,modelParent,orig,member,route,alias,modelChild⟩

end Yulang.GeneralDeclarativeI65.I72.VariantInlinePolicy458
