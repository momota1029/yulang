import Yulang.CommonNominalFullFiniteMaskOrder

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace Yulang.GeneralDeclarativeDeleteShell337
open CommonNominalFullDemand (Ty Observation MaskedProbeStep Environment)
variable {Row : Type u} {leRow : Row → Row → Prop} {env : Environment Row}
  {ordered : Ty Row → Ty Row → Prop}

def shell : Ty Row → Ty Row
  | .bottom => .record 0 .bottom .bottom
  | .union a b => .union (shell a) (shell b)
  | .inter a b => .inter (shell a) (shell b)
  | .mask hs a => .mask hs (shell a)
  | t@(.emptyRecord) | t@(.exactEmpty) | t@(.record _ _ _) | t@(.recordDefault _ _ _) => t
  | _ => .emptyRecord

def requiredField (H : List Nat) (t : Ty Row) (k : Nat) (o : Observation Row) :=
  MaskedProbeStep leRow env ordered H t (.field k o)
def optionalField (H : List Nat) (t : Ty Row) (k : Nat) (o : Observation Row) :=
  MaskedProbeStep leRow env ordered H t (.optional k o)

theorem required_eq (t : Ty Row) (hidden : List Nat) (q : Nat) (probe : Observation Row) :
    requiredField (leRow := leRow) (env := env) (ordered := ordered) hidden (shell t) q probe ↔
      requiredField (leRow := leRow) (env := env) (ordered := ordered) hidden t q probe := by
  induction t using CommonNominalFinite.Ty.rec (motive_2 := fun _ => True)
    (motive_3 := fun _ => True) generalizing hidden with
  | union _ _ ia ib => simp only [requiredField,shell,MaskedProbeStep] at ia ib ⊢; exact and_congr (ia _) (ib _)
  | inter _ _ ia ib => simp only [requiredField,shell,MaskedProbeStep] at ia ib ⊢; exact or_congr (ia _) (ib _)
  | mask _ _ ih => exact ih _
  | bottom => cases probe <;> simp [requiredField,shell,MaskedProbeStep]
  | _ => first | exact Iff.rfl | trivial

theorem optional_eq (t : Ty Row) (hidden : List Nat) (q : Nat) (probe : Observation Row) :
    optionalField (leRow := leRow) (env := env) (ordered := ordered) hidden (shell t) q probe ↔
      optionalField (leRow := leRow) (env := env) (ordered := ordered) hidden t q probe ∨ probe = .trivial := by
  induction t using CommonNominalFinite.Ty.rec (motive_2 := fun _ => True)
    (motive_3 := fun _ => True) generalizing hidden with
  | union _ _ ia ib =>
    simp only [optionalField,shell,MaskedProbeStep] at ia ib ⊢
    rw [ia,ib]
    constructor
    · rintro ⟨a|a,b|b⟩
      · exact .inl ⟨a,b⟩
      · exact .inr b
      · exact .inr a
      · exact .inr a
    · rintro (⟨a,b⟩|trivial)
      · exact ⟨.inl a,.inl b⟩
      · exact ⟨.inr trivial,.inr trivial⟩
  | inter _ _ ia ib =>
    simp only [optionalField,shell,MaskedProbeStep] at ia ib ⊢
    rw [ia,ib]
    constructor
    · rintro ((a|a)|(b|b))
      · exact .inl (.inl a)
      · exact .inr a
      · exact .inl (.inr b)
      · exact .inr b
    · rintro ((a|b)|trivial)
      · exact .inl (.inl a)
      · exact .inr (.inl b)
      · exact .inl (.inr trivial)
  | mask _ _ ih => exact ih _
  | bottom => cases probe <;> simp [optionalField,shell,MaskedProbeStep]
  | emptyRecord => simp [optionalField,shell,MaskedProbeStep]
  | exactEmpty => simp [optionalField,shell,MaskedProbeStep,or_assoc]
  | record x p rest _ _ =>
    refine ⟨Or.inl,?_⟩
    rintro (earlier|rfl)
    · exact earlier
    · change MaskedProbeStep leRow env ordered hidden (.record x p rest) (.optional q .trivial)
      by_cases looks : q = x ∧ x ∉ hidden
      · simp [MaskedProbeStep,looks]
      · simp [MaskedProbeStep,looks]
  | recordDefault x s f _ _ =>
    refine ⟨Or.inl,?_⟩
    rintro (earlier|rfl)
    · exact earlier
    · simp [optionalField,shell,MaskedProbeStep]
  | _ => first | (simp [optionalField,shell,MaskedProbeStep]) | trivial

theorem outside (t : Ty Row) (hidden : List Nat) (probe : Observation Row)
    (notField : ¬ probe.isOuterField) :
    MaskedProbeStep leRow env ordered hidden (shell t) probe ↔
      MaskedProbeStep leRow env ordered hidden .emptyRecord probe := by
  induction t using CommonNominalFinite.Ty.rec (motive_2 := fun _ => True)
    (motive_3 := fun _ => True) generalizing hidden with
  | union _ _ ia ib =>
    cases probe <;> simp_all [shell,Observation.isOuterField,MaskedProbeStep]
  | inter _ _ ia ib =>
    cases probe <;> simp_all [shell,Observation.isOuterField,MaskedProbeStep]
  | mask _ _ ih =>
    cases probe <;> simp_all [shell,Observation.isOuterField,MaskedProbeStep]
  | _ => first | (cases probe <;> simp_all [shell,Observation.isOuterField,MaskedProbeStep]) | trivial

end Yulang.GeneralDeclarativeDeleteShell337
