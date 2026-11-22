import Yulang.GeneralDeclarativeTaggedNamedRoute340
import Yulang.GeneralDeclarativeTaggedFixture340

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeTaggedWithheld340
open GeneralDeclarativeHead320 (State Equation Models environment)
open GeneralDeclarativeOrigins321 (Supported restriction Origin backed_iff from_source)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeLowerKnown321 (Alias alias_refl)
open GeneralDeclarativeTaggedNamed340 (Source entails_read)
open GeneralDeclarativeTaggedNamedRoute340 (no_missing_branch)
open GeneralDeclarativeAlternativeView333 (Offer)
open GeneralDeclarativeTaggedFixture340 (eInt eBool whole)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty variant)

abbrev tag := 7
abbrev joined : Equation := ⟨0,.join (.variable 1) (.variable 2)⟩
abbrev first : Equation := ⟨1,.variant tag eInt⟩
abbrev last : Equation := ⟨2,.variant tag eBool⟩
abbrev state : State := ⟨⟨[],[]⟩,[joined,first,last]⟩

def p (done : Nat → Prop) : Supported state done where
  derivesFrom e o := (e = joined ∨ e = first) ∧ o = .source ∨ e = last ∧ o = .output 8
  ordinary := by
    intro e o has
    rcases has with ⟨rfl|rfl,_⟩|⟨rfl,_⟩
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem visible_exact (done : Nat → Prop) (er : Equation) :
    er ∈ (restriction (p done)).equations ↔ er = joined ∨ er = first ∨ er = last ∧ done 8 := by
  rw [backed_iff]
  constructor
  · rintro ⟨origin,(⟨left,rfl⟩|⟨rfl,rfl⟩),allowed⟩
    · exact left.elim Or.inl (fun yes => .inr (.inl yes))
    · cases allowed with
      | completed known => exact .inr (.inr ⟨rfl,known⟩)
  · rintro (rfl|rfl|⟨rfl,known⟩)
    · exact ⟨.source,.inl ⟨.inl rfl,rfl⟩,.source⟩
    · exact ⟨.source,.inl ⟨.inr rfl,rfl⟩,.source⟩
    · exact ⟨.output 8,.inr ⟨rfl,rfl⟩,.completed known⟩

theorem bounds_diagonal (bound : Bound (restriction (p done)).normal a b) : a = b := by
  induction bound with
  | interval h => cases h
  | constraint h => cases h
  | refl => rfl
  | trans _ _ l r => exact l.trans r

theorem alias_diagonal (a : Alias (restriction (p done)) x y) : x = y := by
  induction a with
  | bounds l _ => exact bounds_diagonal l
  | forward inRows | backward inRows =>
    rcases (visible_exact _ _).mp inRows with e|e|⟨e,_⟩ <;> cases e
  | trans _ _ l r => exact l.trans r

theorem absent_offer (isPending : ¬done 8) (found : Offer (restriction (p done)) 2) : False := by
  have root : 2 = found.owner := alias_diagonal found.linked
  rcases (visible_exact _ _).mp found.stored with e|e|⟨_,done⟩
  · have exact0 : found.owner = 0 := congrArg Equation.left e
    cases root.trans exact0
  · have exact1 : found.owner = 1 := congrArg Equation.left e
    cases root.trans exact1
  · exact isPending done

theorem withheld (isPending : ¬done 8) :
    ¬ ∃ term, Source (restriction (p done)) tag (.variable 0) term := by
  rintro ⟨term,seen⟩
  cases seen with
  | named offer branch =>
    have firstOwner : 0 = offer.owner := alias_diagonal offer.linked
    rcases (visible_exact _ _).mp offer.stored with e|e|⟨_,finished⟩
    · have shape : offer.rhs = joined.right := congrArg Equation.right e
      rw [shape] at branch
      exact no_missing_branch (absent_offer isPending) ⟨term,branch⟩
    · have different : offer.owner = 1 := congrArg Equation.left e
      cases firstOwner.trans different
    · exact isPending finished

theorem completed (wasDone : done 8) :
    Source (restriction (p done)) tag (.variable 0) whole := by
  have j := (visible_exact done joined).mpr (.inl rfl)
  have l := (visible_exact done first).mpr (.inr (.inl rfl))
  have r := (visible_exact done last).mpr (.inr (.inr ⟨rfl,wasDone⟩))
  exact .named ⟨0,_,alias_refl _,j⟩ (.join
    (.named ⟨1,_,alias_refl _,l⟩ .tagged) (.named ⟨2,_,alias_refl _,r⟩ .tagged))

/-- Same ordinary constraints, but authorizing the actual output
changes which real reads exist. It does not add a language rejection. -/
theorem support_separates :
    (¬∃ t, Source (restriction (p (fun _ => False))) tag (.variable 0) t) ∧
    Source (restriction (p (fun n => n = 8))) tag (.variable 0) whole :=
  ⟨withheld id,completed rfl⟩

abbrev leftValue : Ty := variant tag (.base .int)
abbrev rightValue : Ty := variant tag (.base .bool)
def witness : Assignment := fun n =>
  (if n = 0 then .union leftValue rightValue else if n = 1 then leftValue else rightValue,
    Common.rowEmpty)

theorem same_ordinary_model : Models state witness := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,fun _ h => False.elim (List.not_mem_nil h)⟩,?_⟩
  intro row recorded
  change row ∈ [joined,first,last] at recorded
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at recorded
  rcases recorded with rfl|rfl|rfl <;> exact eqv_refl _

theorem pending_is_not_false : GeneralDeclarativeEntailment320.Holds witness last ∧
    (¬∃ t, Source (restriction (p (fun _ => False))) tag (.variable 0) t) :=
  ⟨same_ordinary_model.2 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
    support_separates.1⟩

end Yulang.GeneralDeclarativeTaggedWithheld340
