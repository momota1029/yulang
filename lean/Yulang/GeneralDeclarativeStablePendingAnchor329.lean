import Yulang.GeneralDeclarativeStableBackedAnchor329
import Yulang.GeneralDeclarativeRepeat320

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStablePendingAnchor329
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeStableBackedAnchor329 (BackedPoints)
open GeneralDeclarativeOrigins321 (Supported Available restriction backed_iff from_source from_completed)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralDeclarativeOutputOrigins323 (emit)
open GeneralDeclarativeLowerKnown321 (Alias alias_refl Knows)
open CommonNominalFullCarrier (Equivalent)
open GeneralDeclarativeRepeat320 (int)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_symm)

abbrev scalar : Equation := ⟨3,.primitive (.scalar .int) []⟩
abbrev pendingAlias : Equation := ⟨5,.variable 3⟩
abbrev initial : State := ⟨⟨[],[]⟩,[scalar]⟩
abbrev containing := appendFacts initial [pendingAlias]
abbrev span : Capture := ⟨5,3,5⟩

def seed (done : Nat → Prop) : Supported initial done :=
  ⟨fun e reason => e = scalar ∧ reason = .source,fun h => h.1.symm ▸ List.mem_cons_self⟩
abbrev view (done : Nat → Prop) := emit (seed done) 42 [pendingAlias]

theorem truth (m) (fit : Models containing m) : Equivalent (m 5).1 (m 3).1 :=
  fit.2 pendingAlias (List.mem_cons_of_mem _ List.mem_cons_self)

theorem model : Models containing (fun _ => (int,Common.rowEmpty)) := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,fun _ h => False.elim (List.not_mem_nil h)⟩,?_⟩
  intro e found
  change _ ∈ [scalar,pendingAlias] at found
  rcases List.mem_cons.mp found with rfl|tail
  · exact eqv_refl _
  · cases List.mem_singleton.mp tail
    exact eqv_refl _

theorem old_only {e : Equation} (pending : ¬done 42)
    (w : e ∈ (restriction (view done)).equations) : e = scalar := by
  obtain ⟨origin,fromWhere,available⟩ := (backed_iff _ _).mp w
  rcases fromWhere with old|⟨_,rfl⟩
  · exact old.1
  · cases available with
    | completed usable => exact False.elim (pending usable)

theorem only_identity {a b : Nat} (pending : ¬done 42)
    (existing : Alias (restriction (view done)) a b) : a = b := by
  have one {a b : Nat} (inh : GeneralDeclarativeBounds319.Bound containing.normal a b) : a = b := by
    induction inh with
    | refl => rfl
    | interval h => cases h
    | constraint h => cases h
    | trans _ _ l r => exact l.trans r
  induction existing with
  | bounds h _ => exact one h
  | forward h => cases old_only pending h
  | backward h => cases old_only pending h
  | trans _ _ l r => exact l.trans r

theorem exactly (done : Nat → Prop) : BackedPoints (view done) span [] ↔ done 42 := by
  constructor
  · intro known
    by_cases h : done 42
    · exact h
    · have impossible : (5 : Nat) = 3 :=
        only_identity h (known span List.mem_cons_self).1
      cases impossible
  · intro closed arg used
    cases List.mem_singleton.mp used
    have tied : Alias (restriction (view done)) 5 3 :=
      .forward (from_completed _ (.inr ⟨List.mem_cons_self,rfl⟩) closed)
    exact ⟨tied,tied⟩

/-- Identical ordinary truth and models, but the endpoint path becomes
authorized only when its sole output origin is completed. This is the
boundary needed by a supported anchor, not an announcement that the
producer at 42 has actually been completed. -/
theorem ordinary_not_backed :
    (∃ m, Models containing m) ∧ (∀ m, Models containing m → Equivalent (m 5).1 (m 3).1) ∧
    ¬BackedPoints (view (fun _ => False)) span [] ∧ BackedPoints (view (fun n => n = 42)) span [] :=
  ⟨⟨_,model⟩,truth,fun h => (exactly (fun _ => False)).mp h,(exactly _).mpr rfl⟩

end Yulang.GeneralDeclarativeStablePendingAnchor329
