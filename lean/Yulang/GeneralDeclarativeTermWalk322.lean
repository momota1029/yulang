import Yulang.GeneralDeclarativeEqualities322
import Yulang.GeneralDeclarativeSubstitution320

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeTermWalk322
open GeneralDeclarativeHead320 (State byMode)
open GeneralDeclarativeEqualities322 (Derives Forest)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeSubstitution320 (logical logicals)
open GeneralNominalMaterialization (Mode)
open GeneralNominalCenteredHeadMatExpressions (Expr)

structure Occurrence where
  binder : Nat
  mode : Mode
  term : Expr

mutual
/-- Read a finite ordinary expression without requiring a separate name for
every intermediate constructor. The ordinary names of captured values are
checked after the walk; the walk itself never chooses a type assignment. -/
inductive Walk : Mode → Expr → Expr → List Occurrence → Prop where
  | capture : Walk mode source (.variable binder) [⟨binder,mode,source⟩]
  | primitive : WalkMany mode as bs seen → Walk mode (.primitive tag as) (.primitive tag bs) seen
  | nominal : WalkMany .actual as bs seen → Walk mode (.nominal tag as) (.nominal tag bs) seen
  | record : Walk mode a b first → Walk mode x y rest →
      Walk mode (.record label a x) (.record label b y) (first ++ rest)
  | variant : Walk mode a b seen → Walk mode (.variant tag a) (.variant tag b) seen
  | join : Walk mode a b first → Walk mode x y rest → Walk mode (.join a x) (.join b y) (first ++ rest)
inductive WalkMany : Mode → List Expr → List Expr → List Occurrence → Prop where
  | nil : WalkMany mode [] [] []
  | cons : Walk mode a b first → WalkMany mode as bs rest →
      WalkMany mode (a :: as) (b :: bs) (first ++ rest)
end

def Binds (s : State) (capture : Nat → Capture) (seen : List Occurrence) : Prop :=
  ∀ atTerm ∈ seen, Derives s atTerm.term (.variable (byMode (capture atTerm.binder) atTerm.mode))

theorem split_binds (proof : Binds s capture (one ++ two)) :
    Binds s capture one ∧ Binds s capture two :=
  ⟨fun o h => proof o (List.mem_append_left _ h),fun o h => proof o (List.mem_append_right _ h)⟩

theorem substitute {s : State} {capture : Nat → Capture}
    (walk : Walk mode term pattern seen) (known : Binds s capture seen) :
    Derives s term (logical capture mode pattern) :=
  Walk.rec
    (motive_1 := fun mode a b seen _ => Binds s capture seen → Derives s a (logical capture mode b))
    (motive_2 := fun mode as bs seen _ => Binds s capture seen → Forest s as (logicals capture mode bs))
    (fun h => h _ List.mem_cons_self)
    (fun _ ih known => .primitive (ih known))
    (fun _ ih known => .nominal (ih known))
    (fun _ _ ih jh known => .record (ih (split_binds known).1) (jh (split_binds known).2))
    (fun _ ih known => .variant (ih known))
    (fun _ _ ih jh known => .join (ih (split_binds known).1) (jh (split_binds known).2))
    (fun _ => .nil)
    (fun _ _ ih jh known => .cons (ih (split_binds known).1) (jh (split_binds known).2))
    walk known

theorem actual_head_eq {s : State} {capture : Nat → Capture}
    (exposes : Derives s (.variable name) term)
    (walk : Walk .actual term pattern seen) (known : Binds s capture seen) :
    Derives s (.variable name) (logical capture .actual pattern) :=
  .trans exposes (substitute walk known)

end Yulang.GeneralDeclarativeTermWalk322
