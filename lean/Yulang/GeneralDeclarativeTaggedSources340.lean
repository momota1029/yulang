import Yulang.GeneralDeclarativeMixedLeafGrowth339
import Yulang.GeneralDeclarativePlainCapture323
import Yulang.GeneralDeclarativeOpaqueConserve328

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeTaggedSources340
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_trans variant_congr union_congr)
open GeneralNominalCommonBridge (Assignment variant_merge)
open GeneralDeclarativeHead320 (State Equation Models environment)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeEntailment320 (Entails Holds)
open GeneralDeclarativeEqualities322 (Derives entails)
open GeneralDeclarativeGrowth327 (Extends derives)
open GeneralDeclarativeCompoundSources338 (Anchored)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeWhere319 (Capture)
open CommonNominalFullCarrier (Equivalent)

def merge (tag : Nat) : Expr → Option Expr
  | .variant k x => if k = tag then some x else none
  | .join a b => do return .join (← merge tag a) (← merge tag b)
  | _ => none

inductive Groups (tag : Nat) : Expr → Expr → Prop where
  | single : Groups tag (.variant tag a) a
  | join : Groups tag a x → Groups tag b y → Groups tag (.join a b) (.join x y)

theorem decode_sound (tag : Nat) (source payload : Expr)
    (written : merge tag source = some payload) : Groups tag source payload := by
  cases source with
  | variant k x =>
    by_cases eq : k = tag
    · subst k
      have same : x = payload := by simpa [merge] using written
      subst payload
      exact .single
    · simp [merge,eq] at written
  | join a b =>
    cases x : merge tag a with
    | none => simp [merge,x] at written
    | some l =>
      cases y : merge tag b with
      | none => simp [merge,x,y] at written
      | some r =>
        have same : Expr.join l r = payload := by simpa [merge,x,y] using written
        subst payload
        exact .join (decode_sound tag a _ x) (decode_sound tag b _ y)
  | «variable» | primitive | nominal | record => simp [merge] at written
termination_by sizeOf source

theorem decodes (tag : Nat) (source payload : Expr) :
    merge tag source = some payload ↔ Groups tag source payload := by
  refine ⟨decode_sound tag source payload,?_⟩
  intro known
  induction known with
  | single => simp [merge]
  | join _ _ left right => simp [merge,left,right]

theorem group_sound (seen : Groups tag source payload) (m : Assignment) :
    Equivalent (value (environment m) .actual source) (value (environment m) .actual (.variant tag payload)) := by
  induction seen with
  | single => exact eqv_refl _
  | join _ _ known later => exact eqv_trans (union_congr known later) (variant_merge _ _ _)

/-- The outer grouping is read from actually available authored syntax.
It does not inspect a payload to split it or infer support from models. -/
structure Read {s : State} (p : Supported s done) (name tag : Nat) (payload : Expr) : Prop where
  source : ∃ original, Anchored (restriction p) name original ∧ merge tag original = some payload

theorem entail {s : State} {p : Supported s done} (seen : Read p name tag payload) :
    Entails s ⟨name,.variant tag payload⟩ := by
  obtain ⟨original,⟨owner,identity,authored⟩,decoded⟩ := seen.source
  have written : Derives (restriction p) (.variable name) original :=
    .trans (.congruent (.variable identity)) (.row authored)
  have proof := GeneralDeclarativeOrdinaryIncrease325.derives
    (GeneralDeclarativeOpaqueTrace328.ordinary_over_support p) written
  exact fun m v => eqv_trans (entails proof m v) (group_sound ((decodes _ _ _).mp decoded) m)

theorem prefers_no_split {s : State} {p : Supported s done} (seen : Read p name tag payload)
    (grew : Extends (restriction p) (restriction q)) : Read q name tag payload := by
  obtain ⟨src,known,written⟩ := seen.source
  exact ⟨src,GeneralDeclarativeCompoundSources338.anchored_grows grew known,written⟩

structure BoundsRead {s : State} (p : Supported s done) (arg : Capture) (tag : Nat) (low high : Expr) : Prop where
  interval : Bounds s arg
  lower : Read p arg.lower tag low
  upper : Read p arg.upper tag high

end Yulang.GeneralDeclarativeTaggedSources340
