import Yulang.GeneralDeclarativeOpaqueConserve328

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeOpaquePlan328
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeTrace321 (Trace TraceArgs)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeOpaqueTrace328 (ordinary_over_support)
open GeneralDeclarativeOpaqueIntervals328 (Ends low high)
open GeneralDeclarativeOpaqueVariantNames328 (variant_trace)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralDeclarativePairCenters326 (pair)
open GeneralDeclarativePairProbe326 (components)
open GeneralDeclarativeGrowth327 (Extends derives)
open GeneralNominalCenteredHeadMatExpressions (Expr)

inductive Shape : Expr → Prop where
  | capture : Shape (.variable binder)
  | product : Shape a → Shape b → Shape (pair a b)
  | tagged : Shape a → Shape (.variant tag a)
  | invariant : Shape a → Shape (.nominal tag [a])

/-- Actual source endpoint data, not a selected-candidate flag.
A unary invariant node reads a point at its actual parameter; its
different upper parameter is kept in the ordinary root comparison. -/
inductive Plan where
  | capture (binder : Nat)
  | product (ends : Ends) (a b : Plan)
  | tagged (tag lo hi : Nat) (payload : Plan)
  | invariant (tag lo hi : Nat) (payload : Plan)

def Plan.code : Plan → Expr
  | .capture n => .variable n
  | .product _ a b => pair a.code b.code
  | .tagged tag _ _ p => .variant tag p.code
  | .invariant tag _ _ p => .nominal tag [p.code]

inductive Read (s : State) : Nat → Nat → Plan → Prop where
  | capture : Read s lo hi (.capture binder)
  | product : Derives s (.variable lo) (low ends) → Derives s (.variable hi) (high ends) →
      Read s ends.firstLo ends.firstHi a → Read s ends.secondLo ends.secondHi b →
      Read s lo hi (.product ends a b)
  | tagged : Derives s (.variable lo) (.variant tag (.variable a)) →
      Derives s (.variable hi) (.variant tag (.variable b)) → Read s a b node →
      Read s lo hi (.tagged tag a b node)
  | invariant : Derives s (.variable lo) (.nominal tag [.variable a]) →
      Derives s (.variable hi) (.nominal tag [.variable b]) → Read s a a node →
      Read s lo hi (.invariant tag a b node)

theorem grows {s t : State} (h : Extends s t) (old : Read s lo hi p) : Read t lo hi p := by
  induction old with
  | capture => exact .capture
  | product lo hi _ _ a b => exact .product (derives h lo) (derives h hi) a b
  | tagged lo hi _ payload => exact .tagged (derives h lo) (derives h hi) payload
  | invariant lo hi _ payload => exact .invariant (derives h lo) (derives h hi) payload

theorem nominal_one {s : State} {p : Supported s done}
    (read : Trace (restriction p) mode n (.nominal tag [candidate]) used) :
    ∃ name, Derives s (.variable n) (.nominal tag [.variable name]) ∧
      ∃ uses, Trace (restriction p) .actual name candidate uses := by
  cases read with
  | nominal tied row reads =>
    cases reads with
    | cons head rest =>
      cases rest
      exact ⟨_,GeneralDeclarativeOrdinaryIncrease325.derives (ordinary_over_support p)
        (.trans (.congruent (.variable tied)) (.row row)),_,head⟩

/-- Extract an aligned ordinary projection plan directly from two
supported recursive traces, keeping the real endpoint names. Invariant
parameters use actual-mode traces, independently of their parent's mode. -/
theorem extract {s : State} {p : Supported s done}
    (shape : Shape code) (lo : Trace (restriction p) first loName code used)
    (hi : Trace (restriction p) last hiName code other) :
    ∃ plan, plan.code = code ∧ Read s loName hiName plan := by
  induction shape generalizing first last loName hiName used other with
  | capture => exact ⟨.capture _,rfl,.capture⟩
  | product a b ih jh =>
    obtain ⟨ll,lr,_,_,lowRead,lowL,lowR,_⟩ := components lo
    obtain ⟨hl,hr,_,_,highRead,highL,highR,_⟩ := components hi
    obtain ⟨left,printedL,decodedL⟩ := ih lowL highL
    obtain ⟨right,printedR,decodedR⟩ := jh lowR highR
    let ends : Ends := ⟨ll,hl,lr,hr⟩
    exact ⟨.product ends left right,by simp [Plan.code,printedL,printedR],
      .product (GeneralDeclarativeOrdinaryIncrease325.derives (ordinary_over_support p) lowRead)
        (GeneralDeclarativeOrdinaryIncrease325.derives (ordinary_over_support p) highRead) decodedL decodedR⟩
  | tagged a ih =>
    obtain ⟨l,left,aRead⟩ := variant_trace lo
    obtain ⟨h,right,bRead⟩ := variant_trace hi
    obtain ⟨payload,printed,decoded⟩ := ih aRead bRead
    exact ⟨.tagged _ l h payload,by simp [Plan.code,printed],.tagged left right decoded⟩
  | invariant a ih =>
    obtain ⟨l,left,_,aRead⟩ := nominal_one lo
    obtain ⟨h,right,_,_⟩ := nominal_one hi
    obtain ⟨payload,printed,decoded⟩ := ih aRead aRead
    exact ⟨.invariant _ l h payload,by simp [Plan.code,printed],.invariant left right decoded⟩

end Yulang.GeneralDeclarativeOpaquePlan328
