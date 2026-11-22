import Yulang.GeneralDeclarativeAlternativeMixedReplay333
import Yulang.GeneralDeclarativeArityRun330

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessHead334
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarationPatterns (Constructors Pattern normalize)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarativeTrace321 (Trace)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralDeclarativeStableTrace329 (Actual from_trace)
open GeneralDeclarativeAlternativeRange333 (Known materialize materialize_exact)
open GeneralDeclarativeArityPlan330 (Plan Reads grow)
open GeneralDeclarativeArityRun330 (run build)
open GeneralDeclarativeStableReads329 (One Heads)
open GeneralDeclarativeGrowth327 (Extends fits trans)
open GeneralDeclarativeOpaqueConserve328 (Retains refl chain)
open GeneralDeclarativeObserverGrowth330 (preserve sources_grow trace located)
open GeneralDeclarativeInlineGrowth331 (extend)
open GeneralDeclarativeAlternativeCapture333 (transport_one)

/-- An ordinary source slice, not an execution history. The restricted
embedding is separate: an ordinary equation true now does not make a
withheld historical RHS available to the present observer. -/
structure Slice {s : State} (current : Supported s done) where
  base : State
  support : Supported base done
  ordinary : Extends base s
  allowed : Extends (restriction support) (restriction current)

def full {s : State} (p : Supported s done) : Slice p :=
  ⟨s,p,GeneralDeclarativeClauseBatch327.reflexive _,GeneralDeclarativeClauseBatch327.reflexive _⟩

/-- Relational capture construction with literal names. The three
routes are the existing named, inline and interval observations;
ordinary constructors created by preparation are not made origins. -/
inductive Argument {s : State} (p : Supported s done) (c : Constructors) (i : Interpretation)
    (keep : List Nat) : State → Capture → Pattern → State → List (Nat × Capture) → Prop where
  | named : Actual s c i p arg pat spans → Argument p c i keep before arg pat before spans
  | inline {view : Known s} : Bounds s arg → translate c i (normalize pat) = some code →
      Read (restriction p) .actual (.variable arg.center) code uses →
      materialize view before arg keep code uses = some (after,spans) →
      Argument p c i keep before arg pat after spans
  | projected : Bounds s arg → translate c i (normalize pat) = some plan.code →
      Reads (restriction p) arg.lower arg.upper plan →
      Argument p c i keep before arg pat (run keep before arg plan).state (run keep before arg plan).binds

theorem argument_sound {s t : State} {p : Supported s done}
    (actual : Argument p c i keep t arg pat after spans) (ordinary : Extends s t) :
    Retains t after keep ∧ One after c i arg pat spans ∧ ∀ slot ∈ spans, Bounds after slot.2 := by
  cases actual with
  | named old =>
    obtain ⟨code,seen,printed,real,whereSeen⟩ := old.reads
    obtain ⟨head,known⟩ := from_trace (p := preserve p ordinary) (fits ordinary old.args) printed
      (trace (sources_grow p ordinary) real) (located ordinary whereSeen)
    exact ⟨refl _ _,head,known⟩
  | inline fit normalized source computed =>
    exact materialize_exact (s := s) _ ordinary (fits ordinary fit) normalized
      (extend (sources_grow p ordinary) source) computed
  | projected fit normalized reads =>
    have raw : Extends (restriction p) t :=
      ⟨ordinary.constraints,ordinary.intervals,fun e seen => ordinary.equations
        (GeneralDeclarativeOrigins321.backed_iff p e |>.mp seen |>.elim
          fun o h => p.ordinary h.1)⟩
    have checked := build keep arg _ (fits ordinary fit) (grow raw reads)
    exact ⟨checked.modeled,⟨fits checked.modeled.grows (fits ordinary fit),_,_,
      normalized,checked.center,checked.walks⟩,checked.bounds⟩

inductive Actuals {s : State} (p : Supported s done) (c : Constructors) (i : Interpretation)
    (keep : List Nat) : State → List Capture → List Pattern → State → List (Nat × Capture) → Prop where
  | nil : Actuals p c i keep before [] [] before []
  | cons : Argument p c i keep before arg pat middle first →
      Actuals p c i keep middle args pats after last →
      Actuals p c i keep before (arg::args) (pat::pats) after (first++last)

theorem actuals_sound {s t : State} {p : Supported s done}
    (actual : Actuals p c i keep t args pats after spans) (ordinary : Extends s t) :
    Retains t after keep ∧ Heads after c i args pats spans ∧ ∀ slot ∈ spans, Bounds after slot.2 := by
  induction actual with
  | nil => exact ⟨refl _ _,.nil,fun _ empty => False.elim (List.not_mem_nil empty)⟩
  | cons first _ ih =>
    obtain ⟨retained,one,ranges⟩ := argument_sound first ordinary
    obtain ⟨later,heads,tailBounds⟩ := ih (trans ordinary retained.grows)
    refine ⟨chain retained later,.cons (transport_one later.grows one) heads,?_⟩
    intro slot requested
    exact (List.mem_append.mp requested).elim (fun h => fits later.grows (ranges _ h)) (tailBounds _)


open CommonRoleOutermostResolver (All₂)

def CurrentArgument {s : State} (p : Supported s done) (c : Constructors) (i : Interpretation)
    (a : Capture) (pat : Pattern) : Prop :=
  Bounds s a ∧
    ((∃ code uses, translate c i (normalize pat) = some code ∧ Trace (restriction p) .actual a.center code uses) ∨
     (∃ code uses, translate c i (normalize pat) = some code ∧ Read (restriction p) .actual (.variable a.center) code uses) ∨
     (∃ plan : Plan, translate c i (normalize pat) = some plan.code ∧ Reads (restriction p) a.lower a.upper plan))

theorem current_argument {s : State} {p : Supported s done} (sl : Slice p)
    (argRead : Argument sl.support c i keep a arg pat b spans) :
    CurrentArgument p c i arg pat := by
  cases argRead with
  | named w =>
    obtain ⟨code,uses,printed,seen,_⟩ := w.reads
    exact ⟨fits sl.ordinary w.args,.inl ⟨code,uses,printed,trace sl.allowed seen⟩⟩
  | inline fit printed seen _ =>
    exact ⟨fits sl.ordinary fit,.inr (.inl ⟨_,_,printed,extend sl.allowed seen⟩)⟩
  | projected fit printed seen =>
    exact ⟨fits sl.ordinary fit,.inr (.inr ⟨_,printed,grow sl.allowed seen⟩)⟩

theorem current_heads {s : State} {p : Supported s done} (sl : Slice p)
    (read : Actuals sl.support c i keep a args pats b spans) :
    All₂ (CurrentArgument p c i) args pats := by
  induction read with
  | nil => exact .nil
  | cons here _ rest => exact .cons (current_argument sl here) rest

end Yulang.GeneralDeclarativeWitnessHead334
