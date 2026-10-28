import YulangClosure.HigherOrderRecAllocation

/-! Candidate typed observations of the actual higher-order graph. Projection
is used only for the decreasing rank. Bodies and data fields are not unfolded;
transparent evidence is retained with its own types. -/
namespace YulangClosure.HigherOrderGraph
open HigherOrder (Ty Context emptyContext extend ViewOccurrence ReceiptTemplate)

variable {R : Type}

/-- A finite typed observation of the transparent spine. The two premises of
`both` remain separate. A wrap retains its inner and outer callable types and
both adapters, even when these types differ. Genuine data/code introductions
retain their original typing derivations and stop observation. -/
inductive ObservedTyped (graph : Graph R) (xi : R → Ty) : Value R Empty → Ty → Prop where
  | ref (r) : ObservedTyped graph xi (graph r) (xi r) → ObservedTyped graph xi (.ref r) (xi r)
  | unit : ObservedTyped graph xi .unit (.base .unit)
  | bool : ObservedTyped graph xi (.bool v) (.base .bool)
  | int : ObservedTyped graph xi (.int v) (.base .int)
  | floatBits : ObservedTyped graph xi (.floatBits v) (.base .float)
  | string : ObservedTyped graph xi (.string v) (.base .string)
  | bytes : ObservedTyped graph xi (.bytes v) (.base .bytes)
  | path : ObservedTyped graph xi (.path v) (.base .path)
  | char : ObservedTyped graph xi (.char v) (.base .char)
  | delay : CompTyped xi emptyTy emptyContext body a → ObservedTyped graph xi (.delay body) (.thunk a)
  | inLeft : ValueTyped xi emptyTy emptyContext v a → ObservedTyped graph xi (.inLeft v) (.union a b)
  | inRight : ValueTyped xi emptyTy emptyContext v b → ObservedTyped graph xi (.inRight v) (.union a b)
  | both : ObservedTyped graph xi v a → ObservedTyped graph xi v b →
      ObservedTyped graph xi (.both v) (.intersection a b)
  | top : ObservedTyped graph xi v a → ObservedTyped graph xi (.top v) .top
  | view : ObservedTyped graph xi v a → ObservedTyped graph xi (.view v occurrence) a
  | lambdaValue : CompTyped xi emptyTy (extend emptyContext a) body b →
      AdapterTyped xi emptyTy emptyContext consumer b r →
      ObservedTyped graph xi (.lambda .value receipt a b r body consumer) (.callable a r)
  | lambdaComputation : CompTyped xi emptyTy (extend emptyContext (.thunk a)) body b →
      AdapterTyped xi emptyTy emptyContext consumer b r →
      ObservedTyped graph xi (.lambda .computation receipt a b r body consumer) (.callable a r)
  | wrap : ObservedTyped graph xi f (.callable a b) →
      AdapterTyped xi emptyTy emptyContext input c a → AdapterTyped xi emptyTy emptyContext output b d →
      ObservedTyped graph xi (.wrap f input output) (.callable c d)

variable {graph : Graph R} {xi : R → Ty}

theorem ObservedTyped.typed (h : ObservedTyped graph xi v a) :
    ValueTyped xi emptyTy emptyContext v a := by
  induction h with
  | ref r _ _ => exact .ref r
  | unit => exact .unit
  | bool => exact .bool
  | int => exact .int
  | floatBits => exact .floatBits
  | string => exact .string
  | bytes => exact .bytes
  | path => exact .path
  | char => exact .char
  | delay h => exact .delay h
  | inLeft h => exact .inLeft h
  | inRight h => exact .inRight h
  | both _ _ ih ik => exact .both ih ik
  | top _ ih => exact .top ih
  | view _ ih => exact .view ih
  | lambdaValue h k => exact .lambdaValue h k
  | lambdaComputation h k => exact .lambdaComputation h k
  | wrap _ i o ih => exact .wrap ih i o

/-- Structural descent handles arbitrary finite wrapper syntax between graph
edges. The reference supplier is required only at the actual frontier. -/
theorem observe_from_references (h : ValueTyped xi emptyTy emptyContext v a)
    (refs : ∀ r, nextValue v = some r → ObservedTyped graph xi (.ref r) (xi r)) :
    ObservedTyped graph xi v a := by
  cases h with
  | ref r => exact refs r rfl
  | recvar e => exact Empty.elim e
  | var h => cases h
  | unit => exact .unit
  | bool => exact .bool
  | int => exact .int
  | floatBits => exact .floatBits
  | string => exact .string
  | bytes => exact .bytes
  | path => exact .path
  | char => exact .char
  | delay h => exact .delay h
  | inLeft h => exact .inLeft h
  | inRight h => exact .inRight h
  | both h k => exact .both (observe_from_references h refs) (observe_from_references k refs)
  | top h => exact .top (observe_from_references h refs)
  | view h => exact .view (observe_from_references h refs)
  | lambdaValue h k => exact .lambdaValue h k
  | lambdaComputation h k => exact .lambdaComputation h k
  | wrap h i o => exact .wrap (observe_from_references h refs) i o

/-- Actual reference lookup plus the accepted guard derive finite observation;
no canonical-value or typing oracle for projected terminal units is used. -/
theorem typed_observation (hg : WellTyped graph xi)
    (guard : GuardedValueGraph.Guarded (projectGraph graph))
    (h : ValueTyped xi emptyTy emptyContext v a) : ObservedTyped graph xi v a := by
  have aux : ∀ n (v : Value R Empty) a,
      ValueTyped xi emptyTy emptyContext v a →
      (∀ r, nextValue v = some r → guard.rank r < n) → ObservedTyped graph xi v a := by
    intro n
    induction n with
    | zero =>
        intro v a hv hb
        apply observe_from_references hv
        intro r hr
        exact False.elim (Nat.not_lt_zero _ (hb r hr))
    | succ n ih =>
        intro v a hv hb
        apply observe_from_references hv
        intro r hr
        apply ObservedTyped.ref r
        apply ih (graph r) (xi r) (hg r)
        intro s hs
        exact Nat.lt_of_lt_of_le
          (guard.decrease r s ((projection_edge graph r s).mpr hs))
          (Nat.le_of_lt_succ (hb r hr))
  exact aux guard.ceiling v a h (fun r _ => guard.bound r)

/-- Raw finite reference/view lookup. `here` retains the actual value, and
suppliers below determine its required introduction shape. No typing premise
occurs in this relation. Wrapper entry is not erased by this lookup. -/
inductive Head (graph : Graph R) : Value R Empty → Value R Empty → Prop where
  | here (v) : Head graph v v
  | ref : Head graph (graph r) w → Head graph (.ref r) w
  | view : Head graph v w → Head graph (.view v occurrence) w

theorem thunk_observation_of_eq (h : ObservedTyped graph xi v t) (ht : t = .thunk a) :
    ∃ body, Head graph v (.delay body) ∧ CompTyped xi emptyTy emptyContext body a := by
  revert ht
  induction h with
  | ref r h ih =>
      intro ht
      obtain ⟨body, hh, ht⟩ := ih ht
      exact ⟨body, .ref hh, ht⟩
  | view h ih =>
      intro ht
      obtain ⟨body, hh, ht⟩ := ih ht
      exact ⟨body, .view hh, ht⟩
  | delay h =>
      intro ht
      cases ht
      exact ⟨_, .here _, h⟩
  | unit => intro ht; cases ht
  | bool => intro ht; cases ht
  | int => intro ht; cases ht
  | floatBits => intro ht; cases ht
  | string => intro ht; cases ht
  | bytes => intro ht; cases ht
  | path => intro ht; cases ht
  | char => intro ht; cases ht
  | inLeft h => intro ht; cases ht
  | inRight h => intro ht; cases ht
  | both h k ih ik => intro ht; cases ht
  | top h ih => intro ht; cases ht
  | lambdaValue h k => intro ht; cases ht
  | lambdaComputation h k => intro ht; cases ht
  | wrap h i o ih => intro ht; cases ht

theorem thunk_observation (h : ObservedTyped graph xi v (.thunk a)) :
    ∃ body, Head graph v (.delay body) ∧ CompTyped xi emptyTy emptyContext body a :=
  thunk_observation_of_eq h rfl

inductive CallableTerminal (xi : R → Ty) : Value R Empty → Ty → Ty → Prop where
  | lambdaValue : CompTyped xi emptyTy (extend emptyContext a) body b →
      AdapterTyped xi emptyTy emptyContext consumer b r →
      CallableTerminal xi (.lambda .value receipt a b r body consumer) a r
  | lambdaComputation : CompTyped xi emptyTy (extend emptyContext (.thunk a)) body b →
      AdapterTyped xi emptyTy emptyContext consumer b r →
      CallableTerminal xi (.lambda .computation receipt a b r body consumer) a r
  | wrap : ValueTyped xi emptyTy emptyContext f (.callable a b) →
      AdapterTyped xi emptyTy emptyContext input c a → AdapterTyped xi emptyTy emptyContext output b d →
      CallableTerminal xi (.wrap f input output) c d

theorem callable_observation_of_eq (h : ObservedTyped graph xi v t) (ht : t = .callable a b) :
    ∃ w, Head graph v w ∧ CallableTerminal xi w a b := by
  revert ht
  induction h with
  | ref r h ih =>
      intro ht
      obtain ⟨w, hh, ht⟩ := ih ht
      exact ⟨w, .ref hh, ht⟩
  | view h ih =>
      intro ht
      obtain ⟨w, hh, ht⟩ := ih ht
      exact ⟨w, .view hh, ht⟩
  | lambdaValue h k =>
      intro ht
      cases ht
      exact ⟨_, .here _, .lambdaValue h k⟩
  | lambdaComputation h k =>
      intro ht
      cases ht
      exact ⟨_, .here _, .lambdaComputation h k⟩
  | wrap h i o ih =>
      intro ht
      cases ht
      exact ⟨_, .here _, .wrap h.typed i o⟩
  | unit => intro ht; cases ht
  | bool => intro ht; cases ht
  | int => intro ht; cases ht
  | floatBits => intro ht; cases ht
  | string => intro ht; cases ht
  | bytes => intro ht; cases ht
  | path => intro ht; cases ht
  | char => intro ht; cases ht
  | delay h => intro ht; cases ht
  | inLeft h => intro ht; cases ht
  | inRight h => intro ht; cases ht
  | both h k ih ik => intro ht; cases ht
  | top h ih => intro ht; cases ht

theorem callable_observation (h : ObservedTyped graph xi v (.callable a b)) :
    ∃ w, Head graph v w ∧ CallableTerminal xi w a b :=
  callable_observation_of_eq h rfl

theorem union_observation_of_eq (h : ObservedTyped graph xi v t) (ht : t = .union a b) :
    (∃ w, Head graph v (.inLeft w) ∧ ValueTyped xi emptyTy emptyContext w a) ∨
    (∃ w, Head graph v (.inRight w) ∧ ValueTyped xi emptyTy emptyContext w b) := by
  revert ht
  induction h with
  | ref r h ih =>
      intro ht
      rcases ih ht with ⟨w, hh, ht⟩ | ⟨w, hh, ht⟩
      · exact .inl ⟨w, .ref hh, ht⟩
      · exact .inr ⟨w, .ref hh, ht⟩
  | view h ih =>
      intro ht
      rcases ih ht with ⟨w, hh, ht⟩ | ⟨w, hh, ht⟩
      · exact .inl ⟨w, .view hh, ht⟩
      · exact .inr ⟨w, .view hh, ht⟩
  | inLeft h =>
      intro ht
      cases ht
      exact .inl ⟨_, .here _, h⟩
  | inRight h =>
      intro ht
      cases ht
      exact .inr ⟨_, .here _, h⟩
  | unit => intro ht; cases ht
  | bool => intro ht; cases ht
  | int => intro ht; cases ht
  | floatBits => intro ht; cases ht
  | string => intro ht; cases ht
  | bytes => intro ht; cases ht
  | path => intro ht; cases ht
  | char => intro ht; cases ht
  | delay h => intro ht; cases ht
  | both h k ih ik => intro ht; cases ht
  | top h ih => intro ht; cases ht
  | lambdaValue h k => intro ht; cases ht
  | lambdaComputation h k => intro ht; cases ht
  | wrap h i o ih => intro ht; cases ht

theorem union_observation (h : ObservedTyped graph xi v (.union a b)) :
    (∃ w, Head graph v (.inLeft w) ∧ ValueTyped xi emptyTy emptyContext w a) ∨
    (∃ w, Head graph v (.inRight w) ∧ ValueTyped xi emptyTy emptyContext w b) :=
  union_observation_of_eq h rfl

theorem intersection_observation_of_eq (h : ObservedTyped graph xi v t) (ht : t = .intersection a b) :
    ∃ w, Head graph v (.both w) ∧ ValueTyped xi emptyTy emptyContext w a ∧
      ValueTyped xi emptyTy emptyContext w b := by
  revert ht
  induction h with
  | ref r h ih =>
      intro ht
      obtain ⟨w, hh, ha, hb⟩ := ih ht
      exact ⟨w, .ref hh, ha, hb⟩
  | view h ih =>
      intro ht
      obtain ⟨w, hh, ha, hb⟩ := ih ht
      exact ⟨w, .view hh, ha, hb⟩
  | both h k ih ik =>
      intro ht
      cases ht
      exact ⟨_, .here _, h.typed, k.typed⟩
  | unit => intro ht; cases ht
  | bool => intro ht; cases ht
  | int => intro ht; cases ht
  | floatBits => intro ht; cases ht
  | string => intro ht; cases ht
  | bytes => intro ht; cases ht
  | path => intro ht; cases ht
  | char => intro ht; cases ht
  | delay h => intro ht; cases ht
  | inLeft h => intro ht; cases ht
  | inRight h => intro ht; cases ht
  | top h ih => intro ht; cases ht
  | lambdaValue h k => intro ht; cases ht
  | lambdaComputation h k => intro ht; cases ht
  | wrap h i o ih => intro ht; cases ht

theorem intersection_observation (h : ObservedTyped graph xi v (.intersection a b)) :
    ∃ w, Head graph v (.both w) ∧ ValueTyped xi emptyTy emptyContext w a ∧
      ValueTyped xi emptyTy emptyContext w b :=
  intersection_observation_of_eq h rfl

theorem top_observation_of_eq (h : ObservedTyped graph xi v t) (ht : t = .top) :
    ∃ w a, Head graph v (.top w) ∧ ValueTyped xi emptyTy emptyContext w a := by
  revert ht
  induction h with
  | ref r h ih =>
      intro ht
      obtain ⟨w, a, hh, ht⟩ := ih ht
      exact ⟨w, a, .ref hh, ht⟩
  | view h ih =>
      intro ht
      obtain ⟨w, a, hh, ht⟩ := ih ht
      exact ⟨w, a, .view hh, ht⟩
  | top h ih =>
      intro ht
      cases ht
      exact ⟨_, _, .here _, h.typed⟩
  | unit => intro ht; cases ht
  | bool => intro ht; cases ht
  | int => intro ht; cases ht
  | floatBits => intro ht; cases ht
  | string => intro ht; cases ht
  | bytes => intro ht; cases ht
  | path => intro ht; cases ht
  | char => intro ht; cases ht
  | delay h => intro ht; cases ht
  | inLeft h => intro ht; cases ht
  | inRight h => intro ht; cases ht
  | both h k ih ik => intro ht; cases ht
  | lambdaValue h k => intro ht; cases ht
  | lambdaComputation h k => intro ht; cases ht
  | wrap h i o ih => intro ht; cases ht

theorem top_observation (h : ObservedTyped graph xi v .top) :
    ∃ w a, Head graph v (.top w) ∧ ValueTyped xi emptyTy emptyContext w a :=
  top_observation_of_eq h rfl

theorem ObservedTyped.bottom_empty_of_eq (h : ObservedTyped graph xi v t)
    (ht : t = .bottom) : False := by
  revert ht
  induction h with
  | ref r h ih => intro ht; exact ih ht
  | view h ih => intro ht; exact ih ht
  | unit => intro ht; cases ht
  | bool => intro ht; cases ht
  | int => intro ht; cases ht
  | floatBits => intro ht; cases ht
  | string => intro ht; cases ht
  | bytes => intro ht; cases ht
  | path => intro ht; cases ht
  | char => intro ht; cases ht
  | delay h => intro ht; cases ht
  | inLeft h => intro ht; cases ht
  | inRight h => intro ht; cases ht
  | both h k ih ik => intro ht; cases ht
  | top h ih => intro ht; cases ht
  | lambdaValue h k => intro ht; cases ht
  | lambdaComputation h k => intro ht; cases ht
  | wrap h i o ih => intro ht; cases ht

theorem ObservedTyped.bottom_empty (h : ObservedTyped graph xi v .bottom) : False :=
  h.bottom_empty_of_eq rfl

theorem bottom_empty (hg : WellTyped graph xi)
    (guard : GuardedValueGraph.Guarded (projectGraph graph))
    (h : ValueTyped xi emptyTy emptyContext v .bottom) : False :=
  (typed_observation hg guard h).bottom_empty

namespace ObservationExamples

def unitTy : Ty := .base .unit
def boolTy : Ty := .base .bool
def intTy : Ty := .base .int
def leftTy : Ty := .union unitTy boolTy
def rightTy : Ty := .union unitTy intTy
def intersectionTy : Ty := .intersection leftTy rightTy
def occurrence : ViewOccurrence := ⟨41, ⟨[43], .result, intersectionTy⟩⟩

/-- A real view/reference chain ending at evidence with two different union
typings of the SAME payload. Both premises survive observation and projection. -/
def chainGraph : Graph Bool
  | false => .view (.ref true) occurrence
  | true => .both (.inLeft .unit)
def chainTypes : Bool → Ty := fun _ => intersectionTy

theorem chain_typed : WellTyped chainGraph chainTypes := by
  intro r
  cases r with
  | false => exact .view (.ref true)
  | true => exact .both (.inLeft .unit) (.inLeft .unit)

def chainGuard : GuardedValueGraph.Guarded (projectGraph chainGraph) where
  rank := fun r => if r then 0 else 1
  ceiling := 2
  bound := by intro r; cases r <;> decide
  decrease := by
    intro r s h
    cases r <;> cases s <;>
      simp [projectGraph, projectNode, nextValue, frontier, chainGraph,
        GuardedValueGraph.Node.next] at h ⊢

theorem chain_observed : ObservedTyped chainGraph chainTypes (.ref false) intersectionTy :=
  typed_observation chain_typed chainGuard (.ref false)

theorem chain_both_supplied :
    ∃ w, Head chainGraph (.ref false) (.both w) ∧
      ValueTyped chainTypes emptyTy emptyContext w leftTy ∧
      ValueTyped chainTypes emptyTy emptyContext w rightTy :=
  intersection_observation chain_observed

def receipt : ReceiptTemplate := ⟨[], []⟩
def inner : Value Bool Empty := .lambda .value receipt unitTy unitTy unitTy
  (.ret (.var 0)) (.mk unitTy unitTy (.ret (.var 0)) [] [])
def input : Adapter Bool Empty := .mk boolTy unitTy (.ret .unit) [] []
def output : Adapter Bool Empty := .mk unitTy boolTy (.ret (.bool true)) [] []
def wrapped : Value Bool Empty := .wrap inner input output
def wrapGraph : Graph Bool := fun _ => wrapped
def wrapTypes : Bool → Ty := fun _ => .callable boolTy boolTy

theorem wrap_typed : WellTyped wrapGraph wrapTypes := fun _ =>
  .wrap (.lambdaValue (.ret (.var rfl)) (.mk (.ret (.var rfl))))
    (.mk (.ret .unit)) (.mk (.ret .bool))

def wrapGuard : GuardedValueGraph.Guarded (projectGraph wrapGraph) where
  rank := fun _ => 0
  ceiling := 1
  bound := fun _ => Nat.zero_lt_succ 0
  decrease := by intro r s h; cases h

theorem distinct_wrap_types :
    (Ty.callable unitTy unitTy) ≠ Ty.callable boolTy boolTy := by
  intro h
  cases h

theorem wrapped_observed : ObservedTyped wrapGraph wrapTypes (.ref false) (.callable boolTy boolTy) :=
  typed_observation wrap_typed wrapGuard (.ref false)

theorem wrapped_top_observed : ObservedTyped wrapGraph wrapTypes (.top (.ref false)) .top :=
  typed_observation wrap_typed wrapGuard (.top (.ref false))

/-- A genuine delayed recursive computation is admitted and observed finitely;
its body may execute forever. -/
def delayGraph : Graph (Fin 1) := fun _ => .delay (.force (.ref 0))
def delayTypes : Fin 1 → Ty := fun _ => .thunk unitTy

theorem delay_typed : WellTyped delayGraph delayTypes := fun _ => .delay (.force (.ref 0))

def delayGuard : GuardedValueGraph.Guarded (projectGraph delayGraph) where
  rank := fun _ => 0
  ceiling := 1
  bound := fun _ => Nat.zero_lt_succ 0
  decrease := by intro r s h; cases h

theorem cyclic_delay_observed : ObservedTyped delayGraph delayTypes (.ref 0) (.thunk unitTy) :=
  typed_observation delay_typed delayGuard (.ref 0)

end ObservationExamples

end YulangClosure.HigherOrderGraph
