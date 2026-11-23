import Yulang.GeneralDeclarativeWitnessNativeKinds361
import Yulang.GeneralDeclarativeWitnessNativeLowerCut361

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 59000
set_option maxHeartbeats 57000000
namespace Yulang.GeneralDeclarativeWitnessMixedDependency361
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeTraceNames321 (names)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeTaggedElection340 (Ranked level)
open GeneralDeclarativeWitnessRank350 (rank check sound)
open GeneralDeclarativeWitnessNativeInstall360 (Board World)
open GeneralDeclarativeWitnessNativeValue360 (Code)
open GeneralDeclarativeWitnessNativeLowerCut361 (levels rankBefore actual_rank)
open GeneralDeclarativeWitnessReleasedForward360 (originalBody)
open GeneralDeclarativeWitnessSequentialNative360 (Sequence sequence)
open GeneralDeclarativeWitnessNestedInstall360 (Run)

def reads : Code → List Nat
  | .leaf name => [name]
  | .nullary _ => []
  | .unary _ inner => reads inner

inductive Node where
  | ordinary (name : Nat)
  | native (target : Nat)
  | projected (portName : Nat)
  deriving DecidableEq

/-- The finite typed Code is collapsed to its ordinary leaf uses. Port
readback observes a native write; there is no ordinary-to-native edge
even when the numerical addresses coincide. This is the declared
reference projection, not a complete model of the raw engine graph. -/
inductive Edge (w : World) (projection : Nat → Nat → Prop) : Bool → Node → Node → Prop where
  | alias : Alias w.ordinary a b → Edge w projection false (.ordinary a) (.ordinary b)
  | structure_ {row : Equation} : row ∈ w.ordinary.equations →
      (∀ n,row.right ≠ .variable n) → n ∈ names row.right →
      Edge w projection true (.ordinary row.left) (.ordinary n)
  | writer : row ∈ w.board.writes → n ∈ reads row.code →
      Edge w projection true (.native row.address.target) (.ordinary n)
  | projected : projection name target → Edge w projection false (.projected name) (.native target)

inductive Path (w : World) (projection : Nat → Nat → Prop) : Bool → Node → Node → Prop where
  | done : Path w projection false x x
  | more : Edge w projection first x y → Path w projection rest y z → Path w projection (first || rest) x z

def height (r : Nat → Nat) (cap : Nat) : Node → Nat
  | .ordinary name => r name
  | .native _ | .projected _ => cap

def Within (w : World) (r : Nat → Nat) (cap : Nat) : Prop :=
  ∀ row ∈ w.board.writes,∀ n ∈ reads row.code,r n < cap

theorem edge_height {w : World} {projection r cap strict start end_}
    (base : Ranked w.ordinary r) (whereRead : Within w r cap)
    (edge : Edge w projection strict start end_) :
    height r cap end_ ≤ height r cap start ∧ (strict = true → height r cap end_ < height r cap start) := by
  cases edge with
  | alias h => exact ⟨Nat.le_of_eq (level base h).symm,by simp⟩
  | structure_ haveRow compound use =>
    have step := base.compound _ haveRow _ use compound
    exact ⟨Nat.le_of_lt step,fun _ => step⟩
  | writer written use =>
    have step := whereRead _ written _ use
    exact ⟨Nat.le_of_lt step,fun _ => step⟩
  | projected _ => exact ⟨Nat.le_refl _,by simp⟩

theorem path_height {w : World} {projection r cap strict start end_}
    (base : Ranked w.ordinary r) (whereRead : Within w r cap)
    (path : Path w projection strict start end_) :
    height r cap end_ ≤ height r cap start ∧ (strict = true → height r cap end_ < height r cap start) := by
  induction path with
  | done => exact ⟨Nat.le_refl _,by simp⟩
  | more first _ ih =>
    obtain ⟨be,sharp⟩ := edge_height base whereRead first
    refine ⟨Nat.le_trans ih.1 be,?_⟩
    intro desired
    rcases Bool.or_eq_true_iff.mp desired with left|right
    · exact Nat.lt_of_le_of_lt ih.1 (sharp left)
    · exact Nat.lt_of_lt_of_le (ih.2 right) be

theorem no_strict_loop {w : World} {projection r cap} (base : Ranked w.ordinary r)
    (whereRead : Within w r cap) (n : Node) :
    ¬ Path w projection true n n :=
  fun loop => Nat.lt_irrefl _ ((path_height base whereRead loop).2 rfl)

def boardCheck (w : World) (r : Nat → Nat) (cap : Nat) : Bool :=
  w.board.writes.all fun row => (reads row.code).all fun n => decide (r n < cap)

theorem board_checked {w : World} {r cap} (ok : boardCheck w r cap = true) : Within w r cap := by
  intro row written n there
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp ok _ written) _ there)

def exactGraph {negative r} (s : @Sequence negative r) : Bool :=
  rankBefore s && boardCheck s.final (rank levels) 2

theorem actual_graph (negative : Bool) :
    ((originalBody negative).bind fun r => (sequence r).map exactGraph).getD false = true := by
  cases negative <;> decide +kernel

theorem actual_graph_has_no_strict_loop {negative} {r : Run negative} {s : Sequence r}
    (root : originalBody negative = some r) (sent : sequence r = some s) (projection) (n : Node) :
    ¬ Path s.final projection true n n := by
  have h := actual_graph negative
  rw [root] at h
  change ((sequence r).map exactGraph).getD false = true at h
  rw [sent] at h
  obtain ⟨ranked,board⟩ := Bool.and_eq_true_iff.mp (show exactGraph s = true from h)
  exact no_strict_loop (sound ranked) (board_checked board) n

end Yulang.GeneralDeclarativeWitnessMixedDependency361
