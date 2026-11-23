import Yulang.GeneralDeclarativeWitnessBackedNativeInput363
import Yulang.GeneralDeclarativeWitnessRank350

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessNonpointGraph363
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeTraceNames321 (names)
open GeneralDeclarativeTaggedElection340 (Ranked level)
open GeneralDeclarativeWitnessRank350 (rank check sound)
open GeneralDeclarativeWitnessNativeInstall360 (World)
open GeneralDeclarativeWitnessNativeValue360 (Code)

def uses : Code → List Nat
  | .leaf n => [n]
  | .nullary _ => []
  | .unary _ c => uses c

inductive Node where
  | ordinary (name : Nat)
  | native (address : Nat)
  | occurrence (address : Nat)
  deriving DecidableEq

/-- The supported projection keeps native and ordinary coordinates
distinct, even at the same numeral. Code is finite syntax; only its
ordinary leaves are read. There is no ordinary-to-native reference
in this carrier. The graph is not a completeness claim about Rust. -/
inductive Edge (w : World) (project : Nat → Nat → Prop) : Bool → Node → Node → Prop where
  | aliases : Alias w.ordinary a b → Edge w project false (.ordinary a) (.ordinary b)
  | structure_ {eq : Equation} : eq ∈ w.ordinary.equations → (∀ v,eq.right ≠ .variable v) →
      n ∈ names eq.right → Edge w project true (.ordinary eq.left) (.ordinary n)
  | released : row ∈ w.board.writes → n ∈ uses row.code →
      Edge w project true (.native row.address.target) (.ordinary n)
  | linked : project n target → Edge w project false (.occurrence n) (.native target)

inductive Walk (w : World) (project : Nat → Nat → Prop) : Bool → Node → Node → Prop where
  | empty : Walk w project false n n
  | cons : Edge w project sharp a b → Walk w project tail b c → Walk w project (sharp || tail) a c

def heights (r : Nat → Nat) : Node → Nat
  | .ordinary n => r n
  | _ => 3

def NativeBounds (w : World) (r : Nat → Nat) : Prop :=
  ∀ a ∈ w.board.writes,∀ n ∈ uses a.code,r n < 3

theorem edges_respect_levels {w : World} {p r strict a b}
    (ordinary : Ranked w.ordinary r) (native : NativeBounds w r)
    (edge : Edge w p strict a b) :
    heights r b ≤ heights r a ∧ (strict = true → heights r b < heights r a) := by
  cases edge with
  | aliases h => exact ⟨Nat.le_of_eq (level ordinary h).symm,by simp⟩
  | structure_ chosen real there =>
    have step := ordinary.compound _ chosen _ there real
    exact ⟨Nat.le_of_lt step,fun _ => step⟩
  | released written used =>
    have step := native _ written _ used
    exact ⟨Nat.le_of_lt step,fun _ => step⟩
  | linked _ => exact ⟨Nat.le_refl _,by simp⟩

theorem no_loop {w : World} {p r} (ordinary : Ranked w.ordinary r) (native : NativeBounds w r)
    (a : Node) : ¬Walk w p true a a := by
  have decreases {z t strict} (path : Walk w p strict z t) :
      heights r t ≤ heights r z ∧ (strict = true → heights r t < heights r z) := by
    induction path with
    | empty => exact ⟨Nat.le_refl _,by simp⟩
    | cons e _ ih =>
      obtain ⟨before,strict⟩ := edges_respect_levels ordinary native e
      refine ⟨Nat.le_trans ih.1 before,?_⟩
      intro yes
      rcases Bool.or_eq_true_iff.mp yes with x|y
      · exact Nat.lt_of_le_of_lt ih.1 (strict x)
      · exact Nat.lt_of_lt_of_le (ih.2 y) before
  intro cycle
  exact Nat.lt_irrefl _ ((decreases cycle).2 rfl)

def levels : List Nat := (List.range 324).map fun n =>
  if n < 4 then 0 else if n = 63 ∨ n = 64 then 1 else 2

def graph (w : World) : Bool :=
  check w.ordinary levels &&
  w.board.writes.all (fun z => (uses z.code).all (fun n => decide (rank levels n < 3)))

structure Safe (w : World) : Prop where
  ordinary : Ranked w.ordinary (rank levels)
  projected : ∀ links n,¬Walk w links true n n

theorem graph_exact_positive {w : World} (found : graph w = true) : Safe w := by
  obtain ⟨ordinary,natives⟩ := Bool.and_eq_true_iff.mp found
  have checked := sound ordinary
  have bounds : NativeBounds w (rank levels) := by
    intro row stored n use
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp natives _ stored) _ use)
  exact ⟨checked,fun _ => no_loop checked bounds⟩

end Yulang.GeneralDeclarativeWitnessNonpointGraph363
