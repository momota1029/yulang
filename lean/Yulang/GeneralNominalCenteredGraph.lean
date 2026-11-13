import Yulang.GeneralNominalCenters
import Yulang.GeneralNominalSharedPump

/-! A finite recorded-test graph, closed under equality of actual names.
Semantic equality transports an edge; equality alone never creates an edge. -/
namespace Yulang.GeneralNominalCenteredGraph
open GeneralNominalRecursiveInspection (Origin Observes Test)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalOriginTerms (Same)
open CommonNominalFullCarrier

structure Journal where
  models : Assignment → Prop
  tests : List (Origin × Test)

def Equal (journal : Journal) (first last : Origin) : Prop :=
  ∀ model, journal.models model → Same model first last

inductive Recorded (journal : Journal) : Origin → Origin → Prop
  | structural (origin : Origin) (shape : GeneralNormalizedObservation.Shape)
      (index : Fin shape.arity) : (origin,.structural shape) ∈ journal.tests →
      Recorded journal origin (.structural origin shape index.val)
  | nominal (origin : Origin) (name arity : Nat) (index : Fin arity) :
      (origin,.nominal name arity) ∈ journal.tests →
      Recorded journal origin (.nominal origin name index.val)

def Edge (journal : Journal) (first last : Origin) : Prop :=
  ∃ parent child, Recorded journal parent child ∧ Equal journal first parent ∧ Equal journal child last

inductive Path (journal : Journal) : Origin → Origin → Prop
  | nil (origin) : Path journal origin origin
  | cons : Edge journal first middle → Path journal middle last → Path journal first last

def Cyclic (journal : Journal) (origin : Origin) : Prop :=
  (∃ next, Edge journal origin next ∧ Path journal next origin) ∧ ∃ model, journal.models model

theorem empty_acyclic (journal : Journal) (empty : journal.tests = []) (origin : Origin) :
    ¬ Cyclic journal origin := by
  rintro ⟨⟨next,⟨parent,child,recorded,_,_⟩,_⟩,_⟩
  cases recorded with
  | structural _ _ member => simp only [empty,List.not_mem_nil] at member
  | nominal _ _ _ member => simp only [empty,List.not_mem_nil] at member

theorem self_cycle (journal : Journal) (recorded : Recorded journal parent child)
    (parentEqual : Equal journal origin parent) (childEqual : Equal journal child origin)
    (inhabited : ∃ model, journal.models model) : Cyclic journal origin :=
  ⟨⟨origin,⟨parent,child,recorded,parentEqual,childEqual⟩,.nil _⟩,inhabited⟩

theorem source_equal (journal : Journal) (first last : Nat)
    (same : ∀ model, journal.models model → Equivalent (model first).1 (model last).1) :
    Equal journal (.source first) (.source last) := by
  intro model valid
  exact ⟨⟨_,.source _⟩,⟨_,.source _⟩,by intro a b one two; cases one; cases two; exact same model valid⟩

/-- The three W equalities plus the recorded output edge yield K2 at b.
Trace production remains separate; model inhabitation is a premise. -/
theorem trigger_k2 (journal : Journal) (a b next out : Nat)
    (equations : ∀ model, journal.models model →
      Equivalent (model a).1 (variant 0 (model b).1) ∧
      Equivalent (model a).1 (variant 0 (model next).1) ∧
      Equivalent (model next).1 (variant 0 (model b).1) ∧
      Equivalent (model out).1 (model a).1)
    (edge : Recorded journal (.source out) child)
    (shared : Equal journal child (.source b))
    (inhabited : ∃ model, journal.models model) : Cyclic journal (.source b) := by
  apply self_cycle journal edge ?_ shared inhabited
  apply source_equal
  intro model valid
  obtain ⟨one,two,three,output⟩ := equations model valid
  have cycle := GeneralNominalSharedPump.shared_round_cycle one two three
  exact ⟨subtype_trans cycle.1 (subtype_trans one.2 output.2),
    subtype_trans output.1 (subtype_trans one.1 cycle.2)⟩

end Yulang.GeneralNominalCenteredGraph
