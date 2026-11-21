import Yulang.GeneralDeclarativeLowerKnown321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeK2Graph321
open GeneralDeclarativeLowerKnown321 (Alias alias_refl alias_symm)
open GeneralDeclarativeHead320 (State Equation)
open GeneralNominalCenteredHeadMatExpressions (Expr)

def arguments (args : List Expr) : Option (List Nat) :=
  match args with
  | [] => some []
  | .variable n :: rest => (arguments rest).map (n :: ·)
  | _ :: _ => none

/-- Constructor application with normalized named operands. Row tail links
must already have been flattened; they are not recursive payload descent. -/
inductive Shape where
  | primitive (tag : GeneralCandidateInspection.Primitive) (children : List Nat)
  | nominal (tag : Nat) (children : List Nat)
  | record (payloads : List (Nat × Nat))
  | variant (tag payload : Nat)

def Shape.children : Shape → List Nat
  | .primitive _ args | .nominal _ args => args
  | .record fields => fields.map Prod.snd
  | .variant _ payload => [payload]

/-- A certified normalized observation interface for logical names. It does
not postulate which candidate wins or any dictionary evidence. The normalizer
still has to justify that its relation describes the complete source view. -/
def View := Nat → Shape → Prop

def Descends (view : View) (a b : Nat) : Prop :=
  ∃ shape, view a shape ∧ b ∈ shape.children

inductive Path (view : View) : Nat → Nat → Prop where
  | refl (a : Nat) : Path view a a
  | next : Descends view a b → Path view b c → Path view a c

def OnCycle (view : View) (root : Nat) : Prop :=
  ∃ child, Descends view root child ∧ Path view child root

/-- Closing normalized observations under ordinary aliases is a logical-name
operation. Alias steps alone are never structural descent. -/
def aliasView (s : State) (view : View) : View :=
  fun a shape => ∃ source, Alias s a source ∧ view source shape

theorem edge_transport {s : State} {view : View} (same : Alias s a b)
    (step : Descends (aliasView s view) b c) : Descends (aliasView s view) a c := by
  obtain ⟨shape,⟨source,other,seen⟩,child⟩ := step
  exact ⟨shape,⟨source,.trans same other,seen⟩,child⟩

/-- Concatenation does not turn a cyclic descendant into a cyclic ancestor:
the last endpoint must actually come back to the chosen logical root. -/
theorem path_cat {view : View} (one : Path view a b) (two : Path view b c) : Path view a c := by
  induction one with
  | refl => exact two
  | next edge _ ih => exact .next edge (ih two)

theorem close_cycle {view : View} (into : Descends view a b) (back : Path view b a) :
    OnCycle view a := ⟨b,into,back⟩

theorem no_children_no_cycle {view : View} (noEdge : ∀ child, ¬Descends view root child) :
    ¬OnCycle view root := fun ⟨child,edge,_⟩ => noEdge child edge

theorem closed_cycle_add_edges {view enlarged : View}
    (more : ∀ a head, view a head → enlarged a head) (cycle : OnCycle view root) :
    OnCycle enlarged root := by
  have liftEdge : ∀ x y, Descends view x y → Descends enlarged x y := by
    rintro x y ⟨head,p,there⟩
    exact ⟨head,more x head p,there⟩
  have liftPath : ∀ x y, Path view x y → Path enlarged x y := by
    intro x y path
    induction path with
    | refl => exact .refl _
    | next edge _ ih => exact .next (liftEdge _ _ edge) ih
  obtain ⟨child,first,rest⟩ := cycle
  exact ⟨child,liftEdge _ _ first,liftPath _ _ rest⟩

end Yulang.GeneralDeclarativeK2Graph321
