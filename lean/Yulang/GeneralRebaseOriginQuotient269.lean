import Yulang.GeneralRebaseOriginCongruence269
import Yulang.GeneralRebaseOriginCycles268

namespace Yulang.GeneralRebaseOriginQuotient269
open GeneralNominalRecursiveInspection (Origin Test)
open GeneralNominalOriginTerms (arity project)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedCycles232 (Edge Path Equal Head)
open GeneralRebaseOriginCongruence269 (equal_symm equal_trans self_left self_right edge_of_equiv edge_normal edge_right_live)
open GeneralRebasePartialCycles268 (Walk Cycle)
open GeneralRebaseOriginCycles268 (Window NonemptyCycle Closure)

def Forward (state : State roles) (point : Fin n → Origin) : Prop :=
 ∀ i target, Edge state (point i) target → ∃ j, Equal state target (point j)

def Pos (edge : Fin n → Fin n → Prop) (first last : Fin n) : Prop :=
 ∃ middle, edge first middle ∧ Walk edge middle last

theorem to_walk {edge : Fin n → Fin n → Prop} (positive : Pos edge a b) : Walk edge a b := by
 obtain ⟨next,edge,tail⟩ := positive
 exact .cons edge tail

/-- Lift a nonempty path with prescribed endpoints. The last edge is
retargeted to the requested representative. No injectivity premise nor
conversion of a zero-length path between different indices is needed. -/
theorem lift_positive (state : State roles) (point : Fin n → Origin) (forward : Forward state point)
 {middle last : Origin} (trace : Path state middle last)
 {before : Origin} (incoming : Edge state before middle)
 {a b : Fin n} (atStart : Equal state before (point a)) (atEnd : Equal state last (point b)) :
 Pos (fun i j => Edge state (point i) (point j)) a b := by
 induction trace generalizing before a b with
 | nil _ =>
   exact ⟨b,edge_of_equiv atStart atEnd incoming,.nil _⟩
 | @cons current next finish outgoing _ ih =>
   have anchored := edge_of_equiv atStart (edge_right_live incoming) incoming
   obtain ⟨stepIndex,rep⟩ := forward a current anchored
   exact ⟨stepIndex,edge_of_equiv atStart rep incoming,to_walk (ih outgoing rep atEnd)⟩

theorem short_closure (state : State roles) (window : Window n)
 (forward : Forward state window.point) (i : Fin n) : Closure state window i := by
 rintro ⟨next,edge,trail⟩
 exact lift_positive state window.point forward trail edge
   (GeneralRebaseOriginCongruence269.edge_left_live edge) (GeneralRebaseOriginCongruence269.edge_left_live edge)

theorem mapped_positive (state : State roles) (window : Window n)
 (trace : Pos (fun i j => Edge state (window.point i) (window.point j)) a b) :
 ∃ next, Edge state (window.point a) next ∧ Path state next (window.point b) := by
 obtain ⟨next,edge,tail⟩ := trace
 exact ⟨window.point next,edge,GeneralRebaseOriginCycles268.mapped_path window tail⟩

theorem retarget_positive (state : State roles) (trace : Path state middle last)
 (incoming : Edge state original middle) (atStart : Equal state original newStart)
 (atEnd : Equal state last newEnd) :
 ∃ next, Edge state newStart next ∧ Path state next newEnd := by
 induction trace generalizing original newStart with
 | nil _ => exact ⟨newEnd,edge_of_equiv atStart atEnd incoming,.nil _⟩
 | @cons current next finish edge _ ih =>
   have live := edge_right_live incoming
   obtain ⟨next,advance,path⟩ := ih edge live atEnd
   exact ⟨current,edge_of_equiv atStart live incoming,.cons advance path⟩

theorem nonempty_cycle_iff (state : State roles) (representative : Equal state origin point) :
 NonemptyCycle state origin ↔ NonemptyCycle state point := by
 constructor
 · rintro ⟨_,edge,tail⟩
   exact retarget_positive state tail edge representative representative
 · rintro ⟨_,edge,tail⟩
   exact retarget_positive state tail edge (equal_symm representative) (equal_symm representative)

theorem complete_window (state : State roles) (window : Window n)
 (forward : Forward state window.point) (root : Fin n) (o : Origin) (matched : Equal state o (window.point root)) :
 Cycle (fun i j => Edge state (window.point i) (window.point j)) root ↔ NonemptyCycle state o :=
 ⟨fun bounded => (nonempty_cycle_iff state matched).mpr (GeneralRebaseOriginCycles268.mapped_cycle window bounded),
  fun original => short_closure state window forward root ((nonempty_cycle_iff state matched).mp original)⟩

/-- Retain only actual constructor heads at each existing representative;
the coverage proof is semantic, not a bounded depth heuristic. -/
structure TestsCover (state : State roles) (point : Fin n → Origin) (tests : Fin n → List Test) : Prop where
 allHeads : ∀ a t, Equal state (point a) (point a) → Head state (point a) t → arity t ≠ 0 → t ∈ tests a
 child : ∀ a t, t ∈ tests a → ∀ i : Fin (arity t),
   Equal state (point a) (point a) → Head state (point a) t →
   (∃ other, Equal state (project (point a) t i) other) →
   ∃ b, Equal state (project (point a) t i) (point b)

theorem forward_of_tests (state : State roles) (point : Fin n → Origin) (tests : Fin n → List Test)
 (cover : TestsCover state point tests) : Forward state point := by
 intro a target edge
 obtain ⟨live,t,i,head,matchTarget⟩ := (edge_normal state _ _).mp edge
 have positive : arity t ≠ 0 := fun zero => Nat.not_lt_zero i.val (zero ▸ i.isLt)
 obtain ⟨b,rep⟩ := cover.child a t (cover.allHeads a t live head positive) i live head ⟨target,matchTarget⟩
 exact ⟨b,equal_trans (equal_symm matchTarget) rep⟩

end Yulang.GeneralRebaseOriginQuotient269
