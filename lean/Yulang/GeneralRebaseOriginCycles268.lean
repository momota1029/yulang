import Yulang.GeneralRebasePartialCycles268
import Yulang.GeneralRebaseMergedGate268

namespace Yulang.GeneralRebaseOriginCycles268
open GeneralNominalRecursiveInspection (Origin)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedCycles232 (Edge Path Cyclic)
open GeneralRebasePartialCycles268 (Walk Cycle evaluate evaluate_sound)
open GeneralRebasePartialBool268 (Answer Reflect both)

structure Window (n : Nat) where
 point : Fin n → Origin
 probe : Fin n → Fin n → Answer
 model : Answer

def NonemptyCycle (state : State roles) (o : Origin) : Prop :=
 ∃ next, Edge state o next ∧ Path state next o

def Closure (state : State roles) (w : Window n) (root : Fin n) : Prop :=
 NonemptyCycle state (w.point root) → Cycle (fun a b => Edge state (w.point a) (w.point b)) root

def Forward (state : State roles) (w : Window n) : Prop :=
 ∀ index origin, Edge state (w.point index) origin → ∃ next, w.point next = origin

structure Sound (state : State roles) (w : Window n) : Prop where
 edges : ∀ a b, Reflect (Edge state (w.point a) (w.point b)) (w.probe a b)
 model : Reflect (∃ model, Models state model) w.model

theorem mapped_path (w : Window n)
 (walk : Walk (fun a b => Edge state (w.point a) (w.point b)) first last) :
 Path state (w.point first) (w.point last) := by
 induction walk with
 | nil _ => exact .nil _
 | cons link _ ih => exact .cons link ih

theorem mapped_cycle (w : Window n) {root : Fin n}
 (small : Cycle (fun a b => Edge state (w.point a) (w.point b)) root) :
 NonemptyCycle state (w.point root) := by
 obtain ⟨next,edge,walk⟩ := small
 exact ⟨w.point next,edge,mapped_path w walk⟩

theorem lift_path (w : Window n) (forward : Forward state w) (injective : Function.Injective w.point)
 (path : Path state first last) (a b : Fin n) (start : w.point a = first) (finish : w.point b = last) :
 Walk (fun x y => Edge state (w.point x) (w.point y)) a b := by
 induction path generalizing a b with
 | nil =>
   have same := injective (start.trans finish.symm)
   cases same
   exact .nil _
 | cons edge _ ih =>
   obtain ⟨mid,next⟩ := forward a _ (start.symm ▸ edge)
   exact .cons (next.symm ▸ start.symm ▸ edge) (ih mid b next finish)

theorem closure_of_forward (w : Window n) (forward : Forward state w)
 (injective : Function.Injective w.point) (root : Fin n) : Closure state w root := by
 rintro ⟨next,edge,path⟩
 obtain ⟨index,atPoint⟩ := forward root next edge
 refine ⟨index,?_,lift_path w forward injective path index root atPoint rfl⟩
 change Edge state (w.point root) (w.point index)
 simpa only [atPoint] using edge

/-- Without coverage, the finite origin window only supplies positive evidence
for recurrence. Negative global model evidence can still exclude Cyclic. -/
def graph (w : Window n) (covered : Fin n → Bool) (i : Fin n) : Answer :=
 match evaluate w.probe i with
 | some true => some true
 | some false => if covered i then some false else none
 | none => none

theorem graph_sound (w : Window n) (sound : Sound state w) (covered : Fin n → Bool)
 (cover : ∀ i, covered i = true → Closure state w i) (i : Fin n) :
 Reflect (NonemptyCycle state (w.point i)) (graph w covered i) := by
 have checked := evaluate_sound _ w.probe sound.edges i
 unfold graph
 split
 · rename_i yes
   rw [yes] at checked
   exact mapped_cycle w checked
 · rename_i no
   rw [no] at checked
   split
   · rename_i enough
     exact fun candidate => checked (cover i enough candidate)
   · trivial
 · trivial

def cyclic (w : Window n) (covered : Fin n → Bool) (o : Origin) : Answer :=
 both ((List.finRange n).find? (fun i => decide (w.point i = o)) |>.bind (graph w covered)) w.model

theorem cyclic_sound (w : Window n) (sound : Sound state w) (covered : Fin n → Bool)
 (cover : ∀ i, covered i = true → Closure state w i) (o : Origin) :
 Reflect (Cyclic state o) (cyclic w covered o) := by
 apply GeneralRebasePartialBool268.both_sound _ sound.model
 cases h : (List.finRange n).find? (fun i => decide (w.point i = o)) with
 | none => exact True.intro
 | some i =>
   have same : w.point i = o := of_decide_eq_true (List.find?_some (p := fun i => decide (w.point i = o)) h)
   exact same ▸ graph_sound w sound covered cover i

end Yulang.GeneralRebaseOriginCycles268
