import Yulang.GeneralRebaseDirectCycles268
import Yulang.GeneralRebasePartialBool268

namespace Yulang.GeneralRebasePartialCycles268
open GeneralRebasePartialBool268 (Answer Reflect)

inductive Walk (edge : Fin n → Fin n → Prop) : Fin n → Fin n → Prop where
 | nil (node) : Walk edge node node
 | cons : edge first middle → Walk edge middle last → Walk edge first last

def Cycle (edge : Fin n → Fin n → Prop) (root : Fin n) : Prop :=
 ∃ child, edge root child ∧ Walk edge child root

theorem walk_mono {first last : Fin n → Fin n → Prop}
 (included : ∀ a b, first a b → last a b) (walk : Walk first a b) : Walk last a b := by
 induction walk with
 | nil _ => exact .nil _
 | cons h _ ih => exact .cons (included _ _ h) ih

theorem cycle_mono {first last : Fin n → Fin n → Prop}
 (included : ∀ a b, first a b → last a b) (cyclic : Cycle first root) : Cycle last root := by
 obtain ⟨child,edge,walk⟩ := cyclic
 exact ⟨child,included _ _ edge,walk_mono included walk⟩

def adj (decideEdge : Fin n → Fin n → Bool) (a : Fin n) : List (Fin n) :=
 (List.finRange n).filter (decideEdge a)

theorem adj_exact (decideEdge : Fin n → Fin n → Bool) (a b : Fin n) :
 b ∈ adj decideEdge a ↔ decideEdge a b = true := by simp [adj]

theorem walk_iff (decideEdge : Fin n → Fin n → Bool) (a b : Fin n) :
 FiniteWorklist.Path (adj decideEdge) a b ↔ Walk (fun x y => decideEdge x y = true) a b := by
 constructor <;> intro walk
 · induction walk with
   | nil _ => exact .nil _
   | cons edge _ ih => exact .cons ((adj_exact ..).mp edge) ih
 · induction walk with
   | nil _ => exact .nil _
   | cons edge _ ih => exact .cons ((adj_exact ..).mpr edge) ih

def check (decideEdge : Fin n → Fin n → Bool) (root : Fin n) : Bool :=
 (adj decideEdge root).any fun child =>
  decide (root ∈ FiniteWorklist.reachable (adj decideEdge) n child)

theorem check_iff (decideEdge : Fin n → Fin n → Bool) (root : Fin n) :
 check decideEdge root = true ↔ Cycle (fun x y => decideEdge x y = true) root := by
 have known (child : Fin n) : root ∈ FiniteWorklist.reachable (adj decideEdge) n child ↔
   Walk (fun x y => decideEdge x y = true) child root :=
   (FiniteWorklist.reachable_exact (adj decideEdge) n (List.finRange n) (by simp) (by simp) child root).trans
    (walk_iff decideEdge child root)
 simp only [check,Cycle,List.any_eq_true,decide_eq_true_eq,adj_exact,known]

def lower (probe : Fin n → Fin n → Answer) (a b : Fin n) : Bool :=
 probe a b == some true

def upper (probe : Fin n → Fin n → Answer) (a b : Fin n) : Bool :=
 !(probe a b == some false)

theorem lower_sound (edge : Fin n → Fin n → Prop) (probe : Fin n → Fin n → Answer)
 (cert : ∀ a b, Reflect (edge a b) (probe a b)) (a b : Fin n) (seen : lower probe a b = true) : edge a b := by
 have eq : probe a b = some true := by simpa [lower] using seen
 have sound := cert a b
 rw [eq] at sound
 exact sound

theorem upper_sound (edge : Fin n → Fin n → Prop) (probe : Fin n → Fin n → Answer)
 (cert : ∀ a b, Reflect (edge a b) (probe a b)) (a b : Fin n) (actual : edge a b) : upper probe a b = true := by
 have notFalse : probe a b ≠ some false := by
   intro eq
   have sound := cert a b
   rw [eq] at sound
   exact sound actual
 simp [upper,notFalse]

def evaluate (probe : Fin n → Fin n → Answer) (root : Fin n) : Answer :=
 if check (lower probe) root then some true else
   if check (upper probe) root then none else some false

theorem evaluate_sound (edge : Fin n → Fin n → Prop) (probe : Fin n → Fin n → Answer)
 (cert : ∀ a b, Reflect (edge a b) (probe a b)) (root : Fin n) :
 Reflect (Cycle edge root) (evaluate probe root) := by
 unfold evaluate
 split
 · rename_i lowerCycle
   exact cycle_mono (lower_sound edge probe cert) ((check_iff ..).mp lowerCycle)
 · split
   · trivial
   · rename_i upperNo
     exact fun actual => upperNo ((check_iff ..).mpr (cycle_mono (upper_sound edge probe cert) actual))

theorem evaluate_total (probe : Fin n → Fin n → Answer) (total : ∀ a b, probe a b ≠ none)
 (root : Fin n) : evaluate probe root ≠ none := by
 have same : lower probe = upper probe := by
   funext a b
   cases recorded : probe a b with
   | none => exact False.elim (total a b recorded)
   | some value => cases value <;> simp [lower,upper,recorded]
 cases h : check (upper probe) root <;> simp [evaluate,same,h]

end Yulang.GeneralRebasePartialCycles268
