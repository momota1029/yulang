import Yulang.GeneralDeclarativeEndpointNames336
import Yulang.GeneralDeclarativeGrowth327

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeEndpointBatch336
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeWhere319 (Capture InInterval)
open GeneralDeclarativeCaptureClosure320 (withOrdinary atoms ordinary_models)
open GeneralDeclarativeFootprint321 (stateNames preserves_models)
open GeneralDeclarativeNewNames321 (after before_after)
open GeneralDeclarativeEndpointNames336 (Triple)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty Subtype)

def base (s : State) (protect : List Nat) : Nat := after (stateNames s ++ protect)

def slots (s : State) (protect : List Nat) (j : Nat) : Capture :=
  let lo := base s protect + 3*j
  ⟨lo,lo+1,lo+2⟩

def prepare (s : State) (protect : List Nat) (count : Nat) : State :=
  withOrdinary s ((List.range count).flatMap (fun j => atoms (slots s protect j)))

def patch (s : State) (protect : List Nat) (vals : List Triple) (m : Assignment) : Assignment :=
  fun n => if base s protect ≤ n then
    let diff := n - base s protect
    match vals[diff / 3]? with
    | none => m n
    | some v => (if diff % 3 = 0 then v.1 else if diff % 3 = 1 then v.2.1 else v.2.2, (m n).2)
  else m n

theorem preserves {s : State} {protect : List Nat} (vals) (m) (n : Nat)
    (present : n ∈ stateNames s ++ protect) : patch s protect vals m n = m n := by
  have lt : n < base s protect := before_after present
  simp [patch,Nat.not_le_of_lt lt]

def atSlots (m : Assignment) (c : Capture) : Triple :=
  ((m c.lower).1,(m c.center).1,(m c.upper).1)

theorem patch_values {vals : List Triple} (stored : vals[j]? = some v) :
    atSlots (patch s protect vals m) (slots s protect j) = v := by
  let k := base s protect
  have arith (r : Nat) (small : r < 3) :
      k ≤ k+3*j+r ∧ (k+3*j+r-k)/3 = j ∧ (k+3*j+r-k)%3 = r := by omega
  have written (r : Nat) (small : r < 3) :
      (patch s protect vals m (k+3*j+r)).1 = (if r = 0 then v.1 else if r = 1 then v.2.1 else v.2.2) := by
    obtain ⟨le,idx,offset⟩ := arith r small
    simp only [patch,show base s protect = k from rfl,le,ite_true,idx,stored,offset]
  have x := written 0 (by decide)
  have y := written 1 (by decide)
  have z := written 2 (by decide)
  change ((patch s protect vals m (k+3*j+0)).1,
    (patch s protect vals m (k+3*j+1)).1,(patch s protect vals m (k+3*j+2)).1) = v
  rw [x,y,z]
  cases v <;> rfl

theorem bound {n j : Nat} (idx : j < n) : Bounds (prepare s keep n) (slots s keep j) := by
  let c := slots s keep j
  have add {e} (found : e ∈ atoms c) :
      e ∈ (prepare s keep n).normal.ordinary :=
    List.mem_append_right _ (List.mem_flatMap.mpr ⟨j,List.mem_range.mpr idx,found⟩)
  exact ⟨.constraint (add List.mem_cons_self),
    .constraint (add (List.mem_cons_of_mem _ List.mem_cons_self))⟩

theorem grows (s : State) (keep : List Nat) (n : Nat) :
    GeneralDeclarativeGrowth327.Extends s (prepare s keep n) :=
  GeneralDeclarativeGrowth327.ordinary _ _

/-- A whole finite interval batch can be named without changing any
old type, row, actual root or fixed target. This is before the ordinary
compiler's selected I-58 equalities and output writes, which need not
be conservative. -/
theorem fit {s : State} (old : Models s m) (keep : List Nat) (vals : List Triple)
    (valid : ∀ v ∈ vals, InInterval v.1 v.2.2 v.2.1) :
    Models (prepare s keep vals.length) (patch s keep vals m) := by
  let n := patch s keep vals m
  apply (ordinary_models n).mpr
  refine ⟨(preserves_models s
    (fun x has => preserves vals m x (List.mem_append_left keep has))).mpr old,?_⟩
  intro atom used
  obtain ⟨j,active,part⟩ := List.mem_flatMap.mp used
  have index := List.mem_range.mp active
  let v := vals[j]
  have entry : vals[j]? = some v := List.getElem?_eq_getElem index
  have works := valid v (List.getElem_mem index)
  have all := patch_values (s := s) (protect := keep) (m := m) entry
  have a : (n (slots s keep j).lower).1 = v.1 := congrArg Prod.fst all
  have b : (n (slots s keep j).center).1 = v.2.1 := congrArg (fun x : Triple => x.2.1) all
  have c : (n (slots s keep j).upper).1 = v.2.2 := congrArg (fun x : Triple => x.2.2) all
  simp only [atoms,List.mem_cons,List.not_mem_nil,or_false] at part
  rcases part with rfl|rfl
  · change Subtype (n (slots s keep j).lower).1 (n (slots s keep j).center).1
    exact a.symm ▸ b.symm ▸ works.1
  · change Subtype (n (slots s keep j).center).1 (n (slots s keep j).upper).1
    exact b.symm ▸ c.symm ▸ works.2

end Yulang.GeneralDeclarativeEndpointBatch336
