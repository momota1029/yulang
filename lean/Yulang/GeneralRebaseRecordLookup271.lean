import Yulang.GeneralNominalRecordInversion
import Yulang.CommonNominalFinitePresence

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseRecordLookup271
open CommonNominalFullCarrier
open GeneralNominalStructuralReadback (recordValues)
open CommonNominalFullDemand (ProbeAt Environment Observation)

def first (label : Nat) : List (Nat × α) → Option α
 | [] => none
 | (name,value)::rest => if label = name then some value else first label rest

theorem field (xs : List (Nat × Ty)) (label depth rank : Nat) (env : Environment Row)
 (obs : Observation Row) :
 ProbeAt Common.rowLe rank env (observeTy (depth+1) (recordValues xs)) (.field label obs) ↔
 match first label xs with
 | none => False
 | some value => ProbeAt Common.rowLe rank env (observeTy depth value) obs := by
 induction xs with
 | nil => cases rank <;> rfl
 | cons head tail ih =>
   obtain ⟨k,v⟩ := head
   change ProbeAt Common.rowLe rank env (.record k (observeTy depth v)
     (observeTy (depth+1) (recordValues tail))) (.field label obs) ↔ _
   rw [CommonNominalFullDemand.probeAt_record_field]
   by_cases eq : label = k <;> simp only [first,eq,ite_true,ite_false,ih]

theorem payload (xs ys : List (Nat × Ty)) (label : Nat) (a b : Ty)
 (knownA : first label xs = some a) (knownB : first label ys = some b)
 (model : Equivalent (recordValues xs) (recordValues ys)) : Equivalent a b := by
 have implies (x y : List (Nat × Ty)) (u v : Ty)
   (one : first label x = some u) (two : first label y = some v)
   (below : Subtype (recordValues x) (recordValues y)) : Subtype u v := by
   intro depth
   apply (CommonNominalFullDemand.producerLe_iff_probe _ _).mpr
   intro rank env obs accepted
   have px := field x label depth rank env obs
   have py := field y label depth rank env obs
   rw [one] at px
   rw [two] at py
   apply px.mp
   exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below (depth+1)) rank env (.field label obs)
     (py.mpr accepted)
 exact ⟨implies xs ys a b knownA knownB model.1,implies ys xs b a knownB knownA model.2⟩

theorem exists_first (xs : List (Nat × α)) (label : Nat) :
 (∃ x, first label xs = some x) ↔ label ∈ xs.map Prod.fst := by
 induction xs with
 | nil => simp [first]
 | cons item rest ih =>
   obtain ⟨key,val⟩ := item
   by_cases eq : label = key
   · simp [first,eq]
   · simpa [first,eq] using ih

end Yulang.GeneralRebaseRecordLookup271
