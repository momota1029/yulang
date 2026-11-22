import Yulang.GeneralDeclarativeWitnessAuthWhole351

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessFreshness351
open GeneralDeclarativeWitnessIdentity351 (Stamp Key)
open GeneralDeclarativeWitnessCatalog351 (WriteAnchor)
open GeneralDeclarativeWitnessAuthForest351 (Problem)
open GeneralDeclarativeWitnessAuthWhole351 (Wire Accepted decode)
open GeneralDeclarativeWitnessForest350 (Fixed)
open GeneralDeclarativeWitnessTree349 (Report)
open GeneralDeclarativeWitnessProblem349 (splitAnd)

def position (stamp : Stamp) : List Nat × Nat := (stamp.path,stamp.role)

def liveStamp (active : List Stamp) (p : Problem) : Bool :=
  decide ((active.map position).Nodup) &&
    p.writer.required.all (fun w => active.contains w.producer)

theorem receipt_is_active {active : List Stamp} {p : Problem}
    (ok : liveStamp active p = true) {w : WriteAnchor} (used : w ∈ p.writer.required) :
    w.producer ∈ active :=
  (List.contains_iff_mem).mp (List.all_eq_true.mp (splitAnd ok).2 _ used)

theorem single_position {active : List Stamp} (unique : (active.map position).Nodup) {a b : Stamp}
    (left : a ∈ active) (right : b ∈ active) (same : position a = position b) : a = b := by
  induction active with
  | nil => cases left
  | cons head tail ih =>
    have ⟨miss,rest⟩ := List.nodup_cons.mp unique
    rcases List.mem_cons.mp left with rfl|inTail <;>
      rcases List.mem_cons.mp right with rfl|other
    · rfl
    · exact False.elim (miss (same.symm ▸ List.mem_map_of_mem (f := position) other))
    · exact False.elim (miss (same ▸ List.mem_map_of_mem (f := position) inTail))
    · exact ih rest inTail other

theorem unique_version {active : List Stamp} {p : Problem}
    (ok : liveStamp active p = true)
    {a b : WriteAnchor} (left : a ∈ p.writer.required) (right : b ∈ p.writer.required)
    (same : position a.producer = position b.producer) : a.producer.version = b.producer.version :=
  congrArg Stamp.version (single_position (of_decide_eq_true (splitAnd ok).1)
    (receipt_is_active ok left) (receipt_is_active ok right) same)

def distinctTrace (fs : List Fixed) : Bool := decide ((fs.map Fixed.path).Nodup)

/-- Independently check a single version per occurrence before accepting
a release-backed result. Even a well-formed ordinary row or an accepted
compiler result is not a second current incarnation of that occurrence. -/
def check (active : List Stamp) (p : Problem) (wire : Wire) (report : Report) : Bool :=
  if liveStamp active p then
    ((decode p wire report).map (fun a =>
      distinctTrace a.writer.producer.diagnostic.fixed && distinctTrace a.diagnostic.fixed)).getD false
  else false

theorem sound {active : List Stamp} {p : Problem} {w : Wire} {report : Report}
    (ok : check active p w report = true) :
    liveStamp active p = true ∧ ∃ a : Accepted p w report,
      (a.writer.producer.diagnostic.fixed.map Fixed.path).Nodup ∧ (a.diagnostic.fixed.map Fixed.path).Nodup := by
  unfold check at ok
  cases holds : liveStamp active p with
  | false => simp [holds] at ok
  | true =>
    cases found : decode p w report with
    | none => simp [holds,found] at ok
    | some a =>
      have both : (distinctTrace a.writer.producer.diagnostic.fixed && distinctTrace a.diagnostic.fixed) = true := by
        simpa [holds,found] using ok
      exact ⟨rfl,a,of_decide_eq_true (splitAnd both).1,of_decide_eq_true (splitAnd both).2⟩

end Yulang.GeneralDeclarativeWitnessFreshness351
