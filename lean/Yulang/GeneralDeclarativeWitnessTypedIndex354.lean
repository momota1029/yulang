import Yulang.GeneralDeclarativeWitnessTypedScope354
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessTypedIndex354
open GeneralDeclarativeWitnessTypedOutput354 (Batch Item)
open GeneralDeclarativeWitnessTypedPacket354 (At typedAt)
open GeneralDeclarativeWitnessTypedRelease354 (Released address Stamp position)
open GeneralDeclarativeWitnessTypedForest354 (Leaf)
open GeneralDeclarativeWitnessTypedChild354 (physical_target)

/-- Every typed item in the true producer trace has an exact-index lookup.
This statement covers one finite output batch, not certificate or solver completeness. -/
theorem typedAt_defined {p c input outs} (b : Batch p c input outs) (i : Nat) {row}
    (h : b.trace[i]? = some (.typed row)) : (typedAt b i).isSome = true := by
  induction b generalizing i with
  | nil => simp [Batch.trace] at h
  | cons first tail ih =>
    cases i with
    | zero =>
      cases first with
      | ordinary _ _ => cases h
      | nominal _ => rfl
    | succ i =>
      cases first <;> simpa only [typedAt,Option.isSome_map] using ih i h

theorem trace_index {p c input outs} (b : Batch p c input outs) (i : Nat) {r}
    (_found : typedAt b i = some r) {row} (h : b.trace[i]? = some (.typed row)) :
    r.1.typed.row = row := by
  have hit := Option.some.inj (r.2.symm.trans h)
  exact GeneralDeclarativeWitnessTypedOutput354.Write.typed.inj hit

theorem unique_position {active : List Stamp} (distinct : (active.map position).Nodup)
    {x y : Stamp} (left : x ∈ active) (right : y ∈ active) (same : position x = position y) : x = y := by
  induction active with
  | nil => cases left
  | cons top more ih =>
    change (position top :: more.map position).Nodup at distinct
    have both := List.nodup_cons.mp distinct
    rcases List.mem_cons.mp left with rfl|lt <;> rcases List.mem_cons.mp right with rfl|rt
    · rfl
    · exact False.elim (both.1 (same.symm ▸ List.mem_map_of_mem rt))
    · exact False.elim (both.1 (same ▸ List.mem_map_of_mem lt))
    · exact ih both.2 lt rt

theorem released_version_unique {p w s report}
    {a : GeneralDeclarativeWitnessTypedPacket354.Accepted p w s report} {loc u i}
    (b : Released a loc u i) {other : Stamp}
    (declared : other ∈ u.active)
    (identified : position other = position (GeneralDeclarativeWitnessTypedRelease354.stamp a loc)) :
    other = GeneralDeclarativeWitnessTypedRelease354.stamp a loc := by
  exact unique_position b.distinct declared b.active identified

theorem inspect_other_exact_child_target {p s w i d}
    (a b : Leaf p s w i d)
    (sameCenter : a.linked.receiver.facts.arg.center = b.linked.receiver.facts.arg.center) :
    (address a.linked.writer p.location a.plan.writtenOrdinal a.linked.emitted.atWrite.demand).target =
    (address b.linked.writer p.location b.plan.writtenOrdinal b.linked.emitted.atWrite.demand).target := by
  exact (physical_target a.linked).symm.trans (sameCenter.trans (physical_target b.linked))

end Yulang.GeneralDeclarativeWitnessTypedIndex354
