import Yulang.GeneralWhereOriginBatch318

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 26000000
namespace Yulang.GeneralWhereOriginReservation318
open GeneralWhereOriginSupport318 (planSources journalSources)
open GeneralWhereOriginDelta318 (Cell Delta)
open GeneralWhereOriginTrace318 (rawOf)
open GeneralWhereVersionInstall317 (Journal)
open GeneralNominalCenteredHeadMatSchemas (Equation)
open GeneralNominalVersionedExpressionFrame236 (schemaSources equationSources)
open GeneralWhereVersionCompiler317 (schema)
open GeneralDictionaryBinderLocations (sourceSlot sourceSlot_exact)

theorem recorded_target {j : Journal rs} {p : GeneralNominalCenters.Plan rs}
    (history : p ∈ j.versionedWhere) {e : Equation}
    (emitted : e ∈ (schema p).equations) : e.target ∈ journalSources j := by
  have mentions : e.target ∈ schemaSources p (schema p) :=
    List.mem_flatMap.mpr ⟨e,emitted,List.mem_cons_self⟩
  have exposed : e.target ∈ planSources p := by
    simp [planSources,mentions]
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨p,history,List.mem_append_left _ exposed⟩)

theorem cannot_write_after_record {j : Journal rs} {p : GeneralNominalCenters.Plan rs}
    (history : p ∈ j.versionedWhere) (cell : Cell p) :
    ¬ (cell.row.target ∉ journalSources j) :=
  fun free => free (recorded_target history cell.written.1)

theorem placed_slot {p : GeneralNominalCenters.Plan rs} (d : Delta before after p)
    (c : Cell p) (chosen : c ∈ d.cells) :
    sourceSlot before.base c.row.target = none ∧
      ∃ i, sourceSlot after.base c.row.target = some i := by
  have none : sourceSlot before.base c.row.target = none := by
    cases h : sourceSlot before.base c.row.target with
    | none => rfl
    | some i =>
      exact False.elim (d.absent c chosen ((sourceSlot_exact ..).mp h ▸
        GeneralNominalAllocationSupport.slot_source before i))
  obtain ⟨i,eq⟩ := d.fresh_slot c chosen
  exact ⟨none,i,(sourceSlot_exact ..).mpr eq⟩

end Yulang.GeneralWhereOriginReservation318
