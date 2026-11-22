import Yulang.GeneralDeclarativeWhereLegacyCut346
import Yulang.GeneralDeclarativeNominalIntervals347

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNativeWhere347
open GeneralDeclarations (Registry Clause)
open GeneralNominalCenters (Plan Site)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralVersionedTraceDomain313 (seed raw)
open GeneralWhereOriginDelta318 (Cell High)
open GeneralWhereVersionCompiler317 (child)
open GeneralDictionaryBinderLocations (sourceSlot sourceSlot_exact)
open GeneralDeclarativeWhereRawAtoms346 (cell)
open GeneralDeclarativeNominalIntervals347 (read Named)

abbrev layout (s : State rs) := s.core.erased.current.context.state

theorem absent {s : State rs} (run : Reachable r root s) {n : Nat}
    (other : High (layout s) n) : n ∉ raw s := by
  obtain ⟨k,tag,rfl⟩ := other
  exact GeneralVersionedHighOrigins315.raw_absent run tag

theorem no_lookup {s : State rs} (run : Reachable r root s) {n : Nat}
    (other : High (layout s) n) : sourceSlot (layout s).base n = none := by
  cases got : sourceSlot (layout s).base n with
  | none => rfl
  | some i =>
    exact False.elim (absent run other
      ((sourceSlot_exact ..).mp got ▸ GeneralNominalAllocationSupport.slot_source (layout s) i))

/-- The current native boundary cannot acquire even one physical
versioned where cell at a plan's current seed. This is a domain
obstruction, not a statement about the declarative classification. -/
theorem no_compiled_cell {s : State rs} (run : Reachable r root s) {p : Plan rs}
    (sameSeed : seed s = p.packet.context.state.seed) (c : Cell p) :
    sourceSlot (layout s).base c.row.target = none ∧
    cell (layout s).base c = none ∧ read (layout s) c.row.target = none := by
  have missing := no_lookup run (c.high (t := layout s) sameSeed)
  refine ⟨missing,?_,?_⟩
  · unfold cell
    rw [missing]; rfl
  · unfold GeneralDeclarativeNominalIntervals347.read
    rw [missing]; rfl

theorem recorded_no_compiled_cell {s : State rs} (run : Reachable r root s) {p : Plan rs}
    (recorded : p ∈ s.plans) (c : Cell p) :
    sourceSlot (layout s).base c.row.target = none ∧
    cell (layout s).base c = none ∧ read (layout s) c.row.target = none :=
  no_compiled_cell run (GeneralNominalVersionedMixedSeedLedger237.reachable run p recorded).symm c

/-- The obstruction applies to both actual syntactic compiler polarities,
even at a step that has a relevant recorded native plan. -/
theorem both_missing {s : State rs} (run : Reachable r root s) {p : Plan rs}
    (recorded : p ∈ s.plans) (c : Cell p) :
    cell (layout s).base (GeneralDeclarativeWhereBoth346.polar c .lower) = none ∧
    cell (layout s).base (GeneralDeclarativeWhereBoth346.polar c .upper) = none :=
  ⟨(recorded_no_compiled_cell run recorded _).2.1,(recorded_no_compiled_cell run recorded _).2.1⟩

end Yulang.GeneralDeclarativeNativeWhere347
