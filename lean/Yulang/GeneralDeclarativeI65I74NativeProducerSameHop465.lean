import Yulang.GeneralDeclarativeI65I74NativeProducerInstall465
import Yulang.GeneralDeclarativeI65I74IndexedLogicalSource464
import Yulang.GeneralDeclarativeI65I74PreparedHeadField463

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.NativeProducer465
open Yulang.GeneralDeclarativeI65
open GeneralDeclarativeWitnessNativeValue360 (Write)
open GeneralDeclarativeHead320 (Equation)
open Checker408 (Problem)
open PreparedDeclarations463
open PhysicalVisit463.IssuedProjection464

def physicalOrigins (s : GeneralDeclarativeI65.State) (site : Nat) : List Origin :=
  s.origins.filter (fun o => o.slot == site)

/-- The exact listed origin at this physical slot is unique. Merely sharing
a value, an issuer label, or a logical capture does not imply this. -/
theorem any_origin_at_a_single_physical_slot_is_the_same_occurrence
    {s : GeneralDeclarativeI65.State} {w : Write} {p : CheckedPhase s} {logical ordinal : Nat}
    (found : PhaseOriginAt p w logical ordinal)
    (unique : (physicalOrigins s w.address.target).length = 1) {other : Origin}
    (atOrig : other ∈ s.origins) (slot : other.slot = w.address.target) :
    other = originalOfWrite w := by
  have known : originalOfWrite w ∈ physicalOrigins s w.address.target :=
    List.mem_filter.mpr ⟨List.mem_of_getElem? found.1,by simp [originalOfWrite]⟩
  have candidate : other ∈ physicalOrigins s w.address.target :=
    List.mem_filter.mpr ⟨atOrig,by simp [slot]⟩
  obtain ⟨one,h⟩ := List.length_eq_one_iff.mp unique
  rw [h] at known candidate
  exact (List.mem_singleton.mp candidate).trans (List.mem_singleton.mp known).symm

structure PhaseAtHop where
  hop : Nat
  sourceOrdinal : Nat
  write : Write

structure PhaseField (p : Problem) (phase : CheckedPhase p.state.core) where
  existing : HeadFieldWire p
  actual : PhaseAtHop

/-- Only the original centre or the previous selected child is the logical
source. The stored raw row at its literal path ordinal and the released
physical owner must be identical. -/
def phaseOwnerAtHop {p : Problem} (phase : CheckedPhase p.state.core)
    (r : HeadFieldReceipt) (w : PhaseAtHop) : Bool :=
  (do
    let cap ← p.root.demand.arguments[r.authored.headArgument]?
    let logical ← logicalBeforeHop cap.lower r.path w.hop
    let ordinal ← r.rows[w.hop]?
    let owner ← p.state.core.current.ordinary.equations[ordinal]?
    pure (decide (owner.left = w.write.address.target ∧
      (physicalOrigins p.state.core owner.left).length = 1) &&
      checkPhaseOrigin phase w.write logical w.sourceOrdinal)).getD false

def LiteralPhaseOwnerAtHop {p : Problem} (phase : CheckedPhase p.state.core)
    (r : HeadFieldReceipt) (w : PhaseAtHop) : Prop :=
  ∃ cap logical ordinal owner,
    p.root.demand.arguments[r.authored.headArgument]? = some cap ∧
    logicalBeforeHop cap.lower r.path w.hop = some logical ∧ r.rows[w.hop]? = some ordinal ∧
    p.state.core.current.ordinary.equations[ordinal]? = some owner ∧
    owner.left = w.write.address.target ∧ (physicalOrigins p.state.core owner.left).length = 1 ∧
    PhaseOriginAt phase w.write logical w.sourceOrdinal

theorem every_supplied_phase_hop_is_exactly_the_literal_physical_owner
    {p : Problem} (phase : CheckedPhase p.state.core) (r : HeadFieldReceipt) (w : PhaseAtHop) :
    phaseOwnerAtHop phase r w = true ↔ LiteralPhaseOwnerAtHop phase r w := by
  constructor
  · intro checked
    cases cap : p.root.demand.arguments[r.authored.headArgument]? with
    | none => simp [phaseOwnerAtHop,cap,Option.bind] at checked
    | some a =>
      cases near : logicalBeforeHop a.lower r.path w.hop with
      | none => simp [phaseOwnerAtHop,cap,near,Option.bind] at checked
      | some logical =>
        cases index : r.rows[w.hop]? with
        | none => simp [phaseOwnerAtHop,cap,near,index,Option.bind] at checked
        | some n =>
          cases row : p.state.core.current.ordinary.equations[n]? with
          | none => simp [phaseOwnerAtHop,cap,near,index,row,Option.bind] at checked
          | some o =>
            have strict : (o.left = w.write.address.target ∧ (physicalOrigins p.state.core o.left).length = 1) ∧
                PhaseOriginAt phase w.write logical w.sourceOrdinal := by
              simpa [phaseOwnerAtHop,cap,near,index,row,Option.bind,
                finite_phase_origin_check_iff_literal_placed_active_row] using checked
            exact ⟨a,logical,n,o,cap,near,index,row,strict.1.1,strict.1.2,strict.2⟩
  · rintro ⟨a,l,n,o,cap,near,index,row,same,unique,source⟩
    have exactUnique : (physicalOrigins p.state.core w.write.address.target).length = 1 := same ▸ unique
    simp [phaseOwnerAtHop,cap,near,index,row,same,exactUnique,Option.bind,
      (finite_phase_origin_check_iff_literal_placed_active_row ..).mpr source]

def readFieldWithPhaseOwner {p : Problem} {phase : CheckedPhase p.state.core}
    (tab : CheckedTable p.state.core.current) (w : PhaseField p phase) : Option HeadFieldReceipt := do
  let found ← readHeadField (p := p) tab w.existing
  if phaseOwnerAtHop phase found w.actual then some found else none

theorem phase_owner_reader_keeps_the_exact_existing_field_report
    {p : Problem} {phase : CheckedPhase p.state.core} {tab : CheckedTable p.state.core.current}
    {w : PhaseField p phase} {r : HeadFieldReceipt} :
    readFieldWithPhaseOwner tab w = some r ↔
      readHeadField (p := p) tab w.existing = some r ∧ LiteralPhaseOwnerAtHop phase r w.actual := by
  constructor
  · intro read
    cases actual : readHeadField (p := p) tab w.existing with
    | none => simp [readFieldWithPhaseOwner,actual,Option.bind] at read
    | some a =>
      by_cases yes : phaseOwnerAtHop phase a w.actual = true
      · have same : a = r := by simpa [readFieldWithPhaseOwner,actual,yes,Option.bind] using read
        subst r
        exact ⟨rfl,(every_supplied_phase_hop_is_exactly_the_literal_physical_owner ..).mp yes⟩
      · simp [readFieldWithPhaseOwner,actual,yes,Option.bind] at read
  · rintro ⟨a,b⟩
    simp [readFieldWithPhaseOwner,a,(every_supplied_phase_hop_is_exactly_the_literal_physical_owner ..).mpr b,Option.bind]

end Yulang.GeneralDeclarativeI65.I72.NativeProducer465
