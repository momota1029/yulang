import Yulang.GeneralDeclarativeI65I74AuthenticatedFieldEvent472
import Yulang.GeneralDeclarativeWitnessOrigins350

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ObservationSyntax471
open RetainedFull445
open PreparedDeclarations463 (CheckedTable)
open LiteralFold471 (SourceGate)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWitnessOrigins350 (Table Attached attach support)
open QuotientObservation471 (ConeWire Wire)
open GeneralDeclarativeOrigins321 (Backed)

/-- Adapt an existing ordinary provenance manifest, not a fresh ledger.
The request, selected physical raw ordinal and authored-table ordinal
are checked separately. A completed-output record is not here renamed
to source. The manifest still comes from the caller's compiler phase. -/
def gateFromAttachedAuthor472 {p : FullProblem} {t : Table}
    (a : Attached p.state.base.core.current.ordinary t) : SourceGate p where
  completed := (· ∈ t.released)
  ledger := support a
  Authenticates := fun occ raw row => occ = p.root.occurrence ∧
    p.state.base.core.current.ordinary.equations[raw]? = some row ∧ row ∈ t.authored
  Data := Nat
  verify := fun occ raw row author => decide (occ = p.root.occurrence ∧
    p.state.base.core.current.ordinary.equations[raw]? = some row ∧ t.authored[author]? = some row)
  exact := by
    intro occ raw row
    constructor
    · rintro ⟨author,accepted⟩
      have all := of_decide_eq_true accepted
      exact ⟨all.1,all.2.1,List.mem_of_getElem? all.2.2⟩
    · rintro ⟨r,ord,auth⟩
      obtain ⟨x,atX⟩ := List.mem_iff_getElem?.mp auth
      exact ⟨x,decide_eq_true ⟨r,ord,atX⟩⟩
  source := fun _ _ _ h => h.2.2

structure AttachedFieldWire472 where
  head : PreparedDeclarations463.HeadAddress
  declarationOrdinal : Nat
  label : Nat
  path : List WrittenPattern460.PhysicalOrigin.Pose
  rawOrdinal : Nat
  authorOrdinal : Nat

def AttachedFieldWire472.atGate {p : FullProblem} {t : Table}
    (w : AttachedFieldWire472) (a : Attached p.state.base.core.current.ordinary t) :
    FieldOriginWire (gateFromAttachedAuthor472 (p := p) a) :=
  ⟨w.head,w.declarationOrdinal,w.label,w.path,w.rawOrdinal,w.authorOrdinal⟩

def readAttachedAuthorField472 (p : FullProblem) (t : Table)
    (gd : CheckedTable p.old.state.core.current) (w : AttachedFieldWire472)
    (table : GraphTicket n) (i : Fin n) (scope : ConeWire n m) (quotient : Wire m k) :
    Option CheckedFieldBit := do
  let a ← attach p.state.base.core.current.ordinary t
  readFieldBit (gateFromAttachedAuthor472 (p := p) a) gd (w.atGate a) table i scope quotient

theorem attached_author_wire_checks_both_literal_ordinals472
    {p : FullProblem} {t : Table} (a : Attached p.state.base.core.current.ordinary t)
    {o : List Nat} {raw author : Nat} {row : Equation} :
    (gateFromAttachedAuthor472 (p := p) a).verify o raw row author = true ↔
      o = p.root.occurrence ∧
      p.state.base.core.current.ordinary.equations[raw]? = some row ∧ t.authored[author]? = some row :=
  by simp [gateFromAttachedAuthor472]

theorem output_only_never_becomes_source_even_when_released472
    {p : FullProblem} {t : Table} (a : Attached p.state.base.core.current.ordinary t)
    {o raw author row} (notAuthored : row ∉ t.authored) :
    (gateFromAttachedAuthor472 (p := p) a).verify o raw row author = false := by
  cases found : (gateFromAttachedAuthor472 (p := p) a).verify o raw row author
  · rfl
  · exact (notAuthored (List.mem_of_getElem?
      ((attached_author_wire_checks_both_literal_ordinals472 a).mp found).2.2)).elim

end Yulang.GeneralDeclarativeI65.I72.ObservationSyntax471
