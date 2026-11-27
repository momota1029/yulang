import Yulang.GeneralDeclarativeI65I74AliasedObservationCone472

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ObservationAliasHead472
open ObservationSyntax471
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table Attached attach)
open QuotientObservation471 (ConeWire Wire ReachableClosed ReturnsUpToEquality replayCone exact_finite_cone_replay_exists)

/-- Once an actual old sourced typing walk and complete immutable
observation graph exist, neither bit, nor an old report, nor a caller's
guess at the quotient is a premise for replaying the exact position. -/
theorem either_aliased_field_bit_reifies_at_the_original_request472
    {p : FullProblem} {t : Table} {gd : CheckedTable p.old.state.core.current}
    {w : AttachedFieldWire472} {d : AliasGraphTicket n} {i : Fin n}
    (actual : Attached p.state.base.core.current.ordinary t)
    (current : attach p.state.base.core.current.ordinary t = some actual)
    (f : FieldOrigin (gateFromAttachedAuthor472 (p := p) actual) gd (w.atGate actual))
    (sources : readFieldOrigin (gateFromAttachedAuthor472 (p := p) actual) gd (w.atGate actual) = some f)
    (typing : SourceTyping f) (typed : readTyping f = some typing)
    (pinned : confirmedAddress f = (d.positions.sites.get i).site)
    (distinct : allAddressesDistinct d.positions = true)
    (closed : ReachableClosed (aliasedObservation p.old.state.core d) i)
    (bit : Bool) (independent : bit = true ↔ ReturnsUpToEquality (aliasedObservation p.old.state.core d) i) :
    ∃ (m k : Nat) (scope : ConeWire n m) (q : Wire m k),
      readAliasField472 p t gd w d i scope q =
        some ⟨p.root.occurrence,f.head.orig.declaration.id,w.declarationOrdinal,w.path,w.label,bit⟩ := by
  have localClass := exact_finite_cone_replay_exists closed
  have finite : ∃ (m k : Nat) (scope : ConeWire n m) (q : Wire m k),
      replayCone (aliasedObservation p.old.state.core d) i scope q = some bit := by
    cases bit
    · exact localClass.2.mpr (fun cycle => Bool.false_ne_true (independent.mpr cycle))
    · exact localClass.1.mpr (independent.mp rfl)
  obtain ⟨_,_,scope,q,ok⟩ := finite
  exact ⟨_,_,scope,q,by
    simp [readAliasField472,current,sources,typed,pinned,replayAliasObservation,distinct,ok,bind,Option.bind]⟩

end Yulang.GeneralDeclarativeI65.I72.ObservationAliasHead472
