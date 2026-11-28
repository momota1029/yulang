import Yulang.GeneralDeclarativeI65I74SignedInteriorPath483

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
open RetainedFull445 (FullProblem)
open Producer479 (Site readTrail)
open ObservationAlternatives473 (Positions graphOf)
open GeneralDeclarativeWitnessOrigins350 (Table)

/-- The local card and ambient hop replays are fixed separately from the
structural sequence. The ordering and visited positions are not inferred
from either equivalence classes or a collection of successful endpoints. -/
inductive InteriorComponentReads {p : FullProblem} {pos : Positions n} (table : Table) :
    Site p.old.state.core pos → Site p.old.state.core pos → ReadCard → List (InteriorMove n) →
    List (Site p.old.state.core pos × Site p.old.state.core pos) → Prop where
  | nil : InteriorComponentReads table left right card [] []
  | cons (visit : PairedFocusedHop (p := p) table left right move.step card move.author move.ambient) :
      graphOf p.old.state.core pos left.index ≠ .unresolved →
      graphOf p.old.state.core pos right.index ≠ .unresolved →
      readPairedFocusedHop (p := p) table left right move.step card move.author move.ambient = some visit →
      InteriorComponentReads table visit.author.after visit.ambient visit.author.childCard more rest →
      InteriorComponentReads table left right card (move::more) ((visit.author.after,visit.ambient)::rest)

theorem validated_local_components_replay_a_finite_interior_wire_at_the_same_sites
    {p : FullProblem} {pos : Positions n} {table : Table}
    {left right : Site p.old.state.core pos} {card : ReadCard} {moves path}
    (proof : InteriorComponentReads (p := p) table left right card moves path) :
    ∃ out, readInteriorSequence (p := p) table left right card moves = some out ∧ out.path = path := by
  induction proof with
  | nil => exact ⟨⟨[],.nil⟩,rfl,rfl⟩
  | cons visit l r fetched _ ih =>
    obtain ⟨out,replay,exactPath⟩ := ih
    refine ⟨⟨(visit.author.after,visit.ambient)::out.path,.cons visit l r out.actual⟩,?_,?_⟩
    · rw [readInteriorSequence,dite_eq_left l,dite_eq_left r]
      simp [fetched,replay,bind,Option.bind]
    · simp [exactPath]

private theorem collected_for_signed_result {A : Type} {o : Option A} {a : A} (eq : o = some a) :
    collectedForInterior o = some ⟨a,eq⟩ := by
  subst o
  rfl

theorem validated_local_components_and_old_sign_replay_the_exact_signed_interior
    {p : FullProblem} {pos : Positions n} {table : Table}
    {left right : Site p.old.state.core pos} {card : ReadCard} {rel : List (Fin n × Fin n)}
    {w : SignedInteriorWire n} {path terminal bit}
    (separate : InteriorComponentReads (p := p) table left right card (readPairedIndices w.moves) path)
    (geometry : readTrail rel right w.ambient = some (terminal,bit)) :
    ∃ out, readSignedInteriorPath (p := p) table left right card rel w = some out ∧
      out.sites.path = path ∧ out.terminal = terminal ∧ out.bit = bit := by
  obtain ⟨out,run,exactPath⟩ := validated_local_components_replay_a_finite_interior_wire_at_the_same_sites separate
  refine ⟨⟨out,terminal,bit,geometry⟩,?_,exactPath,rfl,rfl⟩
  simp [readSignedInteriorPath,run,collected_for_signed_result geometry,bind,Option.bind]

end Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
