import Yulang.GeneralDeclarativeI65I74AuthenticatedField472
import Yulang.GeneralDeclarativeCompoundEndpoints338

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ObservationSyntax471
open RetainedFull445
open PreparedDeclarations463
open LiteralFold471 (SourceGate inputSourceOnly)
open GeneralDeclarativeInlineTrace331 (Read Args Fields realize)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativeLowerKnown321 (alias_mono)
open GeneralDeclarativeCompoundEndpoints338 (closed_mono)
open QuotientObservation471 (ConeWire Wire ReachableClosed ReturnsUpToEquality
  replayCone exact_finite_cone_replay_exists)

theorem monotone_ordinary_input_trace472
    {s t : GeneralDeclarativeHead320.State} (normal : s.normal = t.normal)
    (rows : s.equations ⊆ t.equations)
    {mode raw code uses} (read : Read s mode raw code uses) : Read t mode raw code uses := by
  refine Read.rec
    (motive_1 := fun mode raw code uses _ => Read t mode raw code uses)
    (motive_2 := fun mode raw code uses _ => Args t mode raw code uses)
    (motive_3 := fun mode raw code uses _ => Fields t mode raw code uses)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ read
  · intros; exact .capture
  · intro mode code n owner raw uses inspect eq stored _ later
    exact .expose inspect (alias_mono normal rows eq) (rows stored) later
  · intros; exact .primitive (by assumption)
  · intros; exact .nominal (by assumption)
  · intros; exact .variant (by assumption)
  · intros; exact .join (by assumption) (by assumption)
  · intros
    exact .record (closed_mono normal rows (by assumption)) (by assumption) (by assumption)
      (by assumption) (by assumption) (by assumption) (by assumption)
  · intros; exact .nil
  · intros; exact .cons (by assumption) (by assumption)
  · intros; exact .nil
  · intros; exact .cons (by assumption) (by assumption)

theorem same_phase_input_event_reads_the_full_source_only_view472
    {p g gd w} (r : @FieldOrigin p g gd w) (t : SourceTyping r) :
    Read (restriction (inputSourceOnly g)) .actual
      (.variable r.head.orig.capture.lower) r.head.orig.code t.uses := by
  apply monotone_ordinary_input_trace472
    (s := ⟨p.state.base.core.current.ordinary.normal,[r.row]⟩)
    (t := restriction (inputSourceOnly g)) rfl _ t.rooted
  intro row here
  obtain rfl := List.mem_singleton.mp here
  exact t.actualOrdinarySource

theorem exact_same_source_event_is_meant_by_every_original_fit472
    {p g gd w} (r : @FieldOrigin p g gd w) (t : SourceTyping r) :
    ∃ rebuilt, (∀ m : Model, FitsFull p.state m →
      GeneralDeclarativeRepeatedActual323.eqAt m.assignment (.variable r.head.orig.capture.lower) rebuilt) ∧
      GeneralDeclarativeTermWalk322.Walk .actual rebuilt r.head.orig.code t.uses := by
  obtain ⟨term,means,walk⟩ := realize (same_phase_input_event_reads_the_full_source_only_view472 r t)
  exact ⟨term,fun m fit => means m.assignment fit.1.1.1,walk⟩

theorem both_signs_have_exact_finite_wires_at_one_actual_source_event472
    {p : FullProblem} {g : SourceGate p} {gd : CheckedTable p.old.state.core.current}
    {w : FieldOriginWire g} {table : GraphTicket n} {i : Fin n}
    {graph : CommonRoleRegularGraph.Graph n}
    (r : FieldOrigin g gd w) (t : SourceTyping r)
    (origin : readFieldOrigin g gd w = some r) (event : readTyping r = some t)
    (site : confirmedAddress r = (table.sites.get i).site)
    (input : readObservationGraph p.old.state.core table = some graph)
    (closed : ReachableClosed graph i) :
    ∀ b : Bool, (b = true ↔ ReturnsUpToEquality graph i) →
      ∃ (m k : Nat) (scope : ConeWire n m) (part : Wire m k),
        readFieldBit g gd w table i scope part =
          some ⟨p.root.occurrence,r.head.orig.declaration.id,w.originalOrdinal,w.authoredPath,w.logicalField,b⟩ := by
  intro b exact
  have all := exact_finite_cone_replay_exists closed
  have wits : ∃ (m k : Nat) (scope : ConeWire n m) (part : Wire m k),
      replayCone graph i scope part = some b := by
    cases b
    · exact all.2.mpr (fun cyc => Bool.false_ne_true (exact.mpr cyc))
    · exact all.1.mpr (exact.mp rfl)
  obtain ⟨_,_,scope,part,hit⟩ := wits
  refine ⟨_,_,scope,part,?_⟩
  simp [readFieldBit,origin,event,site,replayObservation,input,hit,bind,Option.bind]

end Yulang.GeneralDeclarativeI65.I72.ObservationSyntax471
