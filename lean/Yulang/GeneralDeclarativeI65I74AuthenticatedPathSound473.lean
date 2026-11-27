import Yulang.GeneralDeclarativeI65I74AuthenticatedPathReplay473

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.LiteralVisits473
open ObservationAlternatives473 (Place Positions oldPosition graphOf)
open ObservationSyntax471 (FieldOrigin SourceTyping confirmedAddress AttachedFieldWire472
  readFieldOrigin readTyping gateFromAttachedAuthor472)
open RetainedFull445 (FullProblem)
open GeneralDeclarativeI65
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table Attached attach)
open WrittenPattern460.PhysicalOrigin (Pose)
open QuotientObservation471 (ReturnsUpToEquality)

structure ActualNestedReplay (p : FullProblem) (table : Table)
    (gd : CheckedTable p.old.state.core.current) (input : AttachedFieldWire472)
    (positions : Positions n) (relations : List (Fin n × Fin n)) (outer : Checkpoint n)
    (wire : PathWire n) (result : NestedFieldReport n) where
  attached : Attached p.state.base.core.current.ordinary table
  sameAttachment : attach p.state.base.core.current.ordinary table = some attached
  firstRead : FieldOrigin (gateFromAttachedAuthor472 (p := p) attached) gd (input.atGate attached)
  originalRead : readFieldOrigin (gateFromAttachedAuthor472 (p := p) attached) gd
    (input.atGate attached) = some firstRead
  sourceTyping : SourceTyping firstRead
  event : readTyping firstRead = some sourceTyping
  outerAt : oldPosition positions outer.which = .logical firstRead.head.orig.capture.lower
  outerComplete : GuardedObservationInput p.old.state.core positions relations outer.which
  outerSafe : ¬ ReturnsUpToEquality (graphOf p.old.state.core positions) outer.which
  rawOrdinal : Nat
  rawPrefix : List ObservationSyntax471.Slot
  actualFirst : confirmedAddress firstRead = .inline rawOrdinal rawPrefix
  whereFirst : oldPosition positions wire.here.which = .rowPos rawOrdinal rawPrefix
  writtenSuffix : List Pose
  final : Fin n
  visits : IndependentPath p.old.state.core positions relations wire.here.which
    firstRead.sourcePattern firstRead.selectedQuery firstRead.actualPayload
      (wire.rest.map Prod.fst) writtenSuffix final result.bit
  actuallyField : pathEndsWithField (wire.rest.map Prod.fst)
  exactReport :
    result = ⟨p.root.occurrence,firstRead.head.orig.declaration.id,input.declarationOrdinal,
      input.path ++ writtenSuffix,oldPosition positions final,result.bit⟩

theorem successful_nested_report_never_changes_source_event_or_exact_positions
    {p table gd input positions rel outer wire r}
    (accepted : @readNestedAuthoredField n p table gd input positions rel outer wire = some r) :
    Nonempty (ActualNestedReplay p table gd input positions rel outer wire r) := by
  by_cases last : terminalIsField wire = true
  · cases auth : attach p.state.base.core.current.ordinary table with
    | none => simp [readNestedAuthoredField,last,auth,bind,Option.bind] at accepted
    | some a =>
      let g := gateFromAttachedAuthor472 (p := p) a
      cases origin : readFieldOrigin g gd (input.atGate a) with
      | none => simp [readNestedAuthoredField,last,auth,g,origin,bind,Option.bind] at accepted
      | some f =>
        cases source : readTyping f with
        | none => simp [readNestedAuthoredField,last,auth,g,origin,source,bind,Option.bind] at accepted
        | some t =>
          cases whereFrom : confirmedAddress f with
          | named k => simp [readNestedAuthoredField,last,auth,g,origin,source,whereFrom,bind,Option.bind] at accepted
          | inline ordinal first =>
            cases outerBit : readCheck p.old.state.core positions rel (.logical f.head.orig.capture.lower) outer with
            | none => simp [readNestedAuthoredField,last,auth,g,origin,source,whereFrom,outerBit,bind,Option.bind] at accepted
            | some sign =>
              cases sign
              · cases deeper : readLiteralPath p.old.state.core positions rel (.rowPos ordinal first)
                  f.sourcePattern f.selectedQuery f.actualPayload wire with
                | none => simp [readNestedAuthoredField,last,auth,g,origin,source,whereFrom,outerBit,deeper,bind,Option.bind] at accepted
                | some v =>
                  have same : (⟨p.root.occurrence,f.head.orig.declaration.id,input.declarationOrdinal,
                    input.path ++ v.suffix,oldPosition positions v.final,v.bit⟩ : NestedFieldReport n) = r := by
                    simpa [readNestedAuthoredField,last,auth,g,origin,source,whereFrom,outerBit,deeper,bind,Option.bind] using accepted
                  subst r
                  obtain ⟨guard,root,exact⟩ := read_checkpoint_guards outerBit
                  obtain ⟨atFirst,hops⟩ := actual_read_reflects_the_independent_path_and_all_prefix_guards deeper
                  exact ⟨⟨a,auth,f,origin,t,source,root,guard,fun cyc => Bool.false_ne_true (exact.mpr cyc),
                    ordinal,first,whereFrom,atFirst,v.suffix,v.final,hops,terminal_selector_is_exact.mp last,rfl⟩⟩
              · simp [readNestedAuthoredField,last,auth,g,origin,source,whereFrom,outerBit,bind,Option.bind] at accepted
  · simp [readNestedAuthoredField,last] at accepted

theorem original_same_phase_model_semantics_of_nested_receipt
    {p table gd input positions rel outer wire r}
    (present : @ActualNestedReplay n p table gd input positions rel outer wire r) :
    ∃ rebuilt, (∀ m : GeneralDeclarativeI65.Model, FitsFull p.state m →
      GeneralDeclarativeRepeatedActual323.eqAt m.assignment
        (.variable present.firstRead.head.orig.capture.lower) rebuilt) ∧
      GeneralDeclarativeTermWalk322.Walk .actual rebuilt present.firstRead.head.orig.code
        present.sourceTyping.uses :=
  ObservationSyntax471.exact_same_source_event_is_meant_by_every_original_fit472
    present.firstRead present.sourceTyping

theorem independent_path_bit_iff_returns_at_its_precise_last_site
    {s : OwnState} {positions : Positions n} {rel : List (Fin n × Fin n)}
    {site p q raw steps suffix last bit}
    (actual : IndependentPath s positions rel site p q raw steps suffix last bit) :
    bit = true ↔ ReturnsUpToEquality (graphOf s positions) last := by
  induction actual with
  | terminal _ correct => exact correct
  | branch _ _ _ _ _ _ ih => exact ih

theorem reported_cycle_is_about_the_reported_source_position
    {p table gd input positions rel outer wire r}
    (present : @ActualNestedReplay n p table gd input positions rel outer wire r) :
    r.physicalSite = oldPosition positions present.final ∧
      (r.bit = true ↔ ReturnsUpToEquality (graphOf p.old.state.core positions) present.final) := by
  exact ⟨congrArg NestedFieldReport.physicalSite present.exactReport,
    independent_path_bit_iff_returns_at_its_precise_last_site present.visits⟩

end Yulang.GeneralDeclarativeI65.I72.LiteralVisits473

namespace Yulang.GeneralDeclarativeI65.I72.LiteralVisits473
open ObservationSyntax471 (AttachedFieldWire472 gateFromAttachedAuthor472)
open ObservationAlternatives473 (Positions)
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table)
open GeneralDeclarativeHead320 (Equation)

theorem any_nested_result_needs_the_same_actual_authored_row
    {p : FullProblem} {provenance : Table} {gd input pos rel outer wire out}
    (result : @readNestedAuthoredField n p provenance gd input pos rel outer wire = some out) :
    ∃ (row : Equation), p.state.base.core.current.ordinary.equations[input.rawOrdinal]? = some row ∧
      row ∈ provenance.authored := by
  obtain ⟨receipt⟩ := successful_nested_report_never_changes_source_event_or_exact_positions result
  have file := receipt.firstRead.authenticated
  change p.root.occurrence = p.root.occurrence ∧
    p.state.base.core.current.ordinary.equations[input.rawOrdinal]? = some receipt.firstRead.row ∧
    receipt.firstRead.row ∈ provenance.authored at file
  exact ⟨_,file.2⟩

theorem raw_row_or_completed_output_without_input_author_cannot_return_nested_bit
    (p : FullProblem) (provenance : Table) (gd : CheckedTable p.old.state.core.current)
    (input : AttachedFieldWire472) (pos : Positions n) (rel : List (Fin n × Fin n))
    (outer : Checkpoint n) (wire : PathWire n)
    (notAuthored : ∀ row, p.state.base.core.current.ordinary.equations[input.rawOrdinal]? =
      some row → row ∉ provenance.authored) :
    readNestedAuthoredField p provenance gd input pos rel outer wire = none := by
  cases ran : readNestedAuthoredField p provenance gd input pos rel outer wire with
  | none => rfl
  | some report =>
    obtain ⟨row,actual,authorized⟩ := any_nested_result_needs_the_same_actual_authored_row ran
    exact (notAuthored row actual authorized).elim

end Yulang.GeneralDeclarativeI65.I72.LiteralVisits473
