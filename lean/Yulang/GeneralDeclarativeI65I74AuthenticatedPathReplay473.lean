import Yulang.GeneralDeclarativeI65I74IndependentPathReflection473

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.LiteralVisits473
open ObservationAlternatives473 (Place Positions oldPosition graphOf)
open ObservationSyntax471 (FieldOrigin SourceTyping confirmedAddress AttachedFieldWire472
  readFieldOrigin readTyping gateFromAttachedAuthor472)
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table attach)
open WrittenPattern460.PhysicalOrigin (Pose)
open QuotientObservation471 (ReturnsUpToEquality)

def pathEndsWithField (moves : List StepWire) : Prop :=
  match moves.getLast? with
  | none => True
  | some m => ∃ label, m.action = .field label

theorem terminal_selector_is_exact {wire : PathWire n} :
    terminalIsField wire = true ↔ pathEndsWithField (wire.rest.map Prod.fst) := by
  simp only [terminalIsField,pathEndsWithField,List.getLast?_map]
  cases h : wire.rest.getLast? with
  | none => simp
  | some step =>
    rcases step with ⟨m,cp⟩
    cases m with
    | mk addr written => cases addr <;> simp

theorem already_authenticated_source_use_and_path_have_exact_report_replay
    (p : FullProblem) (manifest : Table) (gd : CheckedTable p.old.state.core.current)
    (input : AttachedFieldWire472) (positions : Positions n) (rel : List (Fin n × Fin n))
    (a : GeneralDeclarativeWitnessOrigins350.Attached p.state.base.core.current.ordinary manifest)
    (attached : attach p.state.base.core.current.ordinary manifest = some a)
    (f : FieldOrigin (gateFromAttachedAuthor472 (p := p) a) gd (input.atGate a))
    (t : SourceTyping f)
    (anchor : readFieldOrigin (gateFromAttachedAuthor472 (p := p) a) gd (input.atGate a) = some f)
    (event : readTyping f = some t)
    (root : Fin n)
    (rootAt : oldPosition positions root = .logical f.head.orig.capture.lower)
    (rootObservation : GuardedObservationInput p.old.state.core positions rel root)
    (safeRoot : ¬ReturnsUpToEquality (graphOf p.old.state.core positions) root)
    (site : Fin n) (ordinal : Nat) (first : List ObservationSyntax471.Slot)
    (actual : confirmedAddress f = .inline ordinal first)
    (atFirst : oldPosition positions site = .rowPos ordinal first)
    {steps suffix final bit}
    (trace : IndependentPath p.old.state.core positions rel site f.sourcePattern f.selectedQuery
      f.actualPayload steps suffix final bit)
    (terminal : pathEndsWithField steps) :
    ∃ (outer : Checkpoint n) (wire : PathWire n),
      readNestedAuthoredField p manifest gd input positions rel outer wire = some
        ⟨p.root.occurrence,f.head.orig.declaration.id,input.declarationOrdinal,input.path ++ suffix,
          oldPosition positions final,bit⟩ := by
  have prior : false = true ↔ ReturnsUpToEquality (graphOf p.old.state.core positions) root := by
    simp [safeRoot]
  obtain ⟨c,_,verified⟩ := independent_checkpoint_reifies_the_exact_site_and_sign rootObservation false prior
  rw [rootAt] at verified
  obtain ⟨wire,out,_,moves,replayed,reported,endAt,output⟩ :=
    independent_path_has_finite_replay_at_its_exact_terminal trace
  have terminalOk : terminalIsField wire = true := terminal_selector_is_exact.mpr (moves.symm ▸ terminal)
  have mapped (whereAt : Place) (eq : oldPosition positions site = whereAt) :
      (readLiteralPath p.old.state.core positions rel whereAt f.sourcePattern f.selectedQuery
        f.actualPayload wire) >>= (fun v => some (⟨p.root.occurrence,f.head.orig.declaration.id,
          input.declarationOrdinal,input.path ++ v.suffix,oldPosition positions v.final,v.bit⟩ :
            NestedFieldReport n)) =
        some ⟨p.root.occurrence,f.head.orig.declaration.id,input.declarationOrdinal,input.path ++ suffix,
          oldPosition positions final,bit⟩ := by
    subst whereAt
    simp [replayed,reported,endAt,output]
  exact ⟨c,wire,by
    simpa [readNestedAuthoredField,terminalOk,attached,anchor,event,actual,verified,bind,Option.bind,
      pure] using mapped _ atFirst⟩

end Yulang.GeneralDeclarativeI65.I72.LiteralVisits473
