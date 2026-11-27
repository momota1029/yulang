import Yulang.GeneralDeclarativeI65I74LiteralFold471
import Yulang.GeneralDeclarativeNestedIndex332

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.LiteralFold471
open RetainedFull445
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeNestedIndex332 (ofRows)
open GeneralDeclarativeNestedDecode332 (decode)
open GeneralDeclarativeNestedRun332 (run)
open GeneralDeclarativeNestedSound332 (sound)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralSourceMetadataRows291 (interpretation)

def inputSourceOnly {p : FullProblem} (g : SourceGate p) :
    Supported p.state.base.core.current.ordinary (fun _ => False) :=
  ⟨g.ledger.derivesFrom,g.ledger.ordinary⟩

theorem original_input_row_is_in_source_only_restriction {p g tab w}
    (r : @SourceReceipt p g tab w) :
    r.field.folded.owner ∈ (restriction (inputSourceOnly g)).equations :=
  from_source _ (g.source _ _ _ r.authenticated)

def selectedSourceView {p g tab w} (r : @SourceReceipt p g tab w) : GeneralDeclarativeHead320.State :=
  ⟨p.state.base.core.current.ordinary.normal,[r.field.folded.owner]⟩

/-- A genuine old ordinary compiler source-typing event on this exact
declared head, restricted to its separately authenticated owner row.
It does not invoke the name allocator, create support, or select a candidate. -/
structure InputTypingEvent {p : FullProblem} {g : SourceGate p}
    {tab : CheckedTable p.old.state.core.current} {w : SourceWire g} (r : SourceReceipt g tab w) where
  captures : List Occurrence
  ordinaryCompile :
    translate (authoredRegistry p.old.state.core.current).constructors
      (interpretation p.old.state.core.current.environment.source.snapshot)
      r.field.head.orig.original = some r.field.head.orig.code
  rootedTyping :
    Read (selectedSourceView r) .actual
      (.variable r.field.head.orig.capture.lower) r.field.head.orig.code captures

def readInputTypingEvent {p g tab w} (r : @SourceReceipt p g tab w) :
    Option (InputTypingEvent r) := do
  let orig := r.field.head.orig
  let c := (authoredRegistry p.old.state.core.current).constructors
  let interpretation := interpretation p.old.state.core.current.environment.source.snapshot
  if yes : GeneralDeclarativeWitnessLiteral349.eqExpr
      ((translate c interpretation orig.original).getD (.variable 0)) orig.code = true then
    match exactLegacy : translate c interpretation orig.original with
    | none => none
    | some code => do
      let target ← decode orig.code
      let index := ofRows (s := selectedSourceView r) [r.field.folded.owner] (fun _ got => got)
      match traced : run index .actual (.variable orig.capture.lower) target.val with
      | none => none
      | some got =>
        have same : code = orig.code :=
          GeneralDeclarativeWitnessLiteral349.eq_expr .. |>.mp (by simpa [exactLegacy] using yes)
        some ⟨got,exactLegacy.trans (congrArg some same),target.property ▸ sound index target.val traced⟩
  else none

def readSameInputTyping {p : FullProblem} (g : SourceGate p)
    (tab : CheckedTable p.old.state.core.current) (w : SourceWire g) :
    Option ((r : SourceReceipt g tab w) × InputTypingEvent r) := do
  let r ← readSourceFold g tab w
  let event ← readInputTypingEvent r
  pure ⟨r,event⟩

theorem same_input_typing_cannot_read_pending_output_support {p g tab w}
    (r : @SourceReceipt p g tab w) (a : InputTypingEvent r) :
    Read (selectedSourceView r) .actual
      (.variable r.field.head.orig.capture.lower) r.field.head.orig.code a.captures ∧
    r.field.folded.owner ∈ (restriction (inputSourceOnly g)).equations :=
  ⟨a.rootedTyping,original_input_row_is_in_source_only_restriction r⟩

end Yulang.GeneralDeclarativeI65.I72.LiteralFold471
