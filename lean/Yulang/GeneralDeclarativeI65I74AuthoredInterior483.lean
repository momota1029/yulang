import Yulang.GeneralDeclarativeI65I74PairedFocusedHop483
import Yulang.GeneralDeclarativeI65I74AuthoredTerminalCompare482

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
open RetainedFull445 (FullProblem)
open Producer479 (Site siteAt)
open LiteralVisits473 (StepWire Checkpoint readCheck read_checkpoint_guards)
open ObservationAlternatives473 (Positions oldPosition graphOf)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open GeneralDeclarativeRepeatedActual323 (eqAt)
open GeneralDeclarativeTermWalk322 (Walk)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeOrigins321 (Supported)
open InputCoordinates475 (rawAt)
open WrittenPattern460.PhysicalOrigin (atSource)
open QuotientObservation471 (ReturnsUpToEquality)

structure AuthoredInterior {n : Nat} (p : FullProblem) (table : Table) (pos : Positions n)
    (rel : List (Fin n × Fin n)) (geom : Checkpoint n) (name : Nat)
    (before : Site p.old.state.core pos) (card : ReadCard) (move : StepWire)
    (physical : Fin n) (after : Checkpoint n) where
  comparison : AuthoredTerminalCompare p table pos rel geom name before.query card
  incoming : before.index = geom.which
  safe : comparison.sign = false
  literary : Site p.old.state.core pos
  actualSite : siteAt (s := p.old.state.core) (pos := pos)
    comparison.lexical before.pattern before.query = some literary
  literaryIndex : literary.index = comparison.lexical
  paired : PairedFocusedHop (p := p) table literary before move card physical after.which
  bit : Bool
  checked : readCheck p.old.state.core pos rel (oldPosition pos after.which) after = some bit

def collectedForInterior {A : Type} (x : Option A) : Option {y // x = some y} :=
  match x with | none => none | some y => some ⟨y,rfl⟩

/-- Open one selected interior child only after independently checking the
old authored comparison at the shared incoming named position. The
physical receipt is not a substitute for the independently read card. -/
def readAuthoredInterior {n : Nat} (p : FullProblem) (table : Table) (pos : Positions n)
    (rel : List (Fin n × Fin n)) (geom : Checkpoint n) (name : Nat)
    (before : Site p.old.state.core pos) (card : ReadCard) (move : StepWire)
    (physical : Fin n) (after : Checkpoint n) :
    Option (AuthoredInterior p table pos rel geom name before card move physical after) := do
  if same : before.index = geom.which then
    let compare ← readAuthoredTerminalCompare p table pos rel geom name before.query card
    if safe : compare.sign = false then
      let precise ← collectedForInterior (siteAt (s := p.old.state.core) (pos := pos)
        compare.lexical before.pattern before.query)
      if index : precise.val.index = compare.lexical then
        let pair ← readPairedFocusedHop (p := p) table precise.val before move card physical after.which
        let sign ← collectedForInterior (readCheck p.old.state.core pos rel (oldPosition pos after.which) after)
        some ⟨compare,same,safe,precise.val,precise.property,index,pair,sign.val,sign.property⟩
      else none
    else none
  else none

theorem checked_interior_compares_a_literal_child_without_transferring_source_authority
    {n : Nat} {p : FullProblem} {table : Table} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {geom : Checkpoint n} {name : Nat}
    {before : Site p.old.state.core pos} {card : ReadCard} {move : StepWire}
    {physical : Fin n} {after : Checkpoint n}
    {done : Nat → Prop} {support : Supported (rawAt p) done}
    (attached : Attached (rawAt p) table)
    (authored : ∀ row ∈ table.authored, support.derivesFrom row .source)
    (out : AuthoredInterior p table pos rel geom name before card move physical after) :
    oldPosition pos before.index = .logical name ∧
    oldPosition pos out.literary.index = .rowPos out.comparison.author.ordinals.raw [] ∧
    (¬ ReturnsUpToEquality (graphOf p.old.state.core pos) before.index) ∧
    atSource before.pattern move.written = some out.paired.ambient.pattern ∧
    after.which = out.paired.ambient.index ∧
    (out.bit = true ↔ ReturnsUpToEquality (graphOf p.old.state.core pos) out.paired.author.after.index) ∧
    ∃ rebuilt : Expr,
      (∀ m : Model, FitsFull p.state m → eqAt m.assignment out.paired.author.after.term rebuilt) ∧
      Walk .actual rebuilt out.paired.author.after.query out.paired.author.uses := by
  have root := read_checkpoint_guards out.comparison.checkedSign
  have geometryKnown := root.1.2.2.2.2.2 geom.which (.nil _)
  have literaryKnown :=
    ObservationAlternatives473.proved_same_observation_cannot_replace_a_resolved_alternative_with_unknown
      _ _ _ out.comparison.agrees geometryKnown
  have sameObs : CommonRoleGraphBisimulation.ObservationallyEqual (graphOf p.old.state.core pos)
      out.literary.index before.index := by
    rw [out.literaryIndex,out.incoming]
    exact fun i => (out.comparison.agrees i).symm
  have actual := paired_focused_hop_keeps_exact_pose_geometry_and_authored_meaning
    out.paired root.1.2.1 (out.literaryIndex.symm ▸ literaryKnown)
      (out.incoming.symm ▸ geometryKnown) sameObs attached authored
  have finish := read_checkpoint_guards out.checked
  refine ⟨out.incoming.symm ▸ root.2.1,out.literaryIndex.symm ▸ out.comparison.spelled,
    ?_,?_,actual.2.1,?_,actual.2.2.2.2.2⟩
  · intro bad
    have hits := root.2.2.mpr (out.incoming ▸ bad)
    rw [out.safe] at hits
    cases hits
  · rw [←out.paired.original]
    exact actual.2.2.2.1 ▸ actual.2.2.1
  · have signed := actual.2.1 ▸ finish.2.2
    exact signed.trans actual.2.2.2.2.1.symm

end Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
