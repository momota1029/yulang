import Yulang.GeneralDeclarativeI65I74AuthoredFullRead482
import Yulang.GeneralDeclarativeI65I74ScopedRouteSound480
import Yulang.GeneralDeclarativeI65I74SourceExposureMeaning481
import Yulang.GeneralDeclarativeI65I74G04Producer479

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable PrecheckedHead readPrecheckedHead)
open ObservationAlternatives473 (Positions)
open Producer479 (RouteWire PriorPhase readRoute)
open InputCoordinates475 (rawAt SamePhaseInputObservation478 SourceIndexPair478)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWitnessOrigins350 (attach)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeTermWalk322 (Occurrence Walk)
open GeneralDeclarativeRepeatedActual323 (eqAt)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeInlineTrace331 (Read realize)

structure AuthoredCardRouteReceipt where
  output : SamePhaseInputObservation478
  initialIndices : SourceIndexPair478
  used : List Occurrence

private def safeCell {n : Nat} (positions : Positions n) (route : RouteWire n) : Nat :=
  (positions.cells.get route.trail.cursor.which).oldOrdinal

/-- Coupling at the exact root only. Old selected route is independently
checked; this does not certify correspondence at its deeper locations. -/
def runRootPinnedAuthoredCard {n : Nat} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current)
    (positions : Positions n) (rel : List (Fin n × Fin n)) (basis : PriorPhase)
    (route : RouteWire n) (card : ReadCard) (expectedAuthor : Nat) : Option AuthoredCardRouteReceipt := do
  let _ ← attach (rawAt p) basis.authors
  let head ← readPrecheckedHead (p := p.old) gd ⟨0,route.argument⟩
  let (selected,row) ← readNamedCardRoot (rawAt p) basis.authors head.orig.capture.lower head.orig.code card
  if selected.ordinals.raw = safeCell positions route ∧ selected.ordinals.author = expectedAuthor ∧
      row.left = head.orig.capture.lower then
    let used ← runReadCard (rawAt p) basis.authors .actual (.variable head.orig.capture.lower) head.orig.code card
    let answer ← readRoute p gd positions rel route
    pure ⟨answer,selected.ordinals,used⟩
  else none

theorem actual_root_pinned_read_iff
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {positions : Positions n} {rel : List (Fin n × Fin n)} {basis : PriorPhase}
    {route : RouteWire n} {card : ReadCard} {expectedAuthor : Nat} {out : AuthoredCardRouteReceipt} :
    runRootPinnedAuthoredCard p gd positions rel basis route card expectedAuthor = some out ↔
    ∃ (attached : GeneralDeclarativeWitnessOrigins350.Attached (rawAt p) basis.authors)
      (head : PrecheckedHead (p := p.old) gd) (exposure : ExposureWire) (row : Equation),
      attach (rawAt p) basis.authors = some attached ∧
      readPrecheckedHead gd ⟨0,route.argument⟩ = some head ∧
      readNamedCardRoot (rawAt p) basis.authors head.orig.capture.lower head.orig.code card = some (exposure,row) ∧
      exposure.ordinals = out.initialIndices ∧ out.initialIndices.raw = safeCell positions route ∧
      out.initialIndices.author = expectedAuthor ∧ row.left = head.orig.capture.lower ∧
      runReadCard (rawAt p) basis.authors .actual (.variable head.orig.capture.lower) head.orig.code card = some out.used ∧
      readRoute p gd positions rel route = some out.output := by
  constructor
  · intro ran
    unfold runRootPinnedAuthoredCard at ran
    cases table : attach (rawAt p) basis.authors with
    | none => simp [table,bind,Option.bind] at ran
    | some attached =>
      simp only [table,bind,Option.bind] at ran
      cases source : readPrecheckedHead (p := p.old) gd ⟨0,route.argument⟩ with
      | none => simp [source] at ran
      | some head =>
        simp only [source] at ran
        cases exposed : readNamedCardRoot (rawAt p) basis.authors head.orig.capture.lower head.orig.code card with
        | none => simp [exposed] at ran
        | some pair =>
          rcases pair with ⟨wire,row⟩
          simp only [exposed] at ran
          split at ran
          · rename_i pinned
            cases ranCard : runReadCard (rawAt p) basis.authors .actual
                (.variable head.orig.capture.lower) head.orig.code card with
            | none => simp [ranCard] at ran
            | some used =>
              cases oldRoute : readRoute p gd positions rel route with
              | none => simp [ranCard,oldRoute] at ran
              | some answer =>
                simp only [ranCard,oldRoute,pure,Option.some.injEq] at ran
                cases ran
                exact ⟨attached,head,wire,row,rfl,rfl,exposed,rfl,pinned.1,pinned.2.1,pinned.2.2,ranCard,rfl⟩
          · cases ran
  · rintro ⟨attached,head,wire,row,table,source,exposed,index,rawIndex,authorIndex,rowName,typing,geometry⟩
    cases out
    simp_all [runRootPinnedAuthoredCard,bind,Option.bind,pure]

theorem successful_root_pin_preserves_exact_ordinary_origins_and_same_fit
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {positions : Positions n} {rel : List (Fin n × Fin n)} {basis : PriorPhase}
    {route : RouteWire n} {card : ReadCard} {expectedAuthor : Nat} {out : AuthoredCardRouteReceipt}
    {done : Nat → Prop} {support : Supported (rawAt p) done}
    (authority : ∀ row ∈ basis.authors.authored, support.derivesFrom row .source)
    (ran : runRootPinnedAuthoredCard p gd positions rel basis route card expectedAuthor = some out) :
    readRoute p gd positions rel route = some out.output ∧
    ∃ (head : PrecheckedHead (p := p.old) gd) (row : Equation) (rebuilt : Expr),
      readPrecheckedHead gd ⟨0,route.argument⟩ = some head ∧
      (rawAt p).equations[(safeCell positions route)]? = some row ∧
      basis.authors.authored[expectedAuthor]? = some row ∧ row.left = head.orig.capture.lower ∧
      support.derivesFrom row .source ∧
      (∀ m : Model, FitsFull p.state m → eqAt m.assignment (.variable head.orig.capture.lower) rebuilt) ∧
      Walk .actual rebuilt head.orig.code out.used := by
  obtain ⟨att,head,wire,row,_,source,exposed,index,rawIndex,authorIndex,rowName,typing,geometry⟩ :=
    actual_root_pinned_read_iff.mp ran
  obtain ⟨raw,prior,_⟩ := recorded_root_is_a_real_ordinal_read exposed
  have read := genuine_authored_reads_transport_into_same_support481 authority (runReadCard_sound typing)
  have derived := authority row (List.mem_of_getElem? prior)
  obtain ⟨rebuilt,means,walk⟩ := realize read
  exact ⟨geometry,head,row,rebuilt,source,((congrArg SourceIndexPair478.raw index).trans rawIndex) ▸ raw,
    ((congrArg SourceIndexPair478.author index).trans authorIndex) ▸ prior,rowName,derived,fun m fit => means m.assignment fit.1.1.1,walk⟩

end Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
