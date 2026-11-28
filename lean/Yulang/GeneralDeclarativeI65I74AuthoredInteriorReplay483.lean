import Yulang.GeneralDeclarativeI65I74AuthoredInterior483

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
open RetainedFull445 (FullProblem)
open Producer479 (Site siteAt readHop)
open LiteralVisits473 (StepWire Checkpoint readCheck)
open ObservationAlternatives473 (Positions oldPosition)
open GeneralDeclarativeWitnessOrigins350 (Table)
open GeneralDeclarativeWitnessLiteral349 (eqExpr eq_expr)

/-- Finite checks are independent of the combined reader: the two
continuations, the earlier authored site, and the final graph sign can
each be established on the original state before replay. -/
def InteriorPrerequisites {n : Nat} (p : FullProblem) (table : Table) (pos : Positions n)
    (rel : List (Fin n × Fin n)) (geom : Checkpoint n) (name : Nat)
    (before : Site p.old.state.core pos) (card : ReadCard) (move : StepWire)
    (physical : Fin n) (after : Checkpoint n) : Prop :=
  before.index = geom.which ∧
  ∃ cmp : AuthoredTerminalCompare p table pos rel geom name before.query card,
    readAuthoredTerminalCompare p table pos rel geom name before.query card = some cmp ∧
    cmp.sign = false ∧
    ∃ lexical : Site p.old.state.core pos,
      siteAt (s := p.old.state.core) (pos := pos) cmp.lexical before.pattern before.query = some lexical ∧
      lexical.index = cmp.lexical ∧ lexical.pattern = before.pattern ∧ lexical.query = before.query ∧
      (∃ out, readFocusedCardHop (p := p) table lexical move card physical = some out) ∧
      (∃ out, readHop before move after.which = some out) ∧
      ∃ bit, readCheck p.old.state.core pos rel (oldPosition pos after.which) after = some bit

private theorem siteAt_identity {s : GeneralDeclarativeI65.State} {pos : Positions n}
    {i : Fin n} {pattern code} {found : Site s pos}
    (run : siteAt i pattern code = some found) :
    found.index = i ∧ found.pattern = pattern ∧ found.query = code := by
  unfold siteAt at run
  split at run
  · cases run
  · have i := Option.some.inj run
    cases i
    exact ⟨rfl,rfl,rfl⟩

private theorem collect_success {A : Type} {o : Option A} {a : A} (eq : o = some a) :
    collectedForInterior o = some ⟨a,eq⟩ := by
  subst o
  rfl

private theorem pair_check_success {A : Type} {o : Option A} {a : A} (eq : o = some a) :
    checkedForPairedFocus o = some ⟨a,eq⟩ := by
  subst o
  rfl

theorem independent_finite_interior_checks_replay_the_exact_child
    {p : FullProblem} {table : Table} {pos : Positions n} {rel} {geom} {name}
    {before : Site p.old.state.core pos} {card move physical after}
    (ready : InteriorPrerequisites p table pos rel geom name before card move physical after) :
    ∃ result, readAuthoredInterior p table pos rel geom name before card move physical after = some result := by
  obtain ⟨atRoot,cmp,replay,safe,lexical,located,index,pattern,code,⟨author,authorRun⟩,⟨ambient,ambientRun⟩,
    bit,checked⟩ := ready
  unfold readAuthoredInterior
  simp only [atRoot,dite_true,replay,bind,Option.bind,safe]
  have lexicalRun : collectedForInterior (siteAt cmp.lexical before.pattern before.query) =
      some ⟨lexical,located⟩ := collect_success located
  have physicalRun : checkedForPairedFocus (readHop before move after.which) =
      some ⟨ambient,ambientRun⟩ := pair_check_success ambientRun
  have signRun : collectedForInterior (readCheck p.old.state.core pos rel (oldPosition pos after.which) after) =
      some ⟨bit,checked⟩ := collect_success checked
  simp [lexicalRun,index,readPairedFocusedHop,pattern,code,(eq_expr _ _).mpr rfl,authorRun,physicalRun,signRun,
    bind,Option.bind]

end Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
