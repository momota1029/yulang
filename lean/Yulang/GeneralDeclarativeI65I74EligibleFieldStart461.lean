import Yulang.GeneralDeclarativeI65I74ScopedSourceReport460
import Yulang.GeneralDeclarativeI65I74HomogeneousClosedEntry459

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.EligibleFieldStart461
open Yulang.GeneralDeclarativeI65
open Yulang.GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarations (Declaration Clause)
open GeneralDeclarativeWhere319 (Capture)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessClassifyVariance357 (DeclarationReady)
open GeneralSourceMetadataRoles291 (Valid)
open AuthoredInspectQuery456 (AuthoredQuery)
open RoutedNominalMixed456 (actualQueryDecoder)
open Checker408 (Problem)
open WrittenPattern460

/-- The currently justified diagnostic-start cut. None of these premises is
inferred from a spelling grammar, from a raw path, or from a report. -/
structure EligibleStart (p : Problem) where
  declaration : Declaration
  original : Pattern
  clause : Clause
  argument : Capture
  query : Expr
  visibleOnly : visible p.state.core p.root = [declaration]
  originalHead : declaration.head = [original]
  originalWhere : declaration.requirements = [clause]
  originalArguments : p.root.demand.arguments = [argument]
  point : argument.lower = argument.center ∧ argument.center = argument.upper
  noGoalOutputs : p.root.demand.outputs = []
  noWhereOutputs : clause.outputs = []
  role : ∃ row ∈ p.state.core.current.environment.source.roles.rows,
    row.role = p.root.demand.role
  rolesValid : Valid p.state.core.current.environment.source.roles
  ready : DeclarationReady (authoredRegistry p.state.core.current) declaration
  compiled : AuthoredQuery p.state.core (normalize original) query

def EligibleStart.anchor {p : Problem} (a : EligibleStart p) : OriginalAnchor p :=
  ⟨⟨0,0,0⟩,a.declaration,a.original,a.clause,a.argument,a.query,
    by rw [a.visibleOnly]; rfl,by rw [a.originalHead]; rfl,
    by rw [a.originalArguments]; rfl,by rw [a.originalWhere]; rfl,a.compiled⟩

def fromReady {p : Problem} {d : Declaration}
    (h : RoutedReadyHeader457.AuthoredHeader p (actualQueryDecoder p.state.core) d) :
    EligibleStart p :=
  ⟨d,h.written,h.clause,h.arg,h.query,h.only,h.head,h.requirement,h.argv,h.atCenter,
    h.noGoalOutputs,h.noWhereOutputs,h.authoredRole,h.rolesValid,
    RecordDiagnosticReady457.actual_closed_header_supplies_prior_declaration_ready457 h.preserved,
    h.translated⟩

def fromHomogeneous {p : Problem} {d : Declaration}
    (h : HomogeneousReadyHeader459.AuthoredHeader p (actualQueryDecoder p.state.core) d) :
    EligibleStart p :=
  ⟨d,h.written,h.clause,h.arg,h.query,h.only,h.head,h.requirement,h.argv,h.atCenter,
    h.noGoalOutputs,h.noWhereOutputs,h.authoredRole,h.rolesValid,
    HomogeneousWrittenHeader459.homogeneous_header_proves_actual_original_ready459 h.preserved,
    h.translated⟩

theorem exact_system_source_index_and_original_clause {p : Problem} (a : EligibleStart p) :
    readOriginalAnchor p ⟨0,0,0⟩ = some a.anchor ∧
    readSite a.declaration (.head 0) = some (readTerm a.original) ∧
    ∀ i original, a.clause.arguments[i]? = some original →
      readSite a.declaration (.clause 0 a.clause.id i) = some (readTerm original) := by
  refine ⟨every_independent_anchor_replays a.anchor,
    original_at_iff_site_read.mpr (address_from_original_declaration_is_exact a.anchor),?_⟩
  intro i original yes
  exact original_at_iff_site_read.mpr (anchor_original_where_input_is_same_declared_site a.anchor yes)

theorem source_readiness_and_role_are_of_exact_original_visible_slot {p : Problem} (a : EligibleStart p) :
    DeclarationReady (authoredRegistry p.state.core.current) a.anchor.declaration ∧
      a.anchor.capture.lower = a.anchor.capture.center ∧
      a.anchor.capture.center = a.anchor.capture.upper ∧
      (∃ row ∈ p.state.core.current.environment.source.roles.rows, row.role = p.root.demand.role) ∧
      a.anchor.clause.outputs = [] := by
  exact ⟨a.ready,a.point.1,a.point.2,a.role,a.noWhereOutputs⟩

end Yulang.GeneralDeclarativeI65.I72.EligibleFieldStart461
