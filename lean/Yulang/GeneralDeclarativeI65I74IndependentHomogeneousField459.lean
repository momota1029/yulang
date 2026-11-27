import Yulang.GeneralDeclarativeI65I74ClosedOriginalTagGrammar459
import Yulang.GeneralDeclarativeI65I74HomogeneousClosedEntry459

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.IndependentHomogeneousField459
open Yulang.GeneralDeclarativeI65
open GeneralDeclarationPatterns
open GeneralDeclarations (Declaration Clause)
open GeneralDeclarativeWhere319 (Capture)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessModeCoverage357 (DeclarationCovered)
open RecordTree455 (WrittenArgs checkTrees checkTrees_exact)
open RecordTrail455 (EmptyConstructor)
open Checker408 (Problem)
open RecordTraversal455.MixedQA (MixedPath)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open RoutedQueryHeader456 (QueryDecoder)
open RoutedNominalMixed456 (actualQueryDecoder)
open RoutedReadyMixed457 (ReportAtField)
open RoutedMixed456 (endsAtField)
open RetainedFull445 (FullProblem)
open NestedIdenticalTagProjection459
open IdenticalTagProjection459 (pruneRepeatedTagsArgs)
open HomogeneousWrittenHeader459 (ExactHomogeneousHeader)
open ClosedOriginalTagGrammar459 (WrittenOriginalArgs actual_original_args_have_auxiliary_closed_proof459
  auxiliary_closed_args_reflect_actual_original459)

/-- Independent declaration-side source evidence. The auxiliary head is
introduced by the inductive projection, not by the checker returning true.
Readiness is still for the original visible declaration. -/
structure OriginalHeader (p : Problem) (decode : QueryDecoder p.state.core) (d : Declaration) where
  emptyKey : Nat
  written : Pattern
  projected : List Pattern
  clause : Clause
  arg : Capture
  query : Expr
  only : visible p.state.core p.root = [d]
  head : d.head = [written]
  projection : ProjectionArgs d.head projected
  changed : projected ≠ d.head
  requirement : d.requirements = [clause]
  argv : p.root.demand.arguments = [arg]
  atCenter : arg.lower = arg.center ∧ arg.center = arg.upper
  noGoalOutputs : p.root.demand.outputs = []
  noWhereOutputs : clause.outputs = []
  actualEmpty : EmptyConstructor p ⟨emptyKey,0,[],[]⟩
  headGrammar : WrittenOriginalArgs emptyKey d.head
  oldUnavailable : ¬ WrittenArgs emptyKey (pruneRepeatedTagsArgs d.head)
  bodyShape : WrittenArgs emptyKey clause.arguments
  authoredRole : ∃ row ∈ p.state.core.current.environment.source.roles.rows,
    row.role = p.root.demand.role
  rolesValid : GeneralSourceMetadataRoles291.Valid p.state.core.current.environment.source.roles
  covered : DeclarationCovered p.state.core.current.environment d
  signature : d.Signature (authoredRegistry p.state.core.current).roles
  identified : d.Identified
  produced : d.Produced
  outputs : d.OutputOnly
  lexical : d.Scoped
  smaller : Smaller d.head clause.arguments
  translation : decode.declarative (normalize written) query

def restore {p decode d} (s : OriginalHeader p decode d) :
    HomogeneousReadyHeader459.AuthoredHeader p decode d := by
  have know := projection_args_preserve_their_exact_data_read459 s.projection
  have written : WrittenArgs s.emptyKey (projectedArgs d.head) :=
    actual_original_args_have_auxiliary_closed_proof459 s.headGrammar
  have same : ExactHomogeneousHeader p.state.core.current d s.clause s.emptyKey :=
    ⟨s.requirement,s.covered,s.signature,s.identified,s.produced,s.outputs,s.lexical,written,s.bodyShape,s.smaller⟩
  have noBinary : checkTrees s.emptyKey (pruneRepeatedTagsArgs d.head) = false := by
    cases old : checkTrees s.emptyKey (pruneRepeatedTagsArgs d.head)
    · rfl
    · exact False.elim (s.oldUnavailable ((checkTrees_exact ..).mp old))
  exact ⟨s.emptyKey,s.written,s.clause,s.arg,s.query,s.only,s.head,s.requirement,s.argv,s.atCenter,
    s.noGoalOutputs,s.noWhereOutputs,s.actualEmpty,written,s.bodyShape,s.authoredRole,
    s.rolesValid,same,fun e => s.changed (know.symm.trans e),noBinary,s.translation⟩

def disclose {p decode d} (s : HomogeneousReadyHeader459.AuthoredHeader p decode d) :
    OriginalHeader p decode d := by
  refine ⟨s.emptyKey,s.written,projectedArgs d.head,s.clause,s.arg,s.query,s.only,s.head,
    projected_real_source_arguments_have_derivation459 d.head,s.genuinelyRepeated,s.requirement,s.argv,s.atCenter,
    s.noGoalOutputs,s.noWhereOutputs,s.actualEmpty,
    auxiliary_closed_args_reflect_actual_original459 s.emptyKey d.head s.admissibleHead,?_,
    s.admissibleBody,s.authoredRole,s.rolesValid,s.preserved.cover,s.preserved.sig,s.preserved.identified,
    s.preserved.produced,s.preserved.outputs,s.preserved.scope,s.preserved.small,s.translated⟩
  intro old
  have yes := (checkTrees_exact ..).mpr old
  rw [s.oldWrittenSpellingUnavailable] at yes
  cases yes

theorem homogeneous_closed_header_from_inductive_source_is_replayed459
    {p decode d} (s : OriginalHeader p decode d) :
    HomogeneousReadyHeader459.readReadyHeader p decode d s.only s.emptyKey = some (restore s) :=
  HomogeneousReadyHeader459.actual_original_homogeneous_header_replays459 (restore s)

theorem inductive_original_header_supplies_original_declaration_ready459
    {p decode d} (s : OriginalHeader p decode d) :
    GeneralDeclarativeWitnessClassifyVariance357.DeclarationReady (authoredRegistry p.state.core.current) d :=
  HomogeneousReadyHeader459.exact_homogeneous_header_supplies_original_ready459 (restore s)

theorem independent_header_projection_is_unique459 {p decode d}
    (left right : OriginalHeader p decode d) : left.projected = right.projected :=
  (projection_args_preserve_their_exact_data_read459 left.projection).symm.trans
    (projection_args_preserve_their_exact_data_read459 right.projection)

structure Derivation (p : Problem) where
  declaration : Declaration
  source : OriginalHeader p (actualQueryDecoder p.state.core) declaration
  path : MixedPath
  terminal : Nat
  visited : AuthenticatedHop458.Trail p.state.core.current.ordinary (InlineStructuralPolicy458.policy p.state.core)
    source.arg.lower source.query path terminal true
  cycle : AliasCycle p.state.core.current.ordinary (observed p.state.core.current.ordinary) terminal
  ends : endsAtField path terminal = true

def Derivation.report {p : Problem} (a : Derivation p) : ReportAtField :=
  ⟨p.root.occurrence,a.declaration.id,0,a.source.clause.id,a.path,a.terminal⟩

def Derivation.toChecked {p : Problem} (a : Derivation p) : HomogeneousClosedEntry459.FieldDerivation p :=
  ⟨a.declaration,restore a.source,a.path,a.terminal,a.visited,a.cycle,a.ends⟩

def Derivation.fromChecked {p : Problem} (a : HomogeneousClosedEntry459.FieldDerivation p) : Derivation p :=
  ⟨a.declaration,disclose a.source,a.path,a.terminal,a.visited,a.cycle,a.fieldEnd⟩

def IndependentExactReport (p : Problem) (report : ReportAtField) : Prop :=
  ∃ actual : Derivation p, actual.report = report

theorem exact_current_homogeneous_report_iff_inductive_original_source459
    (p : Problem) (report : ReportAtField) :
    HomogeneousClosedEntry459.ExactField p report ↔ IndependentExactReport p report := by
  constructor
  · rintro ⟨a,eq⟩
    exact ⟨.fromChecked a,eq⟩
  · rintro ⟨a,eq⟩
    exact ⟨a.toChecked,eq⟩

theorem independent_exact_report_iff_same_full_finite_witness459
    (p : FullProblem) (report : ReportAtField) :
    IndependentExactReport p.old report ↔
      ∃ w, HomogeneousClosedEntry459.check_full_homogeneous459 p (.fieldK2 report) (.fieldK2 w) = true := by
  rw [←exact_current_homogeneous_report_iff_inductive_original_source459]
  exact (HomogeneousClosedEntry459.actual_routed_field_report_iff_finite_wire459 p.old report).symm

theorem checked_report_keeps_inductive_source_and_same_fit459
    (p : FullProblem) (report : ReportAtField) (w : HomogeneousClosedEntry459.FieldWire)
    (yes : HomogeneousClosedEntry459.check_full_homogeneous459 p (.fieldK2 report) (.fieldK2 w) = true) :
    IndependentExactReport p.old report ∧ ∀ m, FitsFull p.state m →
      HomogeneousClosedEntry459.FieldEvidence p.old m report := by
  exact ⟨(independent_exact_report_iff_same_full_finite_witness459 ..).mpr ⟨w,yes⟩,
    (HomogeneousClosedEntry459.check_full_sound459 p _ _ yes).2⟩

end Yulang.GeneralDeclarativeI65.I72.IndependentHomogeneousField459
