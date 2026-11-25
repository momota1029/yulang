import Yulang.GeneralDeclarativeI65I73RuleUnionInclusions407
import Yulang.GeneralDeclarativeWitnessCycle350
import Yulang.GeneralDeclarativeWitnessHeader349
import Yulang.GeneralDeclarativeWitnessModeCoverage357
import Yulang.GeneralDeclarativeWitnessTree349

namespace Yulang.GeneralDeclarativeI65.I72.Check408
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (Tree Dictionary Summarizes)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessTree349 (eqTree eqResult)
open GeneralDeclarativeI65.I72 (R0 Classifies Fits DictionaryEvidence)

structure Problem where
  state : I72.State
  root : I72.Request

/-- A nonflattened wire for a type expression and its argument-kind data.
This cycle never accepts a nonempty writes list; future branches will
need exact replay rather than merely comparing its constructor names. -/
inductive TypeWire where
  | node (tag : Nat) (data : List Nat) (ordered : List TypeWire)
  deriving Repr

structure Write where
  occurrence : List Nat
  declarationOrdinal : Nat
  outputOrdinal : Nat
  target : GeneralSourceState.Output
  body : GeneralDictionaryAssociatedProvenance.Body
  typedRhs : TypeWire

structure Result where
  tree : Tree
  verdict : CommonRoleOutermostResolver.Result
  writes : List Write

inductive Witness where
  | rawRoot (cycle : GeneralDeclarativeWitnessCycle350.Wire)
  | nullary
  | unsupported

def matchesNoWrites (r : Result) (tree : Tree) (out : CommonRoleOutermostResolver.Result) : Bool :=
  (eqTree r.tree tree && eqResult r.verdict out) && r.writes.isEmpty

def checksNullary (p : Problem) (d : Declaration) : Bool :=
  let source := p.state.core.current.environment.source
  GeneralSourceMetadataRoles291.check source.roles &&
  GeneralDeclarativeWitnessProblem349.covered source &&
  GeneralDeclarativeWitnessHeader349.checkedRegistry source &&
  GeneralDeclarativeWitnessModeCoverage357.checkDecl p.state.core.current.environment d &&
  d.head.isEmpty && d.requirements.isEmpty &&
  p.root.demand.arguments.isEmpty && p.root.demand.outputs.isEmpty

/-- The full visible list is recovered from this Problem. No declaration,
source table, dictionary, bound or output is provided by the Witness. -/
def check (p : Problem) (r : Result) : Witness → Bool
  | .rawRoot cycle =>
    GeneralDeclarativeWitnessCycle350.check p.state.core.current.ordinary p.root.demand cycle &&
      matchesNoWrites r .rejected .rejected
  | .nullary =>
    match visible p.state.core p.root with
    | [d] =>
      checksNullary p d && matchesNoWrites r (.selected d.id []) (.selected (.node d.id []))
    | _ => false
  | .unsupported => false

end Yulang.GeneralDeclarativeI65.I72.Check408
