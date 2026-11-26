import Yulang.GeneralDeclarativeI65I74CompletedLowerEntry438
import Yulang.GeneralDeclarativeI65GuardedWhereCenter400
import Yulang.GeneralNominalCenteredHeadMatCompletionCollisionPackets

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.MergedOutput439
open GeneralDeclarativeI65
open GeneralDeclarations (Clause Declaration Checked)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry point)
open GeneralDeclarativeWitnessCompiler350 (Context Finished execute preparation whereBatch placed)
open GeneralDeclarativeHead320 (Equation environment)
open GeneralNominalCenteredHeadMatExpressions (Expr translate value)
open GeneralSourceMetadataRows291 (interpretation)
open CommonNominalFullCarrier (Equivalent variant subtype_trans)
open CommonRoleOutermostResolver (Tree Summarizes)
open Checker408 (Problem Result)

def intCode : Expr := .primitive (.scalar .int) []
def tickCode : Expr := .variant 0 intCode

/-- A single merged child has this report position, and both original
source occurrences survive as evidence. This wrapper cannot be
represented by shortening the old literal `WhereForest`. -/
structure Original439 (s : I72.State) (q : Request) where
  frame : AuthoredBodyFrame393 s.core q
  sourceHead : SourceHead s.core q frame.decl
  checked : Checked (authoredRegistry s.core.current)
  oneParent : visible s.core q = [frame.decl]
  safe : ¬ RootCycle s q
  key : Nat
  sourceHeadSyntax : frame.decl.head = [.app key []]
  firstClause : Clause
  lastClause : Clause
  originalClauses : frame.decl.requirements = [firstClause,lastClause]
  distinctClauses : firstClause.id ≠ lastClause.id
  childRole : Nat
  outName : Nat
  firstEquation : GeneralDeclarations.Equation
  lastEquation : GeneralDeclarations.Equation
  firstRole : firstClause.role = childRole
  lastRole : lastClause.role = childRole
  firstArgs : firstClause.arguments = []
  lastArgs : lastClause.arguments = []
  firstOutput : firstClause.outputs = [firstEquation]
  lastOutput : lastClause.outputs = [lastEquation]
  firstName : firstEquation.name = outName
  lastName : lastEquation.name = outName
  firstRhs : firstEquation.rhs = .app key []
  lastRhs : lastEquation.rhs = .variant 0 (.app key [])
  firstCode : translate (authoredRegistry s.core.current).constructors
    (interpretation s.core.current.environment.source.snapshot) firstEquation.rhs = some intCode
  lastCode : translate (authoredRegistry s.core.current).constructors
    (interpretation s.core.current.environment.source.snapshot) lastEquation.rhs = some tickCode
  rootCell : Nat
  originalRootArgs : q.demand.arguments = [point rootCell]
  leftCell : Nat
  rightCell : Nat
  distinctCells : leftCell ≠ rightCell
  rootLeftDistinct : rootCell ≠ leftCell
  rootRightDistinct : rootCell ≠ rightCell
  leftKept : (⟨leftCell,intCode⟩ : Equation) ∈ s.core.current.ordinary.equations
  rightKept : (⟨rightCell,tickCode⟩ : Equation) ∈ s.core.current.ordinary.equations
  exactKids : frameWhereKids400 frame = [⟨q.occurrence ++ [0],⟨childRole,[],[⟨outName,leftCell⟩]⟩⟩,
    ⟨q.occurrence ++ [1],⟨childRole,[],[⟨outName,rightCell⟩]⟩⟩]
  compiler : Context
  compilerDeclaration : compiler.decl = frame.decl
  compilerRequest : compiler.demand = q.demand
  compilerRegistry : compiler.registry = authoredRegistry s.core.current
  compilerInterpretation : compiler.interp = interpretation s.core.current.environment.source.snapshot
  compilerState : compiler.named = s.core.current.ordinary
  prepared : GeneralDeclarativeHead320.State
  ports : List GeneralDeclarativeClauseBatch327.Port
  preparedExact : preparation compiler = some (prepared,ports)
  originalPlacement : frame.placement = placed compiler ports
  emittedExact : whereBatch compiler ports = some [⟨leftCell,intCode⟩,⟨rightCell,tickCode⟩]
  finished : Finished
  executed : execute compiler = some finished
  compilerKids : children q finished.kids = frameWhereKids400 frame
  compilerNoFixed : finished.fixed = []
  leaf : Declaration
  oneLeaf : visible s.core ⟨q.occurrence ++ [0],⟨childRole,[],[⟨outName,leftCell⟩]⟩⟩ = [leaf]
  leafHead : leaf.head = []
  leafWhere : leaf.requirements = []
  leafEquation : GeneralDeclarations.Equation
  leafBody : leaf.associated = [leafEquation]
  leafName : leafEquation.name = outName
  leafRhs : leafEquation.rhs = .app key []

/-- The report is on the canonical representative of the merged
child. Its two input source occurrences are not erased. -/
def Original439.representative {s q} (a : Original439 s q) : Request :=
  ⟨q.occurrence ++ [0],⟨a.childRole,[],[⟨a.outName,a.leftCell⟩,⟨a.outName,a.rightCell⟩]⟩⟩

def Original439.report {s q} (a : Original439 s q) : Result :=
  ⟨.selected a.frame.decl.id [.rejected],.rejected,[]⟩

theorem report_summarizes_merged_rejection439 {s q} (a : Original439 s q) :
    Summarizes a.report.tree a.report.verdict :=
  .selected (.cons .rejected .nil) (.rejected (by simp))

theorem same_unnamed_inputs_on_original_children439 {s q} (a : Original439 s q) :
    ∃ first last : Request, frameWhereKids400 a.frame = [first,last] ∧
      first.demand.role = last.demand.role ∧ first.demand.arguments = last.demand.arguments ∧
      first.occurrence = q.occurrence ++ [0] ∧ last.occurrence = q.occurrence ++ [1] ∧
      a.representative.occurrence = first.occurrence ∧
      a.representative.demand.outputs = [⟨a.outName,a.leftCell⟩,⟨a.outName,a.rightCell⟩] :=
  ⟨_,_,a.exactKids,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- The old literal forest cannot stand for the merged child: it has
one tree entry per original request. No older theorem is weakened. -/
theorem literal_forest_cannot_shorten_to_merged_child439 {s q}
    (a : Original439 s q) (R : SourcePrimitives) :
    ¬ Nonempty (WhereForest R s (frameWhereKids400 a.frame) [.rejected]) := by
  have length {qs} (f : WhereForest R s qs [.rejected]) : qs.length = 1 := by
    cases f with
    | cons head tail => cases tail; rfl
  rintro ⟨f⟩
  have count := length f
  rw [a.exactKids] at count
  cases count

theorem source_codes_and_compiler_rows439 {s q} (a : Original439 s q) :
    translate (authoredRegistry s.core.current).constructors
      (interpretation s.core.current.environment.source.snapshot) a.firstEquation.rhs = some intCode ∧
    translate (authoredRegistry s.core.current).constructors
      (interpretation s.core.current.environment.source.snapshot) a.lastEquation.rhs = some tickCode ∧
    whereBatch a.compiler a.ports = some [⟨a.leftCell,intCode⟩,⟨a.rightCell,tickCode⟩] ∧
    children q a.finished.kids = frameWhereKids400 a.frame :=
  ⟨a.firstCode,a.lastCode,a.emittedExact,a.compilerKids⟩

/-- Independent class equation added by merging the same named
output on the same unnamed input, not an equality assumed of the
original pre-merge model. -/
def Original439.MergedOutput {s q} (a : Original439 s q) (m : I72.Model) : Prop :=
  Equivalent (m.assignment a.leftCell).1 (m.assignment a.rightCell).1

structure ConflictMeaning439 {s q} (a : Original439 s q) (m : I72.Model) : Prop where
  firstOutput : Equivalent (m.assignment a.leftCell).1 (.base .int)
  lastOutput : Equivalent (m.assignment a.rightCell).1 (variant 0 (.base .int))
  conflict : ¬ a.MergedOutput m

theorem producer_rows_give_separate_meanings_and_merge_conflicts439 {s q}
    (a : Original439 s q) (m : I72.Model) (fit : Fits s m) : ConflictMeaning439 a m := by
  have first : Equivalent (m.assignment a.leftCell).1 (.base .int) := fit.1.1.2 _ a.leftKept
  have last : Equivalent (m.assignment a.rightCell).1 (variant 0 (.base .int)) := fit.1.1.2 _ a.rightKept
  refine ⟨first,last,fun same => ?_⟩
  exact GeneralNominalCenteredHeadMatCompletionCollisionPackets.int_not_variant
    ⟨subtype_trans first.2 (subtype_trans same.1 last.1),
      subtype_trans last.2 (subtype_trans same.2 first.1)⟩

theorem no_fitting_extension_equalizes_the_named_output439 {s q}
    (a : Original439 s q) : ¬ ∃ m : I72.Model, Fits s m ∧ a.MergedOutput m :=
  fun ⟨m,fit,merged⟩ => (producer_rows_give_separate_meanings_and_merge_conflicts439 a m fit).conflict merged

end Yulang.GeneralDeclarativeI65.I72.MergedOutput439
