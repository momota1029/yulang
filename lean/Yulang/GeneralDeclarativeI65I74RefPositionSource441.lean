import Yulang.GeneralDeclarativeI65I74InvariantList410
import Yulang.GeneralDeclarativeI65I74ExactEscape410

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RefPositions441
open GeneralDeclarativeI65
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeWhere319 (Capture)
open CommonRecursiveNominalIntervals (Endpoint Bounds ContextWellFormed Argument)
open CommonDeclaredNominalInspection (Parameter)
open GeneralDeclarativeWitnessDeclaredState357 (point authoredRegistry)
open GeneralDeclarativeWitnessConstructorModes357 (Use)
open GeneralDeclarativeWitnessSparseIntervals357 (names visited visitedList Legal)
open GeneralDeclarativeWitnessModeCoverage357 (DeclarationCovered)
open GeneralDeclarations (Declaration DeclarationChecked)
open Core.PresenceGeneration (TyTerm RowTerm)
open PresenceNormalForm (Atom)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeInspect321 (Visit PatternK2)
open GeneralDeclarativeGraphRows321 (structural observed)

def rowCov : Parameter := ⟨.row,.covariant⟩
def valueInv : Parameter := ⟨.value,.invariant⟩
def layout : List Parameter := [rowCov,valueInv]

def pattern (key rowBinder valueBinder : Nat) : Pattern :=
  .app key [.var rowBinder,.var valueBinder]

def inspectionPattern (key rowBinder valueBinder : Nat) : Expr :=
  .nominal key [.variable rowBinder,.variable valueBinder]

def rowArg (r : Nat) : Argument Nat := .inr (.point (.var r))
def valueArg (v : Nat) : Argument Nat := .inl (.point (.ordinary (.var v)))
def endpoint (key r v : Nat) : Endpoint Nat := .nominal key [rowArg r,valueArg v]

/-- The two leaves are binders in the actual candidate.
The abstract raw visit shape does not encode the row as a value. -/
theorem two_bindings_visit_only_root441 {view : GeneralDeclarativeK2Graph321.View}
    {root key rowBinder valueBinder site}
    (visit : Visit view root (inspectionPattern key rowBinder valueBinder) site) :
    site = root := by
  cases visit with
  | here => rfl
  | nominal _ chosen _ nested =>
    have binder := List.mem_of_getElem? chosen
    simp only [List.mem_cons,List.not_mem_nil,or_false] at binder
    rcases binder with rfl|rfl <;>
      exact False.elim (GeneralDeclarativeInspect321.variable_has_no_visit nested)

structure Original (s : I72.State) (q : Request) (d : Declaration) where
  only : visible s.core q = [d]
  checked : DeclarationChecked (authoredRegistry s.core.current).constructors
    (authoredRegistry s.core.current).roles d
  covered : DeclarationCovered s.core.current.environment d
  noWhere : d.requirements = []
  noOutputs : q.demand.outputs = []
  arg : Capture
  asked : q.demand.arguments = [arg]
  key : Nat
  rowBinder : Nat
  valueBinder : Nat
  separateBinders : rowBinder ≠ valueBinder
  written : d.head = [pattern key rowBinder valueBinder]
  original : Origin
  authored : original ∈ s.core.origins
  issuer : original.issuer = q.occurrence
  lower : original.slot = arg.lower
  center : original.slot = arg.center
  upper : original.slot = arg.upper
  rowName : Nat
  valueName : Nat
  read : original.endpoint = endpoint key rowName valueName
  use : Use s.core.current.environment key 2
  fromBody : use.mode = .declared layout
  table : s.core.modes[key]? = some layout
  rowAtom : Atom.rowLe (.var rowName) (.var rowName) ∈ s.core.current.ordinary.normal.ordinary
  valueAtom : Atom.tyLe (.var valueName) (.var valueName) ∈ s.core.current.ordinary.normal.ordinary
  safe : ¬RootCycle s q

def Original.capture {s q d} (a : Original s q d) (n : Nat) : Capture :=
  if n = a.rowBinder then point a.rowName
  else if n = a.valueBinder then point a.valueName else emptyCapture403

theorem Original.rowCapture {s q d} (a : Original s q d) :
    a.capture a.rowBinder = point a.rowName := by simp [Original.capture]

theorem Original.valueCapture {s q d} (a : Original s q d) :
    a.capture a.valueBinder = point a.valueName := by
  simp [Original.capture,a.separateBinders.symm]

theorem Original.preserveRow {s q d} (a : Original s q d) :
    RowBind s.core (a.capture a.rowBinder) (.var a.rowName) (.var a.rowName) := by
  rw [a.rowCapture]
  exact ⟨a.rowAtom,a.rowAtom,a.rowAtom,a.rowAtom⟩

theorem Original.preserveValue {s q d} (a : Original s q d) :
    ValueBind s.core (a.capture a.valueBinder) (.var a.valueName) (.var a.valueName) := by
  rw [a.valueCapture]
  exact ⟨a.valueAtom,a.valueAtom,a.valueAtom,a.valueAtom⟩

theorem Original.mode {s q d} (a : Original s q d) : names a.use.mode 2 = some layout := by
  rw [a.fromBody]
  rfl

theorem Original.wellFormed {s q d} (a : Original s q d) :
    ContextWellFormed s.core.modes false (endpoint a.key a.rowName a.valueName) :=
  .nominal a.table (.cons (.rowPoint false .covariant (.var _)) (.cons (.valuePoint (.ordinary true _)) (.nil false)))

def Original.compare {s q d} (a : Original s q d) :
    DeclaredComparison s.core.current.environment s.core.current.ordinary s.core.modes false
      (endpoint a.key a.rowName a.valueName) (endpoint a.key a.rowName a.valueName) where
  actualSource := by
    intro site member
    have one : site = (a.key,2) := by
      simpa [endpoint,rowArg,valueArg,visited.eq_def,visitedList.eq_def] using member
    subst site
    exact ⟨a.use,layout,a.mode,a.table⟩
  left := a.wellFormed
  right := a.wellFormed
  compared := .nominal a.table (.cons (.covariantRow a.rowAtom) (.cons
    (.invariantValue (.ordinary a.valueAtom) (.ordinary a.valueAtom)
      (.ordinary a.valueAtom) (.ordinary a.valueAtom)) .nil))

def Original.window {s q d} (a : Original s q d) :
    ModeWindow s.core a.arg (pattern a.key a.rowBinder a.valueBinder) :=
  ⟨a.original,a.original,a.lower ▸ .direct,a.upper ▸ .direct,a.authored,a.authored,
    a.key,[.var a.rowBinder,.var a.valueBinder],rfl,_,_,a.read,a.read,by rw [a.read]; exact a.compare⟩

abbrev Original.rowBinding {s q d} (a : Original s q d) : Binding :=
  .row a.rowBinder (.var a.rowName) (.var a.rowName)
abbrev Original.valueBinding {s q d} (a : Original s q d) : Binding :=
  .value a.valueBinder (.var a.valueName) (.var a.valueName)

def Original.head {s q d} (a : Original s q d) : SourceHead s.core q d := by
  refine .ordered a.capture ?_
  rw [a.asked,a.written]
  refine .cons (.declared (found := [a.rowBinding,a.valueBinding,a.valueBinding]) a.window ?_) .nil
  change DeepRead s.core a.capture false (pattern a.key a.rowBinder a.valueBinder)
    a.original.endpoint a.original.endpoint [a.rowBinding,a.valueBinding,a.valueBinding]
  rw [a.read]
  have first : DeepArgument s.core a.capture false rowCov (.var a.rowBinder)
      (rowArg a.rowName) (rowArg a.rowName) [a.rowBinding] :=
    .covariantRow a.preserveRow
  let leaf : Endpoint Nat := .ordinary (.var a.valueName)
  let span : Bounds (Endpoint Nat) := .point leaf
  have leafRead : DeepRead s.core a.capture true (.var a.valueBinder) leaf leaf [a.valueBinding] :=
    .bind a.preserveValue
  have second : DeepArgument s.core a.capture true valueInv (.var a.valueBinder)
      (.inl span) (.inl span) ([a.valueBinding] ++ [a.valueBinding]) :=
    .invariantValue (a := span) (b := span) leafRead leafRead
  have args : DeepArguments s.core a.capture false layout [.var a.rowBinder,.var a.valueBinder]
      [rowArg a.rowName,.inl span] [rowArg a.rowName,.inl span]
      ([a.rowBinding] ++ (([a.valueBinding] ++ [a.valueBinding]) ++ [])) :=
    .cons first (.cons second .nil)
  exact .nominal a.use a.mode a.table args

theorem actual_typed_positions_mean_in_same_model441 {s q d} (a : Original s q d)
    (m : I72.Model) (fit : I72.Fits s m) :
    WindowMeaning a.window m ∧ Binding.Denotes a.capture m a.rowBinding ∧
    Binding.Denotes a.capture m a.valueBinding :=
  ⟨mode_window_sound a.window m fit,row_binding_sound a.preserveRow m fit,
    value_binding_sound a.preserveValue m fit⟩

theorem no_raw_cycle_at_either_binder441 {s q d} (a : Original s q d) :
    ¬PatternK2 s.core.current.ordinary a.arg.lower (inspectionPattern a.key a.rowBinder a.valueBinder) := by
  rintro ⟨site,visited,cycle⟩
  have e := two_bindings_visit_only_root441 visited
  cases e
  exact a.safe ⟨a.arg,by simp [a.asked],cycle⟩

end Yulang.GeneralDeclarativeI65.I72.RefPositions441
