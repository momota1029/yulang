import Yulang.GeneralDeclarativeI65I74InvariantList410
import Yulang.GeneralDeclarativeI65I74ExactEscape410

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.NestedInvariant440
open GeneralDeclarativeI65
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeHead320 (Equation)
open CommonRecursiveNominalIntervals (Endpoint Bounds ContextWellFormed childContext effectiveParameter)
open CommonDeclaredNominalInspection (Parameter)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessConstructorModes357 (Use)
open GeneralDeclarativeWitnessSparseIntervals357 (names visited Legal)
open GeneralDeclarativeWitnessModeCoverage357 (DeclarationCovered)
open GeneralDeclarations (Declaration DeclarationChecked)
open Core.PresenceGeneration (TyTerm)
open PresenceNormalForm (Atom)
open GeneralDeclarativeGraphRows321 (observed structural shapeOf)
open GeneralDeclarativeInspect321 (Visit PatternK2)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralNominalCenteredHeadMatExpressions (Expr)

def inv : Parameter := ⟨.value,.invariant⟩

def namedShape (outer inner binder : Nat) : Pattern :=
  .app outer [.app inner [.var binder]]

def query (outer inner binder : Nat) : Expr :=
  .nominal outer [.nominal inner [.variable binder]]

def loTerm (n : Nat) : Endpoint Nat := .ordinary (.var n)

def nestedInner (inner low high : Nat) : Endpoint Nat :=
  .nominal inner [.inl (.interval (loTerm low) (loTerm high))]

def nestedEndpoint (outer inner low high : Nat) : Endpoint Nat :=
  .nominal outer [.inl (.point (nestedInner inner low high))]

def nestedArguments (_outer inner low high : Nat) :=
  [(.inl (.point (nestedInner inner low high)) : CommonRecursiveNominalIntervals.Argument Nat)]

def validInner (p : Parameter) : Prop :=
  p = inv ∨ p = ⟨.value,.covariant⟩ ∨ p = ⟨.value,.contravariant⟩

theorem inherited_value440 {p : Parameter} (mode : validInner p) :
    effectiveParameter true p = inv ∧ childContext true p = true := by
  rcases mode with h|h|h <;> cases h <;> exact ⟨rfl,rfl⟩

def rawNominal (root key kid : Nat) : Equation := ⟨root,.nominal key [.variable kid]⟩

theorem nested_raw_visit440 {s : GeneralDeclarativeHead320.State} {root outer inner binder site}
    (read : rawNominal root outer site ∈ s.equations) :
    Visit (structural s) root (query outer inner binder) site :=
  .nominal (i := 0) (GeneralDeclarativeGraphRows321.literal_head read rfl) rfl rfl (.here .nominal)

theorem visit_nested_scope440 {view : GeneralDeclarativeK2Graph321.View}
    {root outer inner binder site}
    (covered : ∀ children, view root (.nominal outer children) →
      ∀ child, children[0]? = some child → child = site)
    {atSite} (seen : Visit view root (query outer inner binder) atSite) :
    atSite = root ∨ atSite = site := by
  cases seen with
  | here => exact .inl rfl
  | nominal shape written child deeper =>
    have w := List.mem_singleton.mp (List.mem_of_getElem? written)
    cases w
    have i0 := (List.getElem?_eq_some_iff.mp written).1
    have eq := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i0)
    subst_vars
    have chosen := covered _ shape _ child
    have deep := GeneralDeclarativeInspect321.nominal_variable_visits_only_root deeper
    exact .inr (deep.trans chosen)

theorem nested_has_no_raw_pattern_K2440 {s : GeneralDeclarativeHead320.State}
    {root outer inner binder site}
    (covered : ∀ children, structural s root (.nominal outer children) →
      ∀ child, children[0]? = some child → child = site)
    (atRoot : ¬AliasCycle s (observed s) root)
    (inside : ¬AliasCycle s (observed s) site) :
    ¬PatternK2 s root (query outer inner binder) := by
  rintro ⟨_,visit,cycle⟩
  rcases visit_nested_scope440 covered visit with h|h <;> cases h
  · exact atRoot cycle
  · exact inside cycle

structure Original (s : I72.State) (q : Request) (d : Declaration) where
  only : visible s.core q = [d]
  checked : DeclarationChecked (authoredRegistry s.core.current).constructors
    (authoredRegistry s.core.current).roles d
  covered : DeclarationCovered s.core.current.environment d
  arg : Capture
  asked : q.demand.arguments = [arg]
  noWhere : d.requirements = []
  noOutputs : q.demand.outputs = []
  outer : Nat
  inner : Nat
  binder : Nat
  written : d.head = [namedShape outer inner binder]
  root : Origin
  source : root ∈ s.core.origins
  issuer : root.issuer = q.occurrence
  rootLower : root.slot = arg.lower
  rootCenter : root.slot = arg.center
  rootUpper : root.slot = arg.upper
  site : Nat
  low : Nat
  center : Nat
  high : Nat
  endpoint : root.endpoint = nestedEndpoint outer inner low high
  rawOuter : rawNominal arg.lower outer site ∈ s.core.current.ordinary.equations
  rawInner : rawNominal site inner center ∈ s.core.current.ordinary.equations
  innerSource : Origin
  innerAuthored : innerSource ∈ s.core.origins
  innerIssuer : innerSource.issuer = q.occurrence
  innerSlot : innerSource.slot = site
  innerEndpoint : innerSource.endpoint = nestedInner inner low high
  physicalBounds : GeneralDeclarativeDemand320.Bounds s.core.current.ordinary ⟨low,center,high⟩
  outerUse : Use s.core.current.environment outer 1
  outerMode : names outerUse.mode 1 = some [inv]
  outerTable : s.core.modes[outer]? = some [inv]
  innerUse : Use s.core.current.environment inner 1
  innerParam : Parameter
  innerMode : names innerUse.mode 1 = some [innerParam]
  innerTable : s.core.modes[inner]? = some [innerParam]
  inherited : validInner innerParam
  lowAtom : Atom.tyLe (.var low) (.var low) ∈ s.core.current.ordinary.normal.ordinary
  highAtom : Atom.tyLe (.var high) (.var high) ∈ s.core.current.ordinary.normal.ordinary
  crossAtom : Atom.tyLe (.var low) (.var high) ∈ s.core.current.ordinary.normal.ordinary
  rootSafe : ¬RootCycle s q
  visitedSafe : ¬PatternK2 s.core.current.ordinary arg.lower (query outer inner binder)

def Original.capture {s q d} (a : Original s q d) (n : Nat) : Capture :=
  if n = a.binder then ⟨a.low,a.center,a.high⟩ else emptyCapture403

theorem Original.captureBounds {s q d} (a : Original s q d) :
    GeneralDeclarativeDemand320.Bounds s.core.current.ordinary (a.capture a.binder) := by
  simpa [Original.capture] using a.physicalBounds

theorem Original.bind {s q d} (a : Original s q d) :
    ValueBind s.core (a.capture a.binder) (.var a.low) (.var a.high) := by
  change ValueBind s.core (if a.binder = a.binder then ⟨a.low,a.center,a.high⟩ else emptyCapture403) _ _
  rw [ite_eq_left rfl]
  exact ⟨a.lowAtom,a.lowAtom,a.highAtom,a.highAtom⟩

theorem Original.innerWF {s q d} (a : Original s q d) :
    ContextWellFormed s.core.modes true (nestedInner a.inner a.low a.high) := by
  have inherit := inherited_value440 a.inherited
  refine .nominal a.innerTable (.cons ?_ (.nil true))
  rw [inherit.1,inherit.2]
  exact .valueInterval (.ordinary true _) (.ordinary true _)

theorem Original.endpointWF {s q d} (a : Original s q d) :
    ContextWellFormed s.core.modes false (nestedEndpoint a.outer a.inner a.low a.high) :=
  .nominal a.outerTable (.cons (.valuePoint a.innerWF) (.nil false))

def Original.innerCompare {s q d} (a : Original s q d) :
    Compare s.core.current.ordinary s.core.modes true
      (nestedInner a.inner a.low a.high) (nestedInner a.inner a.low a.high) := by
  have inherit := inherited_value440 a.inherited
  refine .nominal a.innerTable (.cons ?_ .nil)
  rw [inherit.1,inherit.2]
  exact .invariantValue (.ordinary a.crossAtom) (.ordinary a.crossAtom)
    (.ordinary a.crossAtom) (.ordinary a.crossAtom)

def Original.compare {s q d} (a : Original s q d) :
    DeclaredComparison s.core.current.environment s.core.current.ordinary s.core.modes false
      (nestedEndpoint a.outer a.inner a.low a.high) (nestedEndpoint a.outer a.inner a.low a.high) where
  actualSource := by
    intro site seen
    simp [nestedEndpoint,nestedInner,loTerm,visited.eq_def,
      GeneralDeclarativeWitnessSparseIntervals357.visitedList.eq_def] at seen
    have every : site = (a.outer,1) ∨ site = (a.inner,1) := by
      simpa [or_assoc,or_left_comm,or_comm] using seen
    rcases every with atOuter|atInner <;> subst site
    · exact ⟨a.outerUse,[inv],a.outerMode,a.outerTable⟩
    · exact ⟨a.innerUse,[a.innerParam],a.innerMode,a.innerTable⟩
  left := a.endpointWF
  right := a.endpointWF
  compared := .nominal a.outerTable (.cons (.invariantValue
    a.innerCompare a.innerCompare a.innerCompare a.innerCompare) .nil)

def Original.window {s q d} (a : Original s q d) :
    ModeWindow s.core a.arg (namedShape a.outer a.inner a.binder) :=
  ⟨a.root,a.root,a.rootLower ▸ .direct,a.rootUpper ▸ .direct,a.source,a.source,
    a.outer,[.app a.inner [.var a.binder]],rfl,_,_,a.endpoint,a.endpoint,
    by rw [a.endpoint]; exact a.compare⟩

abbrev Original.binding {s q d} (a : Original s q d) : Binding :=
  .value a.binder (.var a.low) (.var a.high)

def Original.deepInner {s q d} (a : Original s q d) :
    DeepRead s.core a.capture true (.app a.inner [.var a.binder])
      (nestedInner a.inner a.low a.high) (nestedInner a.inner a.low a.high) [a.binding,a.binding] := by
  have inherit := inherited_value440 a.inherited
  let interval : Bounds (Endpoint Nat) := .interval (loTerm a.low) (loTerm a.high)
  have both : DeepArgument s.core a.capture (childContext true a.innerParam)
      (effectiveParameter true a.innerParam) (.var a.binder) (.inl interval) (.inl interval)
      ([a.binding] ++ [a.binding]) := by
    rw [inherit.1,inherit.2]
    exact .invariantValue (.bind a.bind) (.bind a.bind)
  exact .nominal a.innerUse a.innerMode a.innerTable (.cons both .nil)

def Original.head {s q d} (a : Original s q d) : SourceHead s.core q d := by
  refine .ordered a.capture ?_
  rw [a.asked,a.written]
  let pair := [a.binding,a.binding]
  refine .cons (.declared (found := pair ++ pair) a.window ?_) .nil
  change DeepRead s.core a.capture false (namedShape a.outer a.inner a.binder)
    a.root.endpoint a.root.endpoint (pair ++ pair)
  rw [a.endpoint]
  let point : Bounds (Endpoint Nat) := .point (nestedInner a.inner a.low a.high)
  have both : DeepArgument s.core a.capture true inv (.app a.inner [.var a.binder])
      (.inl point) (.inl point) (pair ++ pair) := .invariantValue a.deepInner a.deepInner
  have parts : DeepArguments s.core a.capture false [inv] [.app a.inner [.var a.binder]]
      [.inl point] [.inl point] ((pair ++ pair) ++ []) := .cons both .nil
  exact .nominal a.outerUse a.outerMode a.outerTable parts

theorem nested_captures_mean_in_same_model440 {s q d} (a : Original s q d)
    (m : I72.Model) (fit : I72.Fits s m) :
    WindowMeaning a.window m ∧
    Binding.Denotes a.capture m a.binding ∧
    GeneralDeclarativeWhere319.InInterval (m.assignment a.low).1
      (m.assignment a.high).1 (m.assignment a.center).1 := by
  refine ⟨mode_window_sound a.window m fit,value_binding_sound a.bind m fit,?_⟩
  exact GeneralDeclarativeDemand320.bounds_sound a.physicalBounds m.assignment fit.1.1

end Yulang.GeneralDeclarativeI65.I72.NestedInvariant440
