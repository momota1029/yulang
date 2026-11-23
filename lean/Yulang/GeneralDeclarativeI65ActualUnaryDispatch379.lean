import Yulang.GeneralDeclarativeI65NativePrefix369
import Yulang.GeneralDeclarativeI65OrdinaryCrossingRoot378
import Yulang.GeneralDeclarativeWitnessNativeNestedMatch361

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessNativeKinds361 (Ctor readCtor)
open GeneralDeclarativeWitnessNativeNestedMatch361 (read)
open GeneralDeclarativeWitnessNativeValue360 (Code)
open GeneralDeclarativeWitnessNominalSource359 (Route SlotRead)
open GeneralDeclarativeWitnessNativeOrder362 (node)
open GeneralDeclarationPatterns (Pattern normalize)

/-- Replays exactly the head of the unary clause of the already defined
native read, leaving its recursive result entirely open. The read of
the authored constructor precedes the child read, not vice versa. -/
structure UnaryDispatch (e : Environment) (source : Route) (code : Code) (pattern : Pattern) where
  key : Nat
  fromRoute : Route
  fromCode : Code
  fromPattern : Pattern
  parentRoute : source = .unary key fromRoute
  parentCode : code = .unary key fromCode
  parentPattern : pattern = .app key [fromPattern]
  ctor : Ctor e key 1
  modeRead : readCtor e key 1 = some ctor

def dispatchUnary (e : Environment) :
    (source : Route) → (code : Code) → (pattern : Pattern) →
      Option (UnaryDispatch e source code pattern)
  | .unary a route, .unary b payload, .app c [query] =>
    if sameCode : a = b then
      if samePattern : b = c then
        match actual : readCtor e a 1 with
        | none => none
        | some declared =>
          some ⟨a,route,payload,query,rfl,by rw [sameCode],by rw [sameCode,samePattern],declared,actual⟩
      else none
    else none
  | _,_,_ => none

theorem unary_dispatch_exact {e : Environment} {key : Nat} {route : Route} {code : Code}
    {pat : Pattern} {declared : Ctor e key 1} (mode : readCtor e key 1 = some declared) :
    ∃ step, dispatchUnary e (.unary key route) (.unary key code) (.app key [pat]) = some step ∧
      step.fromRoute = route ∧ step.fromCode = code ∧ step.fromPattern = pat := by
  simp [dispatchUnary]
  split
  · rename_i absent
    rw [mode] at absent
    cases absent
  · exact ⟨_,rfl,rfl,rfl,rfl⟩

/-- Exact boundary of the original executable unary branch. The
recorded head dispatch does not depend on success at the child. -/
theorem unary_dispatch_recursive_success_iff {e : Environment} {locals : SlotRead}
    {route : Route} {code : Code} {pat : Pattern}
    (step : UnaryDispatch e route code pat) :
    (read e locals route code pat).isSome =
      (read e locals step.fromRoute step.fromCode step.fromPattern).isSome := by
  rcases step with ⟨key,source,inner,query,eqRoute,eqCode,eqPat,ctor,checked⟩
  subst route
  subst code
  subst pat
  cases ran : read e locals source inner query <;> simp [GeneralDeclarativeWitnessNativeNestedMatch361.read,checked,ran]

theorem failed_child_does_not_erase_unary_dispatch {e : Environment} {locals : SlotRead}
    {route : Route} {code : Code} {pat : Pattern} {step : UnaryDispatch e route code pat}
    (entered : dispatchUnary e route code pat = some step)
    (rest : read e locals step.fromRoute step.fromCode step.fromPattern = none) :
    (dispatchUnary e route code pat).isSome = true ∧ read e locals route code pat = none := by
  refine ⟨by simp [entered],?_⟩
  have h := unary_dispatch_recursive_success_iff (locals := locals) step
  rw [rest] at h
  cases outer : read e locals route code pat with
  | none => rfl
  | some result => simp [outer] at h

theorem released_unary_dispatch_has_literal_child {s : State} {origin : Origin}
    (source : CurrentReleasedOrigin s origin) {route : Route} {pat : Pattern}
    (step : UnaryDispatch s.current.environment route source.exactWrite.code pat) :
    origin.endpoint = .nominal step.key [.inl (.point (node step.fromCode))] ∧
      pat = .app step.key [step.fromPattern] ∧
      origin.slot = source.exactWrite.address.target := by
  exact ⟨source.endpoint.trans (congrArg node step.parentCode),step.parentPattern,source.target⟩

/-- Attach the actual occurrence and exact source-written root
pattern to the physically opened unary node. This is a local dispatch,
not a claim that the global scheduler must elect this candidate. -/
theorem authored_prefix_and_unary_dispatch_agree {s : State} {q : Request}
    {decl : GeneralDeclarations.Declaration} {accept : Origin → Prop} {side : OriginalSide}
    (pre : NativeHeadPrefix s q decl accept side)
    (release : CurrentReleasedOrigin s pre.atBound.original) {route : Route}
    (entered : UnaryDispatch s.current.environment route release.exactWrite.code (normalize pre.pattern)) :
    pre.key = entered.key ∧
      pre.written[0]? = some entered.fromPattern ∧
      pre.arguments[0]? = some (.inl (.point (node entered.fromCode))) := by
  have exactPat := Pattern.app.inj (pre.actualPattern.symm.trans entered.parentPattern)
  have endpoint := (released_unary_dispatch_has_literal_child release entered).1
  have exactNode := CommonRecursiveNominalIntervals.Endpoint.nominal.inj (pre.actualEndpoint.symm.trans endpoint)
  exact ⟨exactPat.1,by rw [exactPat.2]; rfl,by rw [exactNode.2]; rfl⟩

theorem exact_c361_leaf_does_not_read_compound {e : Environment} {locals : SlotRead}
    {source : Route} {name : Nat} {pat : Pattern}
    (compound : ∀ b,pat ≠ .var b) :
    read e locals source (.leaf name) pat = none := by
  cases pat <;> first
  | exact False.elim (compound _ rfl)
  | cases source <;> rfl

/-- The old native reader does enter this literal child but stops at
the ordinary boundary. This is a coverage boundary, not a verdict.
The ordinary reader is separate and has a root visit once this
exact child query has an inspecting ordinary translation. -/
theorem entered_ordinary_child_needs_the_separate_graph {e : Environment} {locals : SlotRead}
    {route : Route} {code : Code} {pat : Pattern}
    (step : UnaryDispatch e route code pat)
    {logical : Nat} (literal : step.fromCode = .leaf logical)
    (compound : ∀ b,step.fromPattern ≠ .var b)
    {view : GeneralDeclarativeK2Graph321.View}
    {query : GeneralNominalCenteredHeadMatExpressions.Expr}
    (inspecting : GeneralDeclarativeInspect321.Inspects query) :
    read e locals route code pat = none ∧
      GeneralDeclarativeInspect321.Visit view logical query logical := by
  have stopped : read e locals step.fromRoute step.fromCode step.fromPattern = none := by
    rw [literal]
    exact exact_c361_leaf_does_not_read_compound compound
  have there := unary_dispatch_recursive_success_iff (locals := locals) step
  rw [stopped] at there
  refine ⟨?_,.here inspecting⟩
  cases ran : read e locals route code pat with
  | none => rfl
  | some _ => simp [ran] at there

end Yulang.GeneralDeclarativeI65
