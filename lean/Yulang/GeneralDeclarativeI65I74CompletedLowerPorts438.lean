import Yulang.GeneralDeclarativeI65I74CompletedLowerSeed437
import Yulang.GeneralDeclarativeI65I74CompletedLowerCenter437
import Yulang.GeneralDeclarativeI65I74CompletedLowerNativeHeader437
import Yulang.GeneralDeclarativeI65I74ExactEscape410

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.CompletedEntry438
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration Checked DeclarationChecked)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry point)
open GeneralDeclarativeWitnessConstructorModes357 (Use readUse)
open GeneralDeclarativeWitnessSparseIntervals357 (Legal names visited visitedList)
open GeneralDeclarativeWitnessModeCoverage357 (DeclarationCovered)
open CommonRecursiveNominalIntervals (ContextWellFormed)
open PresenceNormalForm (Atom)
open List410 (ExactEscapeWire checkExactEscape exact_escape_refutes_raw_root_K2410)

structure ReadSingleton438 (s : I72.State) (q : Request) where
  row : Declaration
  arg : Capture
  args : q.demand.arguments = [arg]
  key : Nat
  binder : Nat
  head : row.head = [authoredUnaryPattern405 key binder]
  visibleOnly : visible s.core q = [row]
  bookIndex : Nat
  ordinal : unfilterOrdinal395 (fun d : Declaration => d.role == q.demand.role)
    (authoredRegistry s.core.current).declarations 0 = some bookIndex
  book : (authoredRegistry s.core.current).declarations[bookIndex]? = some row
  checked : Checked (authoredRegistry s.core.current)
  covered : DeclarationCovered s.core.current.environment row
  use : Use s.core.current.environment key 1
  mode : use.mode = .declared [coValue404]
  table : s.core.modes[key]? = some [coValue404]

def readSingleton438 (s : I72.State) (q : Request) : Option (ReadSingleton438 s q) := do
  let env := s.core.current.environment
  let registry := authoredRegistry s.core.current
  if header : CompletedNativeHeader437.checkHeader env = true then
    let checked := CompletedNativeHeader437.checkedHeader (s := s.core.current) header
    match args : q.demand.arguments, candidates : visible s.core q with
    | [arg], [row] =>
      match head : row.head with
      | [.app key [.var binder]] =>
        match ordinal : unfilterOrdinal395 (fun d : Declaration => d.role == q.demand.role)
            registry.declarations 0 with
        | none => none
        | some j =>
          if book : registry.declarations[j]? = some row then
            let use ← readUse env key 1
            match mode : use.mode with
            | .declared [⟨.value,.covariant⟩] =>
              if table : s.core.modes[key]? = some [coValue404] then
                let covered := checked.2.1 row (List.mem_of_getElem? book)
                return ⟨row,arg,args,key,binder,head,candidates,j,ordinal,book,checked.1,covered,use,mode,table⟩
              else none
            | _ => none
          else none
      | _ => none
    | _,_ => none
  else none

theorem ReadSingleton438.rootSafe {s q} (leaf : ReadSingleton438 s q)
    (w : ExactEscapeWire) (guard : checkExactEscape s.core.current.ordinary leaf.arg.lower w = true) :
    ¬RootCycle s q := by
  rintro ⟨a,seen,bad⟩
  rw [leaf.args] at seen
  obtain rfl := List.mem_singleton.mp seen
  exact exact_escape_refutes_raw_root_K2410 guard bad

private def captureKey (a : Capture) : Nat × Nat × Nat := (a.lower,a.center,a.upper)
private theorem capture_eq (a b : Capture) : captureKey a = captureKey b ↔ a = b := by
  cases a
  cases b
  simp [captureKey]

local instance : DecidableEq Capture :=
  fun a b => decidable_of_iff (captureKey a = captureKey b) (capture_eq a b)

private def reflectPointComparison {s q} (leaf : ReadSingleton438 s q) (pa : Nat)
    (comparison : Atom.tyLe (.var pa) (.var pa) ∈ s.core.current.ordinary.normal.ordinary) :
    DeclaredComparison s.core.current.environment s.core.current.ordinary s.core.modes false
      (unaryNominalPoint404 leaf.key pa) (unaryNominalPoint404 leaf.key pa) := by
  have authority : Legal s.core.current.environment s.core.modes (leaf.key,1) := by
    refine ⟨leaf.use,[coValue404],?_,leaf.table⟩
    change names leaf.use.mode 1 = some [coValue404]
    rw [leaf.mode]
    rfl
  have wf : ContextWellFormed s.core.modes false (unaryNominalPoint404 leaf.key pa) :=
    .nominal leaf.table (.cons (.valuePoint (.ordinary false (.var pa))) (.nil false))
  refine ⟨?_,wf,wf,.nominal leaf.table (.cons (.covariantValue (.ordinary comparison)) .nil)⟩
  intro site visitedAt
  have same : site = (leaf.key,1) := by
    simpa [unaryNominalPoint404,visited,visitedList] using visitedAt
  exact same ▸ authority

private def pointChoice {s q} (leaf : ReadSingleton438 s q)
    (o : Origin) (atOrigin : o ∈ s.core.origins)
    (atInput : leaf.arg = point o.slot) (pa : Nat)
    (source : o.endpoint = unaryNominalPoint404 leaf.key pa)
    (comparison : Atom.tyLe (.var pa) (.var pa) ∈ s.core.current.ordinary.normal.ordinary) :
    AuthoredUnaryChoice405 s q leaf.row := by
  have route : OriginRoute s.core o leaf.arg.lower := atInput.symm ▸ (OriginRoute.direct : OriginRoute s.core o o.slot)
  have upper : OriginRoute s.core o leaf.arg.upper := atInput.symm ▸ (OriginRoute.direct : OriginRoute s.core o o.slot)
  have sameComparison := reflectPointComparison leaf pa comparison
  let win : ModeWindow s.core leaf.arg (authoredUnaryPattern405 leaf.key leaf.binder) :=
    ⟨o,o,route,upper,atOrigin,atOrigin,leaf.key,[.var leaf.binder],rfl,_,_,source,source,
      source.symm ▸ sameComparison⟩
  exact ⟨leaf.key,leaf.binder,leaf.arg,leaf.args,leaf.head,leaf.visibleOnly,leaf.checked,leaf.covered,
    leaf.use,leaf.mode,leaf.table,win,pa,pa,source,source⟩

structure SeedSource438 {s q} (leaf : ReadSingleton438 s q) (originIndex : Nat) where
  basis : CompletedSeed437.SeedBasis s q leaf.row
  exactOrigin : s.core.origins[originIndex]? = some basis.capture.actual
  exactIssuer : basis.capture.actual.issuer = q.occurrence

def readSeedBasis438 {s q} (leaf : ReadSingleton438 s q)
    (sourceAt : Nat) (escape : ExactEscapeWire) : Option (SeedSource438 leaf sourceAt) := do
  if safe : checkExactEscape s.core.current.ordinary leaf.arg.lower escape = true then
    if noWhere : leaf.row.requirements = [] then
      match found : s.core.origins[sourceAt]? with
      | none => none
      | some o =>
        if atInput : leaf.arg = point o.slot then
          if issuer : o.issuer = q.occurrence then
            match payload : literalUnaryPayloadName406 leaf.key o.endpoint with
            | none => none
            | some pa =>
              if comparison : Atom.tyLe (.var pa) (.var pa) ∈ s.core.current.ordinary.normal.ordinary then
                let source := unary_payload_name_read_exact406.mp payload
                let atOrigin := List.mem_of_getElem? found
                let choice := pointChoice leaf o atOrigin atInput pa source comparison
                have route : OriginRoute s.core o leaf.arg.center :=
                  atInput.symm ▸ (OriginRoute.direct : OriginRoute s.core o o.slot)
                let actual : UnaryActualPayload405 choice :=
                  ⟨point pa,⟨comparison,comparison,comparison,comparison⟩,⟨.refl pa,.refl pa⟩,
                    o,atOrigin,route,source⟩
                let b : CompletedSeed437.SeedBasis s q leaf.row :=
                  ⟨choice,actual,leaf.rootSafe escape safe,leaf.bookIndex,leaf.ordinal,leaf.book,noWhere⟩
                return ⟨b,found,issuer⟩
              else none
          else none
        else none
    else none
  else none


structure TypedUnary438 {s slots c p} (key : Nat) (rhs : NamedMixedTree401 s slots c p) where
  lowerName : Nat
  exactTyped : TypedCovariantPoint404 key lowerName rhs

def readTypedUnary438 {s slots c p} (key : Nat) (rhs : NamedMixedTree401 s slots c p) :
    Option (TypedUnary438 key rhs) :=
  match rhs with
  | .declaredApp name use _ _ args =>
    if nameAt : name = key then
      match modeAt : use.mode with
      | .declared [⟨.value,.covariant⟩] =>
        match atName : singlePointName404 args with
        | none => none
        | some n => some ⟨n,nameAt,modeAt,atName⟩
      | _ => none
    else none
  | _ => none

structure ReadGate438 {s q} (leaf : ReadSingleton438 s q) (need : OutputNeed s)
    (upperIndex : Nat) where
  gate : CompletedUnaryGate406 s q leaf.row need
  exactUpper : s.core.origins[upperIndex]? = some gate.upper

def readGate438 {s q} (leaf : ReadSingleton438 s q) (need : OutputNeed s)
    (upperIndex : Nat) : Option (ReadGate438 leaf need upperIndex) := do
  if target : need.expected.original.target = leaf.arg.lower then
    let selected ← readTypedUnary438 leaf.key need.expected.rhs
    match found : s.core.origins[upperIndex]? with
    | none => none
    | some upper =>
      if route : routeMember s.core leaf.arg.upper upper = true then
        match literal : literalUnaryPayloadName406 leaf.key upper.endpoint with
        | none => none
        | some last =>
          if compare : Atom.tyLe (.var selected.lowerName) (.var last) ∈ s.core.current.ordinary.normal.ordinary then
            let gate : CompletedUnaryGate406 s q leaf.row need :=
              ⟨leaf.key,leaf.binder,leaf.arg,leaf.args,leaf.head,leaf.visibleOnly,leaf.checked,
                leaf.covered,selected.lowerName,target,selected.exactTyped,upper,List.mem_of_getElem? found,
                actual_route_iff.mp route, last,unary_payload_name_read_exact406.mp literal,compare⟩
            return ⟨gate,found⟩
          else none
      else none
  else none

theorem checked_gate_cannot_use_wrong_target438 {s q} {leaf : ReadSingleton438 s q}
    {need : OutputNeed s} {upperIndex} (r : ReadGate438 leaf need upperIndex) :
    need.expected.original.target = r.gate.arg.lower :=
  r.gate.lowerTarget

theorem checked_gate_uses_independent_authored_upper438 {s q} {leaf : ReadSingleton438 s q}
    {need : OutputNeed s} {upperIndex} (r : ReadGate438 leaf need upperIndex) :
    s.core.origins[upperIndex]? = some r.gate.upper ∧
    OriginRoute s.core r.gate.upper r.gate.arg.upper ∧
    r.gate.upper.endpoint = unaryNominalPoint404 r.gate.key r.gate.upperPayload :=
  ⟨r.exactUpper,r.gate.upperRoute,r.gate.upperLiteral⟩

end Yulang.GeneralDeclarativeI65.I72.CompletedEntry438
