import Yulang.GeneralDeclarativeI65I74NestedInvariantSource440
import Yulang.GeneralDeclarativeI65I74MergedOutputHeader439

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace Yulang.GeneralDeclarativeI65.I72.NestedInvariant440
open GeneralDeclarativeI65
open Checker408 (Problem)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeHead320 (Equation)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeGraphRows321 (observed structural shapeOf)
open GeneralDeclarativeK2Graph321 (Shape)
open GeneralDeclarativeInspect321 (Visit PatternK2)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeWitnessSparseIntervals357 (names)
open GeneralDeclarativeWitnessConstructorModes357 (readUse)
open GeneralDeclarativeWitnessProblem349 (splitAnd)
open GeneralDeclarativeWhere319 (Capture)
open CommonRecursiveNominalIntervals (Endpoint Bounds)
open CommonDeclaredNominalInspection (Parameter)
open Core.PresenceGeneration (TyTerm)
open PresenceNormalForm (Atom)
open List410 (ExactEscapeWire checkExactEscape exact_escape_preserves_alias_side410
  exact_escape_refutes_raw_root_K2410)

def coversEveryRawOuter (w : ExactEscapeWire) (outer site : Nat) (row : Equation) : Bool :=
  match shapeOf row.right with
  | some (.nominal tag children) =>
    if w.side row.left = 0 ∧ tag = outer then
      match children[0]? with
      | none => true
      | some n => decide (n = site)
    else true
  | _ => true

theorem raw_cover_reflects_every_actual_visit440 {s : GeneralDeclarativeHead320.State}
    {root outer site w}
    (esc : checkExactEscape s root w = true)
    (covered : s.equations.all (coversEveryRawOuter w outer site) = true) :
    ∀ children, structural s root (.nominal outer children) →
      ∀ child, children[0]? = some child → child = site := by
  intro children seen kid fromSlot
  obtain ⟨source,alias,e,present,same⟩ := seen
  have rootZero := of_decide_eq_true (splitAnd (splitAnd esc).1).2
  have sourceZero := (exact_escape_preserves_alias_side410 esc alias).symm.trans rootZero
  have checked := List.all_eq_true.mp covered (⟨source,e⟩ : Equation) present
  simpa [coversEveryRawOuter,same,sourceZero,fromSlot] using checked

def isUsedInner (p : Parameter) : Bool :=
  decide (p = inv) || (decide (p = ⟨.value,.covariant⟩) || decide (p = ⟨.value,.contravariant⟩))

theorem isUsedInner_exact {p : Parameter} (ok : isUsedInner p = true) : validInner p := by
  simpa [isUsedInner,validInner] using ok

def rawBounds (s : GeneralDeclarativeHead320.State) (b : Capture) : Bool :=
  decide ((Atom.tyLe (.var b.lower) (.var b.center) : Atom Nat) ∈ s.normal.ordinary) &&
  decide ((Atom.tyLe (.var b.center) (.var b.upper) : Atom Nat) ∈ s.normal.ordinary)

theorem rawBounds_exact {s : GeneralDeclarativeHead320.State} {b : Capture}
    (ok : rawBounds s b = true) : GeneralDeclarativeDemand320.Bounds s b :=
  ⟨.constraint (of_decide_eq_true (splitAnd ok).1),
    .constraint (of_decide_eq_true (splitAnd ok).2)⟩

/-- Locations in the original source/state and two finite graph witnesses.
The declaration keys, the capture endpoints and actual center, the
dictionary, diagnostic, and typed comparison are not witness fields. -/
structure Wire where
  rootOrigin : Nat
  innerOrigin : Nat
  outerRow : Nat
  innerRow : Nat
  rootEscape : ExactEscapeWire
  innerEscape : ExactEscapeWire

def replay440 (p : Problem) (d : Declaration)
    (scope : visible p.state.core p.root = [d]) (w : Wire) :
    Option (Original p.state p.root d) := do
  let core := p.state.core
  let env := core.current.environment
  let ord := core.current.ordinary
  if header : MergedOutput439.checkHeader439 env = true then
    if boundary : (d.requirements.isEmpty && p.root.demand.outputs.isEmpty) = true then
      match written : d.head, asked : p.root.demand.arguments with
      | [.app outer [.app inner [.var binder]]],[arg] =>
        if rootClear : checkExactEscape ord arg.lower w.rootEscape = true then
          match rootAt : core.origins[w.rootOrigin]?, innerAt : core.origins[w.innerOrigin]? with
          | some root, some innerSource =>
            let site := innerSource.slot
            if clear : checkExactEscape ord site w.innerEscape = true then
              if all : ord.equations.all (coversEveryRawOuter w.rootEscape outer site) = true then
                match outerAt : ord.equations[w.outerRow]?, innerAtEq : ord.equations[w.innerRow]? with
                | some oa,some ia =>
                  match parsed : root.endpoint, decoded : ia.right, outerDecoded : oa.right,
                    innerParsed : innerSource.endpoint with
                  | .nominal ro [.inl (.point (.nominal ri
                      [.inl (.interval (.ordinary (.var low)) (.ordinary (.var high)))]))],
                    .nominal key [.variable center], .nominal ok [.variable actualSite],
                    .nominal ik [.inl (.interval (.ordinary (.var ilow)) (.ordinary (.var ihigh)))] =>
                    if nat : ro = outer ∧ ri = inner ∧ key = inner ∧ ia.left = site ∧
                        oa.left = arg.lower ∧ ok = outer ∧ actualSite = site then
                      if author : root.issuer = p.root.occurrence ∧
                          innerSource.issuer = p.root.occurrence ∧ root.slot = arg.lower ∧
                          root.slot = arg.center ∧ root.slot = arg.upper ∧
                          ik = inner ∧ ilow = low ∧ ihigh = high then
                        if bounds : rawBounds ord ⟨low,center,high⟩ = true then
                          let ous ← readUse env outer 1
                          let ius ← readUse env inner 1
                          if om : names ous.mode 1 = some [inv] ∧ core.modes[outer]? = some [inv] then
                            match mode : names ius.mode 1 with
                            | some [param] =>
                              if innerOK : isUsedInner param && decide (core.modes[inner]? = some [param]) then
                                if atoms : decide ((Atom.tyLe (.var low) (.var low) : Atom Nat) ∈ ord.normal.ordinary) &&
                                    decide ((Atom.tyLe (.var high) (.var high) : Atom Nat) ∈ ord.normal.ordinary) &&
                                    decide ((Atom.tyLe (.var low) (.var high) : Atom Nat) ∈ ord.normal.ordinary) then
                                  let proof := MergedOutput439.checked_header439 header
                                  let authoredDecl := ((visible_exact core p.root d).mp
                                    (by rw [scope]; exact List.mem_cons_self)).1
                                  let rootSafe : ¬RootCycle p.state p.root := by
                                    rintro ⟨a,member,cyclic⟩
                                    rw [asked] at member
                                    cases List.mem_singleton.mp member
                                    exact exact_escape_refutes_raw_root_K2410 rootClear cyclic
                                  let safe := nested_has_no_raw_pattern_K2440 (binder := binder)
                                    (raw_cover_reflects_every_actual_visit440 rootClear all)
                                    (exact_escape_refutes_raw_root_K2410 rootClear)
                                    (exact_escape_refutes_raw_root_K2410 clear)
                                  let a : Original p.state p.root d :=
                                    { only := scope
                                      checked := proof.1.2 d authoredDecl
                                      covered := proof.2.1 d authoredDecl
                                      arg := arg
                                      asked := asked
                                      noWhere := List.isEmpty_iff.mp (splitAnd boundary).1
                                      noOutputs := List.isEmpty_iff.mp (splitAnd boundary).2
                                      outer := outer
                                      inner := inner
                                      binder := binder
                                      written := written
                                      root := root
                                      source := List.mem_of_getElem? rootAt
                                      issuer := author.1
                                      rootLower := author.2.2.1
                                      rootCenter := author.2.2.2.1
                                      rootUpper := author.2.2.2.2.1
                                      site := site
                                      low := low
                                      center := center
                                      high := high
                                      endpoint := by rw [parsed,nat.1,nat.2.1]; rfl
                                      rawOuter := by
                                        have rhs : oa.right = .nominal outer [.variable site] := by
                                          rw [outerDecoded,nat.2.2.2.2.2.1,nat.2.2.2.2.2.2]
                                        have shape : oa = rawNominal arg.lower outer site := by
                                          obtain ⟨left,right⟩ := oa
                                          have sameLeft : left = arg.lower := nat.2.2.2.2.1
                                          have sameRight : right = .nominal outer [.variable site] := rhs
                                          simp [rawNominal,sameLeft,sameRight]
                                        exact shape ▸ List.mem_of_getElem? outerAt
                                      rawInner := by
                                        have rhs : ia.right = .nominal inner [.variable center] := by rw [decoded,nat.2.2.1]
                                        have shape : ia = rawNominal site inner center := by
                                          obtain ⟨left,right⟩ := ia
                                          have sameLeft : left = site := nat.2.2.2.1
                                          have sameRight : right = .nominal inner [.variable center] := rhs
                                          simp [rawNominal,sameLeft,sameRight]
                                        exact shape ▸ List.mem_of_getElem? innerAtEq
                                      innerSource := innerSource
                                      innerAuthored := List.mem_of_getElem? innerAt
                                      innerIssuer := author.2.1
                                      innerSlot := rfl
                                      innerEndpoint := by
                                        rw [innerParsed,author.2.2.2.2.2.1,author.2.2.2.2.2.2.1,author.2.2.2.2.2.2.2]
                                        rfl
                                      physicalBounds := rawBounds_exact bounds
                                      outerUse := ous
                                      outerMode := om.1
                                      outerTable := om.2
                                      innerUse := ius
                                      innerParam := param
                                      innerMode := mode
                                      innerTable := of_decide_eq_true (splitAnd innerOK).2
                                      inherited := isUsedInner_exact (splitAnd innerOK).1
                                      lowAtom := of_decide_eq_true (splitAnd (splitAnd atoms).1).1
                                      highAtom := of_decide_eq_true (splitAnd (splitAnd atoms).1).2
                                      crossAtom := of_decide_eq_true (splitAnd atoms).2
                                      rootSafe := rootSafe
                                      visitedSafe := safe }
                                  some a
                                else none
                              else none
                            | _ => none
                          else none
                        else none
                      else none
                    else none
                  | _,_,_,_ => none
                | _,_ => none
              else none
            else none
          | _,_ => none
        else none
      | _,_ => none
    else none
  else none

end Yulang.GeneralDeclarativeI65.I72.NestedInvariant440
