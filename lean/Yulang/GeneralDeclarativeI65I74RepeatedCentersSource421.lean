import Yulang.GeneralDeclarativeI65I74RoleDefaultCoherence420

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RepeatedCenters421
open GeneralDeclarativeI65
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeWitnessLiteral349 (eqExpr eq_expr)
open Checker408 (Problem)
open List410 (ExactEscapeWire checkExactEscape exact_escape_refutes_raw_root_K2410)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeK2Alias321 (AliasCycle)

def variantRow (slot tag child : Nat) : Equation := ⟨slot,.variant tag (.variable child)⟩
def literalVariant (tag child : Nat) : CommonRecursiveNominalIntervals.Endpoint Nat :=
  .ordinary (.variant tag (.var child))

structure LowerRead (s : I72.State) (slot : Nat) where
  origin : Origin
  inSource : origin ∈ s.core.origins
  sourceSlot : origin.slot = slot
  tag : Nat
  child : Nat
  literal : origin.endpoint = literalVariant tag child
  exactRow : variantRow slot tag child ∈ s.core.current.ordinary.equations

structure LowerWire where
  origin : Nat
  ordinaryRow : Nat

def readLower (s : I72.State) (slot : Nat) (w : LowerWire) : Option (LowerRead s slot) := do
  match src : s.core.origins[w.origin]? with
  | none => none
  | some o =>
    match term : o.endpoint with
    | .ordinary (.variant tag (.var child)) =>
      match seen : s.core.current.ordinary.equations[w.ordinaryRow]? with
      | none => none
      | some eq =>
        if exact : o.slot = slot ∧ eq.left = slot ∧
            eqExpr eq.right (.variant tag (.variable child)) = true then
          have same : eq = variantRow slot tag child := by
            cases eq
            congr
            · exact exact.2.1
            · exact (eq_expr _ _).mp exact.2.2
          some ⟨o,List.mem_of_getElem? src,exact.1,tag,child,term,same ▸ List.mem_of_getElem? seen⟩
        else none
    | _ => none

/-- Two original ranges with a shared upper endpoint. This election
contains no model, fixed-target relation, or retained center equality. -/
structure Choice (p : Problem) where
  first : Capture
  second : Capture
  originalArgs : p.root.demand.arguments = [first,second]
  commonUpper : first.upper = second.upper
  firstRange : Bounds p.state.core.current.ordinary first
  secondRange : Bounds p.state.core.current.ordinary second
  firstNonpoint : first.lower ≠ first.upper
  secondNonpoint : second.lower ≠ second.upper
  firstNotLower : first.center ≠ first.lower
  secondNotLower : second.center ≠ second.lower
  lowerFirst : LowerRead p.state first.lower
  lowerSecond : LowerRead p.state second.lower
  sameTag : lowerFirst.tag = lowerSecond.tag
  decl : Declaration
  ordinal : Nat
  authored : (authoredRegistry p.state.core.current).declarations[ordinal]? = some decl
  only : visible p.state.core p.root = [decl]
  role : ∃ r ∈ p.state.core.current.environment.source.roles.rows, r.role = p.root.demand.role
  checked : GeneralDeclarations.Checked (authoredRegistry p.state.core.current)
  binder : Nat
  literal : decl.head = [.var binder,.var binder]
  noWhere : decl.requirements = []
  noOutputs : p.root.demand.outputs = []
  rawSafe : ¬ RootCycle p.state p.root

def checkRange (s : I72.State) (a : Capture) : Prop :=
  (a.lower,a.center) ∈ s.core.current.ordinary.normal.intervals ∧
    (a.center,a.upper) ∈ s.core.current.ordinary.normal.intervals

instance (s : I72.State) (a : Capture) : Decidable (checkRange s a) := inferInstanceAs (Decidable (_ ∧ _))

theorem exact_range_bounds421 {s a} (h : checkRange s a) : Bounds s.core.current.ordinary a :=
  ⟨.interval h.1,.interval h.2⟩

theorem no_raw_cycle_on_either_original_root421 {p : Problem} {a b : Capture}
    (args : p.root.demand.arguments = [a,b])
    (A : ¬ AliasCycle p.state.core.current.ordinary (observed p.state.core.current.ordinary) a.lower)
    (B : ¬ AliasCycle p.state.core.current.ordinary (observed p.state.core.current.ordinary) b.lower) :
    ¬ RootCycle p.state p.root := by
  rintro ⟨c,member,loop⟩
  rw [args] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h|h
  · exact A (h ▸ loop)
  · exact B (h ▸ loop)

structure ChoiceWire where
  firstLower : LowerWire
  secondLower : LowerWire
  ordinal : Nat
  firstEscape : ExactEscapeWire
  secondEscape : ExactEscapeWire

/-- Only ordinary input-evidence, the actual visible declaration and raw
root checks are read here. Center value row locators do not exist in
ChoiceWire and a missing equality never delays this election. -/
def readChoice421 (p : Problem) (w : ChoiceWire) : Option (Choice p) := do
  let env := p.state.core.current.environment
  match args : p.root.demand.arguments with
  | [a,b] =>
    if ranges : checkRange p.state a ∧ checkRange p.state b ∧ a.upper = b.upper ∧
        a.lower ≠ a.upper ∧ b.lower ≠ b.upper ∧ a.center ≠ a.lower ∧ b.center ≠ b.lower then
      let l ← readLower p.state a.lower w.firstLower
      let r ← readLower p.state b.lower w.secondLower
      if tags : l.tag = r.tag then
        if safe : (checkExactEscape p.state.core.current.ordinary a.lower w.firstEscape &&
            checkExactEscape p.state.core.current.ordinary b.lower w.secondEscape) = true then
          if header : RoleDefault420.checkHeader env = true then
            let valid := RoleDefault420.checked_default_header420 header
            match seen : visible p.state.core p.root with
            | [d] =>
              if pos : (authoredRegistry p.state.core.current).declarations[w.ordinal]? = some d then
                match real : GeneralSourceMetadataFiniteLookup291.get p.root.demand.role
                    (GeneralSourceMetadataRoles291.index env.source.roles) with
                | none => none
                | some role =>
                  have source := GeneralSourceMetadataRoles291.indexed real
                  match written : d.head with
                  | [.var n,.var k] =>
                    if isShape : n = k ∧ d.requirements = [] ∧ p.root.demand.outputs = [] then
                      have raw := GeneralDeclarativeWitnessProblem349.splitAnd safe
                      pure ⟨a,b,args,ranges.2.2.1,exact_range_bounds421 ranges.1,
                        exact_range_bounds421 ranges.2.1,ranges.2.2.2.1,ranges.2.2.2.2.1,
                        ranges.2.2.2.2.2.1,ranges.2.2.2.2.2.2,l,r,tags,d,w.ordinal,pos,seen,
                        ⟨role,source.1,source.2⟩,valid.1,n,by simpa [isShape.1] using written,
                        isShape.2.1,isShape.2.2,no_raw_cycle_on_either_original_root421 args
                          (exact_escape_refutes_raw_root_K2410 raw.1)
                          (exact_escape_refutes_raw_root_K2410 raw.2)⟩
                    else none
                  | _ => none
              else none
            | _ => none
          else none
        else none
      else none
    else none
  | _ => none

def Choice.tie {p} (a : Choice p) : Equation := ⟨a.second.center,.variable a.first.center⟩

def Choice.row {p} (a : Choice p) : RepeatedRow403 p.root a.decl :=
  ⟨[a.binder,a.binder],a.literal,by simp [a.originalArgs]⟩

theorem actual_distinct_centers_generate_only_one_ordered_tie421 {p}
    (a : Choice p) (apart : a.second.center ≠ a.first.center) :
    selectedCenterRows403 p.root a.row = [a.tie] := by
  simp [selectedCenterRows403,selectedInputSpans403,selectedInput403,Choice.row,
    a.originalArgs,bindings403,centerTie403,Choice.tie,apart]

end Yulang.GeneralDeclarativeI65.I72.RepeatedCenters421
