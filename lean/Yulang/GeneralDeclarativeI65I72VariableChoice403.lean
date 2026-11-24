import Yulang.GeneralDeclarativeI65I72Obligations402

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (All₂ Dictionary Tree Result Summarizes)
open CommonRecursiveNominalIntervals (Endpoint Argument)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarations (Declaration Checked DeclarationChecked)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessConstructorModes357 (Use)
open GeneralDeclarativeWitnessModeCoverage357 (DeclarationCovered)
open GeneralDeclarativeEmissionForest322 (Placement)
open GeneralDeclarativeBounds319 (Bound)

/-- An independently authored head of an original input. No equations
from an unfinished output, model, registry candidate, or B6 result
make this source-known. The full input interval is preserved as given. -/
structure SourceArgument403 (s : State) (a : Capture) where
  lower : Origin
  present : lower ∈ s.core.origins
  route : OriginRoute s.core lower a.lower
  key : Nat
  arguments : List (Argument Nat)
  literal : lower.endpoint = .nominal key arguments
  authoredConstructor : Use s.core.current.environment key arguments.length
  bounds : GeneralDeclarativeDemand320.Bounds s.core.current.ordinary a

/-- Scope evidence consists of written syntax and independently
authored input facts, not a successful match or diagnostic tape.
A repeated binder or a structural subpattern is outside this proof,
not evidence that a declaration should be dropped. -/
structure VariableRow403 (q : Request) (d : Declaration) where
  binders : List Nat
  literal : d.head = binders.map Pattern.var
  distinct : binders.Nodup
  sameArity : binders.length = q.demand.arguments.length
  noWhere : d.requirements = []

structure VariableScope403 (s : State) (q : Request) where
  ready : ∀ a ∈ q.demand.arguments, SourceArgument403 s a
  checked : Checked (authoredRegistry s.core.current)
  covered : ∀ d ∈ visible s.core q, DeclarationCovered s.core.current.environment d
  allVisible : ∀ d ∈ visible s.core q, VariableRow403 q d

def emptyCapture403 : Capture := ⟨0,0,0⟩

def bindings403 (ns : List Nat) (as : List Capture) (n : Nat) : Capture :=
  ((ns.zip as).lookup n).getD emptyCapture403

/-- The original entire input triple is used, not a chosen assignment
or a lower endpoint substituted for the actual name. -/
theorem binding_at_original403 {ns : List Nat} {as : List Capture}
    (distinct : ns.Nodup) (lengths : ns.length = as.length)
    {i n : Nat} {a : Capture} (binder : ns[i]? = some n) (arg : as[i]? = some a) :
    bindings403 ns as n = a := by
  induction ns generalizing as i with
  | nil => simp at binder
  | cons k ns ih =>
    cases as with
    | nil => simp at lengths
    | cons b as =>
      cases i with
      | zero =>
        simp at binder arg
        subst n; subst a
        simp [bindings403]
      | succ i =>
        have nb : ns[i]? = some n := by simpa using binder
        have ab : as[i]? = some a := by simpa using arg
        have distinct' := List.nodup_cons.mp distinct
        have neq : n ≠ k := by
          intro same
          exact distinct'.1 (same ▸ List.mem_of_getElem? nb)
        simpa [bindings403,List.lookup,beq_eq_false_iff_ne.mpr neq] using
          (ih distinct'.2 (Nat.succ.inj lengths) nb ab)

private theorem all_variable_reads403 (s : State) (capture : Nat → Capture)
    (ns : List Nat) (as : List Capture) (lengths : ns.length = as.length)
    (ready : ∀ a ∈ as, GeneralDeclarativeDemand320.Bounds s.core.current.ordinary a)
    (aligns : ∀ (i n : Nat) (a : Capture), ns[i]? = some n → as[i]? = some a → capture n = a) :
    All₂ (DeepHead s.core capture) as (ns.map Pattern.var) := by
  induction ns generalizing as with
  | nil =>
    cases as with
    | nil => exact .nil
    | cons => simp at lengths
  | cons k ns ih =>
    cases as with
    | nil => simp at lengths
    | cons a as =>
      have same := aligns 0 k a rfl rfl
      refine .cons (.ordinary ⟨ready a List.mem_cons_self, .variable k, rfl,
        .direct (.structural (.capture ?_ ?_))⟩) ?_
      · rw [same]
        exact .refl _
      · rw [same]
        exact .refl _
      · apply ih _ (Nat.succ.inj lengths)
          (fun a mem => ready a (List.mem_cons_of_mem _ mem))
        intro i n a nAt aAt
        exact aligns (i+1) n a (by simpa using nAt) (by simpa using aAt)

def variableHead403 {s q d} (scope : VariableScope403 s q)
    (row : VariableRow403 q d) : SourceHead s.core q d :=
  .ordered (bindings403 row.binders q.demand.arguments) (by
    rw [row.literal]
    exact all_variable_reads403 s _ _ _ row.sameArity
      (fun a atArg => (scope.ready a atArg).bounds)
      (fun _ _ _ nAt aAt => binding_at_original403 row.distinct row.sameArity nAt aAt))

def variableCandidate403 {s q} (scope : VariableScope403 s q) {d : Declaration}
    (present : d ∈ visible s.core q) : AuthoredCandidate s.core q d :=
  ⟨present,scope.covered d present,
    (scope.checked.2 d ((visible_exact s.core q d).mp present).1).signature,
    variableHead403 scope (scope.allVisible d present)⟩

/-- Every call-site visible entry occurs in this scan, without
filters for outputs, IDs, or selected body readiness. -/
def variableTapeOn403 {s q} (scope : VariableScope403 s q) :
    (rows : List Declaration) →
    (∀ d ∈ rows, d ∈ visible s.core q) → CandidateTape s.core q rows
  | [], _ => .nil
  | d::ds, incl => .next (.matched (variableCandidate403 scope (incl d List.mem_cons_self)))
      (variableTapeOn403 scope ds (fun a mem => incl a (List.mem_cons_of_mem _ mem)))

abbrev variableTape403 {s q} (scope : VariableScope403 s q) :=
  variableTapeOn403 scope (visible s.core q) (fun _ here => here)

theorem variable_scan_all_positive403 {s q} (scope : VariableScope403 s q)
    (rows : List Declaration) (incl : ∀ d ∈ rows, d ∈ visible s.core q) :
    (variableTapeOn403 scope rows incl).live = rows ∧ (variableTapeOn403 scope rows incl).waits = false := by
  induction rows with
  | nil => exact ⟨rfl,rfl⟩
  | cons d rows ih =>
    obtain ⟨live,wait⟩ := ih (fun a mem => incl a (List.mem_cons_of_mem _ mem))
    exact ⟨congrArg (List.cons d) live,wait⟩

/-- The independent selection evidence is derived before inspecting
an associated type or constructing an Event. -/
theorem variable_single_selection403 {s q d} (scope : VariableScope403 s q)
    (rawSafe : ¬ RootCycle s q) (exactlyOne : visible s.core q = [d]) :
    TapedMatch s.core q (variableTape403 scope) d := by
  have scanned := variable_scan_all_positive403 scope (visible s.core q) (fun _ here => here)
  exact ⟨rawSafe,scanned.2,scanned.1.trans exactlyOne⟩

theorem variable_no_inspection403 {s q} (scope : VariableScope403 s q) {d : Declaration}
    (present : d ∈ visible s.core q) {i : Nat} {p : Pattern} (atHead : d.head[i]? = some p) :
    ∃ binder, p = Pattern.var binder ∧ ∀ (view : GeneralDeclarativeK2Graph321.View) (root site : Nat),
      ¬ GeneralDeclarativeInspect321.Visit view root (.variable binder) site := by
  have member := List.mem_of_getElem? atHead
  rw [(scope.allVisible d present).literal] at member
  obtain ⟨nr,_,rfl⟩ := List.mem_map.mp member
  exact ⟨nr,rfl,fun _ _ _ => GeneralDeclarativeInspect321.variable_has_no_visit⟩

end Yulang.GeneralDeclarativeI65.I72
