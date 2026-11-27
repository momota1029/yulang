import Yulang.GeneralDeclarativeI65I74ActualHeaderProtocol461

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.EligibleFieldStart461
open Yulang.GeneralDeclarativeI65
open GeneralDeclarations (Declaration Clause)
open GeneralDeclarationPatterns (Smaller StableSmaller checkSmaller checkSmaller_exact)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessClassifyVariance357 (DeclarationReady)
open GeneralDeclarativeWitnessModeCoverage357 (DeclarationCovered)
open GeneralSourceMetadataRoles291 (Valid)
open Checker408 (Problem)
open RecordTrail455 (localAuthorBits local_author_bits_exact455)
open WrittenPattern460

def CurrentAddressShape (p : Problem) (a : OriginalAnchor p) : Prop :=
  (visible p.state.core p.root).length = 1 ∧
  a.declaration.head.length = 1 ∧ a.declaration.requirements.length = 1 ∧
  p.root.demand.arguments.length = 1 ∧
  a.capture.lower = a.capture.center ∧ a.capture.center = a.capture.upper

instance {p : Problem} {a : OriginalAnchor p} : Decidable (CurrentAddressShape p a) := by
  unfold CurrentAddressShape
  infer_instance

def checkStartShell (p : Problem) (a : OriginalAnchor p) : Bool :=
  ((decide (CurrentAddressShape p a) && p.root.demand.outputs.isEmpty) && a.clause.outputs.isEmpty) &&
  (((Checker408.originalRole p).isSome &&
      GeneralSourceMetadataRoles291.check p.state.core.current.environment.source.roles) &&
    (localAuthorBits p.state.core.current.environment a.declaration &&
      checkSmaller a.declaration.head a.clause.arguments))

/-- All finite source metadata is checked here. The remaining universal
capture-stability proposition is separate; nothing in this shell decides it. -/
structure StartShell (p : Problem) (a : OriginalAnchor p) : Prop where
  shape : CurrentAddressShape p a
  noGoalOutput : p.root.demand.outputs = []
  noWhereOutput : a.clause.outputs = []
  role : ∃ row ∈ p.state.core.current.environment.source.roles.rows,
    row.role = p.root.demand.role
  rolesValid : Valid p.state.core.current.environment.source.roles
  cover : DeclarationCovered p.state.core.current.environment a.declaration
  signature : a.declaration.Signature (authoredRegistry p.state.core.current).roles
  identified : a.declaration.Identified
  produced : a.declaration.Produced
  outputOnly : a.declaration.OutputOnly
  lexicalScope : a.declaration.Scoped
  smaller : Smaller a.declaration.head a.clause.arguments

private theorem role_here_exact (p : Problem) :
    (Checker408.originalRole p).isSome = true ↔
    ∃ row ∈ p.state.core.current.environment.source.roles.rows, row.role = p.root.demand.role := by
  constructor
  · intro yes
    cases h : Checker408.originalRole p with
    | none => simp [h] at yes
    | some row =>
      have origin := GeneralSourceMetadataRoles291.indexed h
      exact ⟨row,origin.1,origin.2⟩
  · exact Opaque448.original_role_is_read448 (p := p)

theorem finite_original_start_shell_exact {p : Problem} {a : OriginalAnchor p} :
    checkStartShell p a = true ↔ StartShell p a := by
  constructor
  · intro yes
    simp only [checkStartShell,Bool.and_eq_true] at yes
    obtain ⟨⟨⟨shape,goal⟩,out⟩,⟨⟨role,valid⟩,bits,small⟩⟩ := yes
    obtain ⟨covered,sig,ident,prod,os,ss⟩ := (local_author_bits_exact455 ..).mp bits
    exact ⟨of_decide_eq_true shape,List.isEmpty_iff.mp goal,List.isEmpty_iff.mp out,
      (role_here_exact p).mp role,(GeneralSourceMetadataRoles291.check_exact _).mp valid,
      covered,sig,ident,prod,os,ss,(checkSmaller_exact ..).mp small⟩
  · intro h
    simp only [checkStartShell,Bool.and_eq_true]
    exact ⟨⟨⟨decide_eq_true h.shape,List.isEmpty_iff.mpr h.noGoalOutput⟩,
        List.isEmpty_iff.mpr h.noWhereOutput⟩,
      ⟨⟨(role_here_exact p).mpr h.role,(GeneralSourceMetadataRoles291.check_exact _).mpr h.rolesValid⟩,
        (local_author_bits_exact455 ..).mpr
          ⟨h.cover,h.signature,h.identified,h.produced,h.outputOnly,h.lexicalScope⟩,
        (checkSmaller_exact ..).mpr h.smaller⟩⟩

private theorem exact_only_index_and_object {α : Type} {xs : List α} {i : Nat} {a : α}
    (length : xs.length = 1) (actual : xs[i]? = some a) :
    i = 0 ∧ xs = [a] := by
  cases xs with
  | nil => cases length
  | cons x xs =>
    cases xs with
    | cons _ _ => simp at length
    | nil =>
      cases i with
      | zero =>
        simp at actual
        subst a
        exact ⟨rfl,rfl⟩
      | succ => simp at actual

theorem shell_is_bound_to_the_single_actual_source_and_its_locations
    {p : Problem} {a : OriginalAnchor p} (g : StartShell p a) :
    a.location = ⟨0,0,0⟩ ∧
    visible p.state.core p.root = [a.declaration] ∧ a.declaration.head = [a.original] ∧
    a.declaration.requirements = [a.clause] ∧ p.root.demand.arguments = [a.capture] := by
  obtain ⟨loc1,deck⟩ := exact_only_index_and_object g.shape.1 a.actualVisible
  obtain ⟨loc2,head⟩ := exact_only_index_and_object g.shape.2.1 a.actualHead
  obtain ⟨loc3,where_⟩ := exact_only_index_and_object g.shape.2.2.1 a.actualClause
  have args := (exact_only_index_and_object g.shape.2.2.2.1 a.actualArgument).2
  refine ⟨?_,deck,head,where_,args⟩
  cases shape : a.location
  simp only [shape] at loc1 loc2 loc3
  simp [loc1,loc2,loc3]

theorem actual_shell_ready_iff_same_original_stable_capture {p : Problem} {a : OriginalAnchor p}
    (g : StartShell p a) :
    DeclarationReady (authoredRegistry p.state.core.current) a.declaration ↔
      StableSmaller a.declaration.head a.clause.arguments := by
  have exact := (shell_is_bound_to_the_single_actual_source_and_its_locations g).2.2.2.1
  constructor
  · intro r
    exact (r.descent a.clause (by rw [exact]; exact List.mem_cons_self)).2
  · intro fixed
    refine ⟨g.signature,g.identified,g.produced,g.outputOnly,g.lexicalScope,
      GeneralDeclarativeWitnessModeDeclaration357.scoped_decl g.cover,?_⟩
    intro child row
    rw [exact] at row
    cases List.mem_singleton.mp row
    exact ⟨g.smaller,fixed⟩

def joinActualStable {p : Problem} {a : OriginalAnchor p}
    (g : StartShell p a) (fixed : StableSmaller a.declaration.head a.clause.arguments) :
    EligibleStart p :=
  let fields := shell_is_bound_to_the_single_actual_source_and_its_locations g
  ⟨a.declaration,a.original,a.clause,a.capture,a.code,fields.2.1,fields.2.2.1,
    fields.2.2.2.1,fields.2.2.2.2,⟨g.shape.2.2.2.2.1,g.shape.2.2.2.2.2⟩,
    g.noGoalOutput,g.noWhereOutput,g.role,g.rolesValid,
    (actual_shell_ready_iff_same_original_stable_capture g).mpr fixed,a.compiled⟩

theorem with_stability_shell_keeps_exact_original_anchor {p : Problem} {a : OriginalAnchor p}
    (g : StartShell p a) (fixed : StableSmaller a.declaration.head a.clause.arguments) :
    (joinActualStable g fixed).anchor = a := by
  have loc := (shell_is_bound_to_the_single_actual_source_and_its_locations g).1
  cases a
  simp_all [EligibleStart.anchor,joinActualStable]

theorem genuine_original_eligible_shell_with_source_coverage {p : Problem} (a : EligibleStart p)
    (cover : DeclarationCovered p.state.core.current.environment a.declaration) :
    StartShell p a.anchor := by
  have originalClause : a.clause ∈ a.declaration.requirements := by
    rw [a.originalWhere]
    exact List.mem_cons_self
  exact ⟨⟨by simp [a.visibleOnly],by change a.declaration.head.length = 1; simp [a.originalHead],
      by change a.declaration.requirements.length = 1; simp [a.originalWhere],
      by simp [a.originalArguments],a.point.1,a.point.2⟩,
    a.noGoalOutputs,a.noWhereOutputs,a.role,a.rolesValid,cover,a.ready.signature,
    a.ready.identified,a.ready.produced,a.ready.outputOnly,a.ready.scopeOK,
    (a.ready.descent a.clause originalClause).1⟩

def readFiniteSourceShell (p : Problem) (loc : AnchorAddress) :
    Option {a : OriginalAnchor p // StartShell p a} := do
  let a ← readOriginalAnchor p loc
  if yes : checkStartShell p a = true then
    return ⟨a,finite_original_start_shell_exact.mp yes⟩
  else none

theorem actual_finite_shell_replays_without_any_stability_claim {p : Problem}
    (a : OriginalAnchor p) (g : StartShell p a) :
    readFiniteSourceShell p a.location = some ⟨a,g⟩ := by
  simp [readFiniteSourceShell,every_independent_anchor_replays a,Option.bind,
    finite_original_start_shell_exact.mpr g]

end Yulang.GeneralDeclarativeI65.I72.EligibleFieldStart461
