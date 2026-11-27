import Yulang.GeneralDeclarativeI65I74ReadyHeadCaptureReceipt466
import Yulang.GeneralDeclarativeWitnessNativePreparation360

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ActualHeadFrame467
open GeneralDeclarations (Declaration)
open GeneralDeclarativeI65 (visible)
open GeneralDeclarativeI65.I72.Checker408 (Problem)
open GeneralDeclarativeI65.I72.PreparedDeclarations463
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)

def literalRoleRows (r offset : Nat) : List Declaration → List (Nat × Declaration)
  | [] => []
  | first::rest =>
    if first.role = r then (offset,first)::literalRoleRows r (offset+1) rest
    else literalRoleRows r (offset+1) rest

theorem role_row_erasure_is_the_existing_authored_filter (r offset : Nat) (table : List Declaration) :
    (literalRoleRows r offset table).map Prod.snd = table.filter (fun d => d.role == r) := by
  induction table generalizing offset with
  | nil => rfl
  | cons d ds ih =>
    by_cases wanted : d.role = r
    · simp [literalRoleRows,wanted,ih]
    · simp [literalRoleRows,wanted,ih]

private theorem literal_role_rows_lower {r off i : Nat} {table : List Declaration} {d : Declaration}
    (there : (i,d) ∈ literalRoleRows r off table) : off ≤ i := by
  induction table generalizing off with
  | nil => simp [literalRoleRows] at there
  | cons head rest lower =>
    by_cases here : head.role = r
    · simp only [literalRoleRows,here,ite_true,List.mem_cons] at there
      rcases there with front|later
      · exact Nat.le_of_eq (congrArg Prod.fst front).symm
      · have on := lower later
        omega
    · simp [literalRoleRows,here] at there
      have on := lower there
      omega

theorem literal_role_rows_record_exact_unfiltered_ordinals
    (r offset : Nat) (table : List Declaration) (i : Nat) (d : Declaration) :
    (offset+i,d) ∈ literalRoleRows r offset table ↔ table[i]? = some d ∧ d.role = r := by
  induction table generalizing offset i with
  | nil => simp [literalRoleRows]
  | cons d₀ later ih =>
    cases i with
    | zero =>
      have noTail : (offset,d) ∉ literalRoleRows r (offset+1) later := by
        intro wrong
        have x := literal_role_rows_lower wrong
        omega
      by_cases here : d₀.role = r
      · simp [literalRoleRows,here,noTail]
        constructor
        · intro eq
          exact ⟨eq.symm,eq ▸ here⟩
        · intro eq
          exact eq.1.symm
      · simp [literalRoleRows,here,noTail]
        intro eq same
        exact here (eq.symm ▸ same)
    | succ i =>
      have off : offset + (i+1) = offset+1+i := by omega
      have noHead : (offset + (i+1),d) ≠ (offset,d₀) := by
        intro eq
        have bad := congrArg Prod.fst eq
        simp at bad
      by_cases here : d₀.role = r
      · simp only [literalRoleRows,here,ite_true,List.mem_cons,noHead,false_or,
          List.getElem?_cons_succ]
        rw [off]
        exact ih _ _
      · simp only [literalRoleRows,here,ite_false,List.getElem?_cons_succ]
        rw [off]
        exact ih _ _

def originalHeadOrdinal {p : Problem} (h : OriginalHead p) : Option Nat :=
  match literalRoleRows p.root.demand.role 0 p.state.core.current.environment.source.declarations with
  | [(i,d)] => if d = h.declaration then some i else none
  | _ => none

theorem a_single_visible_compiler_head_has_exactly_its_own_unfiltered_source_index
    {p : Problem} (h : OriginalHead p)
    (one : (visible p.state.core p.root).length = 1) :
    ∃ i, originalHeadOrdinal h = some i ∧
      p.state.core.current.environment.source.declarations[i]? = some h.declaration ∧
      ∀ j, p.state.core.current.environment.source.declarations[j]? = some h.declaration → j = i := by
  let decls := p.state.core.current.environment.source.declarations
  let kept := literalRoleRows p.root.demand.role 0 decls
  have eq : kept.map Prod.snd = visible p.state.core p.root :=
    role_row_erasure_is_the_existing_authored_filter .. 
  have length : kept.length = 1 := by
    have h := congrArg List.length eq
    rw [List.length_map,one] at h
    exact h
  obtain ⟨⟨i,d⟩,only⟩ := List.length_eq_one_iff.mp length
  have declared : h.declaration = d := by
    rw [only] at eq
    have atVisible := h.actualVisible
    rw [←eq] at atVisible
    have mem := List.mem_of_getElem? atVisible
    exact List.mem_singleton.mp mem
  subst d
  have found : (0+i,h.declaration) ∈ literalRoleRows p.root.demand.role 0 decls := by
    change (0+i,h.declaration) ∈ kept
    simp [only]
  have real := (literal_role_rows_record_exact_unfiltered_ordinals _ _ _ _ _).mp found
  refine ⟨i,?_,real.1,?_⟩
  · unfold originalHeadOrdinal
    have exactTable : literalRoleRows p.root.demand.role 0 decls = [(i,h.declaration)] := only
    change literalRoleRows p.root.demand.role 0 p.state.core.current.environment.source.declarations = [(i,h.declaration)] at exactTable
    rw [exactTable]
    simp
  · intro j equation
    have mem := (literal_role_rows_record_exact_unfiltered_ordinals _ 0 decls j h.declaration).mpr ⟨equation,real.2⟩
    have exactPair : (j,h.declaration) = (i,h.declaration) := by
      change (0+j,h.declaration) ∈ kept at mem
      simpa [only] using mem
    exact congrArg Prod.fst exactPair

open GeneralDeclarativeWitnessScopedBindings359 (FrameKey)
open GeneralDeclarativeWitnessNativePreparation360 (Layout Prepared)

def actualCompilerFrameKey {p : Problem} (h : OriginalHead p) : Option FrameKey :=
  (originalHeadOrdinal h).map fun i => ⟨p.root.occurrence,h.declaration.id,i⟩

theorem a_real_single_head_fixes_an_existing_prepared_frame_without_generating_authority
    {p : Problem} (h : OriginalHead p)
    (one : (visible p.state.core p.root).length = 1) :
    ∃ frame,
      actualCompilerFrameKey h = some frame ∧
      frame.occurrence = p.root.occurrence ∧
      frame.declaration = h.declaration.id ∧
      p.state.core.current.environment.source.declarations[frame.sourceOrdinal]? = some h.declaration ∧
      ∀ (layout : Layout) (existing : Prepared p.state.core.current.environment frame p.root.demand layout),
        existing.impl = h.declaration := by
  obtain ⟨i,at_i,sourceAt,_⟩ := a_single_visible_compiler_head_has_exactly_its_own_unfiltered_source_index h one
  refine ⟨⟨p.root.occurrence,h.declaration.id,i⟩,?_,rfl,rfl,sourceAt,?_⟩
  · simp [actualCompilerFrameKey,at_i]
  · intro _ actual
    exact Option.some.inj (actual.authored.symm.trans sourceAt)

end Yulang.GeneralDeclarativeI65.I72.ActualHeadFrame467


set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000