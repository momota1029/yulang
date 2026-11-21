import Yulang.GeneralDeclarativeHiddenState324
import Yulang.GeneralDeclarativeRank321
import Yulang.GeneralDeclarativeGraphRows321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeHiddenProbe324
open GeneralDeclarativeHiddenDecl324
open GeneralDeclarativeHiddenState324
open GeneralDeclarativeExampleSource320 (point leaf)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeDemand320 (Bounds Demand)
open GeneralDeclarativeLowerKnown321 (Ready Alias alias_refl knows_row)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeTrace321 (Trace Occurrence)
open GeneralDeclarativeEndpointProbe321 (HeadMatches)
open GeneralDeclarativePriority321 (Candidates Recurs)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeRank321 (graph_no_cycle)
open GeneralDeclarativeInspect321 (Visit variable_has_no_visit)
open GeneralNominalMaterialization (Mode)
open CommonRoleOutermostResolver (All₂)

theorem root_bounds (s : State) (n : Nat) : Bounds s (point n) := ⟨.refl _,.refl _⟩

theorem source_row (completed : Nat → Prop) {e : Equation} (known : e ∈ s0Rows) :
    e ∈ (restriction (support completed)).equations :=
  from_source (support completed) (.inl (.inl ⟨known,rfl⟩))

theorem root_trace (completed : Nat → Prop) (mode : Mode) :
    Trace (restriction (support completed)) mode 0 normCode [⟨0,mode,3⟩] := by
  have first : (⟨0,opened⟩ : Equation) ∈ s0Rows := by simp [s0Rows]
  have tail : (⟨2,empty⟩ : Equation) ∈ s0Rows := by simp [s0Rows]
  exact .record (alias_refl _) (source_row completed first) .capture
    (.primitive (args := []) (alias_refl _) (source_row completed tail) .nil)

theorem traces (completed : Nat → Prop) :
    HeadMatches (restriction (support completed)) catalogue interpretation root parent :=
  .cons ⟨root_bounds _ 0, normCode,[⟨0,.lower,3⟩],[⟨0,.upper,3⟩],normal_compiles,
    root_trace completed .lower,root_trace completed .upper⟩ .nil

theorem leaf_traces (completed : Nat → Prop) :
    HeadMatches (restriction (support completed)) catalogue interpretation child leaf :=
  .cons ⟨root_bounds _ 3,.variable 0,[⟨0,.lower,3⟩],[⟨0,.upper,3⟩],rfl,.capture,.capture⟩ .nil

theorem ready_root (completed : Nat → Prop) : Ready (support completed) root := by
  intro arg found
  cases List.mem_singleton.mp found
  exact ⟨_,knows_row (source_row completed (show (⟨0,direct⟩ : Equation) ∈ s0Rows by simp [s0Rows])) rfl⟩

theorem ready_child (completed : Nat → Prop) : Ready (support completed) child := by
  intro arg found
  cases List.mem_singleton.mp found
  exact ⟨_,knows_row (source_row completed
    (show (⟨3,.primitive (.scalar .int) []⟩ : Equation) ∈ s0Rows by simp [s0Rows])) rfl⟩

def weight (n : Nat) : Nat := if n = 0 then 1 else 0

theorem aliases {x y : Nat} (same : Alias final x y) : weight x = weight y := by
  have rowWeight {a b : Nat} (inRows : (⟨a,.variable b⟩ : Equation) ∈ final.equations) :
      weight a = weight b := by
    change _ ∈ finalRows at inRows
    simp only [finalRows,s0Rows,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at inRows
    rcases inRows with h|h|h|h|h|h <;> cases h <;> rfl
  have bw {a b : Nat} (read : GeneralDeclarativeBounds319.Bound final.normal a b) :
      weight a = weight b := by
    induction read with
    | refl => rfl
    | interval never => cases never
    | constraint never => cases never
    | trans _ _ x y => exact x.trans y
  induction same with
  | bounds read _ => exact bw read
  | forward found => exact rowWeight found
  | backward found => exact (rowWeight found).symm
  | trans _ _ x y => exact x.trans y

theorem no_cycle : ∀ n, ¬AliasCycle final (observed final) n := by
  apply graph_no_cycle weight (fun _ _ same => aliases same)
  rintro n head deeper ⟨code,entered,shape⟩ childThere
  change _ ∈ finalRows at entered
  simp only [finalRows,s0Rows,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at entered
  rcases entered with h|h|h|h|h|h <;> cases h
  all_goals cases shape
  all_goals first
    | (have same : deeper = 3 := List.mem_singleton.mp childThere; subst deeper; decide +kernel)
    | cases childThere

def tests (completed : Nat → Prop) : Candidates :=
  ⟨HeadMatches (restriction (support completed)) catalogue interpretation,
   fun demand decl => ¬HeadMatches (restriction (support completed)) catalogue interpretation demand decl⟩

theorem safe (completed : Nat → Prop) (d : Demand) :
    ¬Recurs final registry interpretation (tests completed) d := by
  rintro (⟨argument,_,cycle⟩|⟨impl,_,i,arg,pat,code,_,_,_,site,_,cycle⟩)
  · exact no_cycle argument.lower cycle
  · exact no_cycle site cycle

theorem exact_k2_positions {view} (read : Visit view name normCode site) : site = name := by
  cases read with
  | here => rfl
  | field _ _ field deeper =>
    have same := List.mem_singleton.mp field
    cases same
    exact False.elim (variable_has_no_visit deeper)

end Yulang.GeneralDeclarativeHiddenProbe324
