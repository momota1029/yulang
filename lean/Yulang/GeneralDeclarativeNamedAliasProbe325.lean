import Yulang.GeneralDeclarativeNamedAliasState325
import Yulang.GeneralDeclarativeRank321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNamedAliasProbe325
open GeneralDeclarativeHiddenWhere324 (root child parent implementation registry)
open GeneralDeclarativeHiddenDecl324 (catalogue interpretation empty normCode normal_compiles)
open GeneralDeclarativeHiddenState324 (direct opened)
open GeneralDeclarativeHiddenProbe324 (root_bounds)
open GeneralDeclarativeNamedAliasState325
open GeneralDeclarativeExampleSource320 (point)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeLowerKnown321 (Ready Alias alias_refl knows_row)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativeTrace321 (Trace)
open GeneralDeclarativeEndpointProbe321 (HeadMatches)
open GeneralDeclarativePriority321 (Candidates Recurs)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeRank321 (graph_no_cycle)
open GeneralNominalMaterialization (Mode)

theorem head_trace (done : Nat → Prop) (mode : Mode) :
    Trace (restriction (sources done)) mode 0 normCode [⟨0,mode,3⟩] :=
  .record (alias_refl _) (retained done (show (⟨0,opened⟩ : Equation) ∈ rows by simp [rows])) .capture
    (.primitive (args := []) (alias_refl _) (retained done (show (⟨2,empty⟩ : Equation) ∈ rows by simp [rows])) .nil)

theorem root_ready (done : Nat → Prop) : Ready (sources done) root := by
  intro a h
  cases List.mem_singleton.mp h
  exact ⟨_,knows_row (retained done (show (⟨0,direct⟩ : Equation) ∈ rows by simp [rows])) rfl⟩

theorem child_ready (done : Nat → Prop) : Ready (sources done) child := by
  intro a h
  cases List.mem_singleton.mp h
  exact ⟨_,knows_row (retained done (show (⟨3,.primitive (.scalar .int) []⟩ : Equation) ∈ rows
    by simp [rows])) rfl⟩

theorem root_probe (done : Nat → Prop) :
    HeadMatches (restriction (sources done)) catalogue interpretation root parent :=
  .cons ⟨root_bounds _ 0,normCode,[⟨0,.lower,3⟩],[⟨0,.upper,3⟩],normal_compiles,
    head_trace done .lower,head_trace done .upper⟩ .nil

theorem child_probe (done : Nat → Prop) :
    HeadMatches (restriction (sources done)) catalogue interpretation child implementation :=
  .cons ⟨root_bounds _ 3,.variable 0,[⟨0,.lower,3⟩],[⟨0,.upper,3⟩],rfl,.capture,.capture⟩ .nil

def rank (n : Nat) : Nat := if n = 0 ∨ n = 54 ∨ n = 55 then 1 else 0

theorem alias_rank {a b : Nat} (same : Alias ordinary a b) : rank a = rank b := by
  have aliasRow {x y : Nat} (h : (⟨x,.variable y⟩ : Equation) ∈ ordinary.equations) : rank x = rank y := by
    change _ ∈ rows at h
    simp only [rows,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with h|h|h|h|h|h|h|h <;> cases h <;> rfl
  have bound {x y : Nat} (h : GeneralDeclarativeBounds319.Bound ordinary.normal x y) : rank x = rank y := by
    induction h with
    | refl => rfl
    | interval none => cases none
    | constraint none => cases none
    | trans _ _ h j => exact h.trans j
  induction same with
  | bounds first _ => exact bound first
  | forward written => exact aliasRow written
  | backward written => exact (aliasRow written).symm
  | trans _ _ h j => exact h.trans j

theorem no_cycles : ∀ n, ¬AliasCycle ordinary (observed ordinary) n := by
  apply graph_no_cycle rank (fun _ _ same => alias_rank same)
  rintro n target child ⟨code,there,shape⟩ member
  change _ ∈ rows at there
  simp only [rows,List.mem_cons,List.not_mem_nil,or_false] at there
  rcases there with h|h|h|h|h|h|h|h <;> cases h
  all_goals cases shape
  all_goals first
    | (have same : child = 3 := List.mem_singleton.mp member; subst child; decide +kernel)
    | cases member

def tests (done : Nat → Prop) : Candidates :=
  ⟨HeadMatches (restriction (sources done)) catalogue interpretation,
   fun d impl => ¬HeadMatches (restriction (sources done)) catalogue interpretation d impl⟩

theorem safe (done : Nat → Prop) (d : Demand) :
    ¬Recurs ordinary registry interpretation (tests done) d := by
  rintro (⟨arg,_,cycle⟩|⟨_,_,_,_,_,_,_,_,_,site,_,cycle⟩)
  · exact no_cycles arg.lower cycle
  · exact no_cycles site cycle

end Yulang.GeneralDeclarativeNamedAliasProbe325
