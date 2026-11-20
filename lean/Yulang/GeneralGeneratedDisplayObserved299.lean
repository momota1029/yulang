import Yulang.GeneralGeneratedDisplayBothCurrent299
import Yulang.GeneralGeneratedFrontierReceipt299
import Yulang.GeneralGeneratedDictionaryMemoCheck299
import Yulang.GeneralRebaseCompiledExecutor277

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralGeneratedDisplayObserved299
open GeneralNominalExamples (registry displayRoot displayChild)
open GeneralDeclarationExamples (roles)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralRebaseCompiledDisplay277 (after)
open GeneralRebaseDisplayExecutor276 (Goal localTable invocation)
open GeneralGeneratedFrontierReceipt299
open GeneralGeneratedDisplayTable299 (decode table)
open GeneralGeneratedDictionaryRun299 (run Read)
open GeneralGeneratedDictionaryRankCheck299 (Known)
open GeneralGeneratedDictionaryMemo299 (checkMemo)
open GeneralGeneratedDictionaryMemoCheck299 (bitFirst)
open GeneralGeneratedDictionaryScope299 (Faithful)
open GeneralNominalVersionedJournal232 (Models)
open CommonRoleOutermostResolver (Frontier Child)
open B4TargetV8

def goalAt : Nat → Option Goal
  | 0 => some .parent
  | 1 => some .child
  | _ => none

def encode : Goal → Option Nat
  | .parent => some 0
  | .child => some 1

def lookup (x : Nat) : Option (Frontier Goal) :=
  (goalAt x).map fun goal => .selected (localTable goal).1 (localTable goal).2

def observedTable : Read := readRows lookup encode

theorem roundtrip (g : Goal) (i : Nat) (hit : encode g = some i) : decode i = invocation g := by
  cases g <;> { cases Option.some.inj hit; rfl }

theorem observed (i : Nat) (f : Frontier Goal) (hit : lookup i = some f) :
    Local (boundary roles) registry after (decode i) (translate invocation f) := by
  cases i with
  | zero =>
    cases Option.some.inj hit
    exact GeneralRebaseCompiledExecutor277.exact_local .parent
  | succ i =>
    cases i with
    | zero =>
      cases Option.some.inj hit
      exact GeneralRebaseCompiledExecutor277.exact_local .child
    | succ i => cases hit

theorem faithful : Faithful (b:=boundary roles) (r:=registry) (s:=after) observedTable decode :=
  GeneralGeneratedFrontierReceipt299.faithful (b := boundary roles) (r := registry) (s := after) lookup encode decode invocation observed roundtrip

theorem checked_rows : observedTable = table := by
  funext i
  cases i with
  | zero => rfl
  | succ i =>
    cases i with
    | zero => rfl
    | succ i => rfl

theorem known : Known observedTable [0,1] := by
  intro i row hit
  rw [checked_rows] at hit
  rcases GeneralGeneratedDisplayTable299.rows i row hit with ⟨rfl,_⟩|⟨rfl,_⟩ <;> simp

theorem known_pass : checkMemo observedTable [0,1] 2 = true := rfl

theorem least_depth : bitFirst observedTable [0,1] 0 2 = some 2 := rfl

theorem no_child_below_child (d) : ¬ Child (Local (boundary roles) registry after) d displayChild := by
  rintro ⟨key,children,chosen,here⟩
  obtain ⟨_,rfl⟩ := Frontier.selected.inj
    (local_functional chosen GeneralRebaseCompiledSelection277.picked_child)
  cases here

theorem child_exact (d) : Child (Local (boundary roles) registry after) d displayRoot ↔ d = displayChild := by
  constructor
  · rintro ⟨key,children,chosen,here⟩
    obtain ⟨_,rfl⟩ := Frontier.selected.inj
      (local_functional chosen GeneralRebaseCompiledSelection277.picked_parent)
    exact List.mem_singleton.mp here
  · rintro rfl
    exact ⟨1,[displayChild],GeneralRebaseCompiledSelection277.picked_parent,List.mem_singleton_self _⟩

theorem semantically_accessible : Acc (Child (Local (boundary roles) registry after)) displayRoot := by
  apply Acc.intro
  intro d below
  cases (child_exact d).mp below
  exact Acc.intro _ (fun sub impossible => False.elim (no_child_below_child sub impossible))

theorem observed_result (m) (valid : Models after m) :
    (∃ d, run observedTable 2 0 = some d ∧
      Classify (boundary roles) registry after displayRoot (.selected d) ∧
      (boundary roles).Evidence registry after m displayRoot d) := by
  rw [checked_rows]
  exact ⟨.node 1 [.node 3 []],GeneralGeneratedDisplayTable299.computed_root,
    GeneralGeneratedDisplayTable299.actual_result.2.1,
    GeneralGeneratedDisplayBothCurrent299.root_from_current m valid⟩

end Yulang.GeneralGeneratedDisplayObserved299
