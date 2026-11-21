import Yulang.GeneralDeclarativeStableCrossBridge329
import Yulang.GeneralDeclarativeRank321

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 18000
set_option maxHeartbeats 15000000
namespace Yulang.GeneralDeclarativeStableCrossResolve329
open GeneralDeclarativeStableCrossBridge329 (current compiled literal_alias conserves)
open GeneralDeclarativeStableCrossCompile329 (requested final chosen declared inhabitance)
open GeneralDeclarativeStableCrossSource329 (oldRows)
open GeneralDeclarativeRepeatedSource323 (registry parent child goal pat a b checked well_covered scalar nominalCode)
open GeneralDeclarativeExampleSource320 (interp)
open GeneralDeclarativeHead320 (Equation Models)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeLowerKnown321 (Alias Ready alias_refl knows_row knows_alias)
open GeneralDeclarativeTrace321 (Trace)
open GeneralDeclarativeEndpointProbe321 (HeadMatches)
open GeneralDeclarativePriority321 (Candidates Recurs)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeRank321 (graph_no_cycle)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeStableReads329 (Heads)
open GeneralDeclarativeStableCompiler329 (Frame)
open GeneralDeclarativeStableSelect329 (Rule sound)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeEvidence320 (Evidence)
open CommonRoleOutermostResolver (Classify Dictionary)

theorem table : current.equations = oldRows ++ [⟨11,nominalCode 7⟩,⟨3,.variable 7⟩] := rfl
def support : Supported current (fun _ => False) :=
  ⟨fun e origin => e ∈ oldRows ∧ origin = .source,by
    intro e _ h
    rw [table]
    exact List.mem_append_left _ h.1⟩
theorem lit {e : Equation} (found : e ∈ oldRows) : e ∈ (restriction support).equations :=
  from_source _ ⟨found,rfl⟩

theorem child_range : Bounds current (⟨13,3,14⟩ : Capture) :=
  compiled.ranges 0 (by decide +kernel)

theorem parent_ready : Ready support goal := by
  intro arg found
  change arg ∈ [a,b] at found
  rcases List.mem_cons.mp found with rfl|later
  · exact ⟨_,knows_row (lit (show (⟨0,nominalCode 3⟩ : Equation) ∈ oldRows from List.mem_cons_self)) rfl⟩
  · cases List.mem_singleton.mp later
    exact ⟨_,knows_row (lit (show (⟨10,nominalCode 7⟩ : Equation) ∈ oldRows by simp [oldRows])) rfl⟩

theorem child_ready : Ready support requested := by
  intro arg found
  cases List.mem_singleton.mp found
  exact ⟨_,knows_alias (literal_alias support) (knows_row
    (lit (show (⟨3,scalar⟩ : Equation) ∈ oldRows by simp [oldRows])) rfl)⟩

theorem parent_matches : HeadMatches (restriction support) registry.constructors interp goal parent := by
  refine .cons ⟨?_,nominalCode 0,[⟨0,.actual,3⟩],[⟨0,.actual,4⟩],rfl,?_,?_⟩
    (.cons ⟨?_,nominalCode 0,[⟨0,.actual,7⟩],[⟨0,.actual,8⟩],rfl,?_,?_⟩ .nil)
  · exact ⟨.interval List.mem_cons_self,.interval (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  · exact .nominal (args := [3]) (alias_refl _) (lit (show (⟨0,nominalCode 3⟩ : Equation) ∈ oldRows from
      List.mem_cons_self)) (.cons .capture .nil)
  · exact .nominal (args := [4]) (alias_refl _) (lit (show (⟨2,nominalCode 4⟩ : Equation) ∈ oldRows by
      simp [oldRows])) (.cons .capture .nil)
  · exact ⟨.interval (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
      .interval (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))⟩
  · exact .nominal (args := [7]) (alias_refl _) (lit (show (⟨10,nominalCode 7⟩ : Equation) ∈ oldRows by
      simp [oldRows])) (.cons .capture .nil)
  · exact .nominal (args := [8]) (alias_refl _) (lit (show (⟨12,nominalCode 8⟩ : Equation) ∈ oldRows by
      simp [oldRows])) (.cons .capture .nil)

theorem child_matches : HeadMatches (restriction support) registry.constructors interp requested child :=
  .cons ⟨child_range,.variable 0,[⟨0,.lower,13⟩],[⟨0,.upper,14⟩],rfl,.capture,.capture⟩ .nil

def rank (n : Nat) := if n ≤ 2 ∨ (10 ≤ n ∧ n ≤ 12) then 1 else 0

abbrev atom (a b : Nat) := PresenceNormalForm.Atom.tyLe (.var a) (.var b)
abbrev aggregateAtoms (l u : Nat) : List (PresenceNormalForm.Atom Nat) :=
  [atom 3 3,atom 3 3,atom 7 3,atom 3 7,
    .tyLe (.var l) (.union (.var 3) (.var 7)),.tyLe (.union (.var 3) (.var 7)) (.var l),
    .tyLe (.var u) (.inter (.var 3) (.var 7)),.tyLe (.inter (.var 3) (.var 7)) (.var u),
    atom l 3,atom 3 u]

theorem constraints : current.normal.ordinary =
    aggregateAtoms 13 14 ++ aggregateAtoms 15 16 ++ [atom 13 3,atom 3 13,atom 14 3,atom 3 14] := rfl

theorem alias_rank {a b : Nat} (same : Alias current a b) : rank a = rank b := by
  have recorded {a b : Nat} (p : (⟨a,.variable b⟩ : Equation) ∈ current.equations) : rank a = rank b := by
    rw [table] at p
    simp only [oldRows,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at p
    rcases p with h|h|h|h|h|h|h|h|h|h <;> cases h <;> rfl
  have bound {a b} (p : GeneralDeclarativeBounds319.Bound current.normal a b) : rank a = rank b := by
    induction p with
    | refl => rfl
    | trans _ _ x y => exact x.trans y
    | interval there =>
      change _ ∈ [(0,1),(1,2),(10,11),(11,12)] at there
      simp only [List.mem_cons,List.not_mem_nil,or_false] at there
      rcases there with h|h|h|h <;> cases h <;> rfl
    | constraint there =>
      rw [constraints] at there
      simp only [aggregateAtoms,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at there
      rcases there with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> cases h <;> rfl
  induction same with
  | bounds yes _ => exact bound yes
  | forward yes => exact recorded yes
  | backward yes => exact (recorded yes).symm
  | trans _ _ yes other => exact yes.trans other

theorem no_cycle : ∀ a, ¬AliasCycle current (observed current) a := by
  apply graph_no_cycle rank (fun _ _ h => alias_rank h)
  rintro a shape part ⟨exp,listed,read⟩ member
  rw [table] at listed
  simp only [oldRows,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at listed
  rcases listed with h|h|h|h|h|h|h|h|h|h <;> cases h
  all_goals cases read
  all_goals simp [GeneralDeclarativeK2Graph321.Shape.children] at member
  all_goals (subst part; decide +kernel)

def tests : Candidates :=
  ⟨HeadMatches (restriction support) registry.constructors interp,
    fun d decl => ¬HeadMatches (restriction support) registry.constructors interp d decl⟩

theorem safe (d : Demand) : ¬Recurs current registry interp tests d := by
  rintro (⟨root,_,loop⟩|⟨_,_,_,_,_,_,_,_,_,whereAt,_,loop⟩)
  · exact no_cycle root.lower loop
  · exact no_cycle whereAt loop

def leafBase (_ : Nat) : Capture := ⟨13,3,14⟩
def leafFrame : Frame current registry interp requested child [] := by
  refine ⟨leafBase,[(0,leafBase 0)],?_,(by intro _ h; cases h),
    (fun _ _ => child_range),(fun _ _ => 18),[],current,current,[],rfl,
    GeneralDeclarativeClauseBatch327.reflexive _,[],rfl,(fun _ h => False.elim (List.not_mem_nil h)),
    [],rfl,(fun _ h => False.elim (List.not_mem_nil h)),rfl⟩
  exact Heads.cons (first := [(0,leafBase 0)]) (rest := []) ⟨child_range,.variable 0,.variable 3,rfl,.refl _,.capture⟩ .nil

abbrev localRule := Rule current registry interp support tests
abbrev dict : Dictionary := .node parent.id [.node child.id []]

theorem root_only (d) (visible : d ∈ registry.declarations) (role : d.role = goal.role) : d = parent := by
  rcases List.mem_cons.mp visible with rfl|later
  · rfl
  · cases List.mem_singleton.mp later; cases role

theorem child_only (d) (visible : d ∈ registry.declarations) (role : d.role = requested.role) : d = child := by
  rcases List.mem_cons.mp visible with rfl|later
  · cases role
  · exact List.mem_singleton.mp later

theorem root_selected : localRule goal (.selected parent.id [requested]) := by
  refine .selected parent_ready (safe _) ?_ ⟨⟨List.mem_cons_self,rfl⟩,parent_matches⟩ ?_ ⟨compiled⟩
  · rintro ⟨d,⟨present,role⟩,wait⟩
    cases root_only d present role
    exact wait parent_matches
  · rintro d ⟨⟨present,role⟩,_⟩
    rw [root_only d present role]

theorem child_selected : localRule requested (.selected child.id []) := by
  refine .selected child_ready (safe _) ?_
    ⟨⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩,child_matches⟩ ?_ ⟨leafFrame⟩
  · rintro ⟨d,⟨present,role⟩,wait⟩
    cases child_only d present role
    exact wait child_matches
  · rintro d ⟨⟨present,role⟩,_⟩
    rw [child_only d present role]

theorem tree : Classify localRule goal (.selected dict) :=
  ⟨.selected parent.id [.selected child.id []],
    .selected root_selected (.cons (.selected child_selected .nil) .nil),
    .selected (.cons (.selected .nil (.selected rfl)) .nil) (.selected rfl)⟩

theorem typed (m) (fit : Models current m) : Evidence registry interp m goal dict :=
  sound checked well_covered declared fit tree

theorem nonvacuous : ∃ m, Models current m ∧ Evidence registry interp m goal dict := by
  obtain ⟨m,fit⟩ := inhabitance
  have valid := (conserves m).mpr fit
  exact ⟨m,valid,typed m valid⟩

end Yulang.GeneralDeclarativeStableCrossResolve329
