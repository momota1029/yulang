import Yulang.GeneralDeclarativeWitnessOrderedFixture350

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000
namespace Yulang.GeneralDeclarativeWitnessOrderedModel350
open GeneralDeclarativeWitnessOrderedFixture350
open GeneralDeclarativeWitnessWhole350 (goal)
open GeneralDeclarativeHead320 (Models State Equation)
open GeneralDeclarativeWitnessForest350 (ProblemTree Code Fixed)
open GeneralDeclarativeWitnessRecordWhole350 (checked selected)
open GeneralDeclarativeExactDictionary337 (Evidence)
open GeneralNominalCommonBridge (Assignment)
open GeneralSourceMetadataBundle291 (registry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralDeclarativeEntailment320 (Holds)
open CommonNominalFullCarrier (Ty Subtype record exactEmpty emptyRecord subtype_refl
  exactEmpty_below_width common_record_mono)

inductive Kind where
  | int | endExact | endOpen | inner | outerExact | outerOpen
  deriving DecidableEq

def Kind.ty : Kind → Ty
  | .int => .base .int
  | .endExact => exactEmpty
  | .endOpen => emptyRecord
  | .inner => record 9 (.base .int) exactEmpty
  | .outerExact => record 7 (record 9 (.base .int) exactEmpty) exactEmpty
  | .outerOpen => record 7 (record 9 (.base .int) exactEmpty) emptyRecord

def classify (n : Nat) : Kind :=
  if n ∈ [0,1] then .outerExact
  else if n = 2 then .outerOpen
  else if n ∈ [3,4,5,20,21,22,26,27] then .inner
  else if n ∈ [25,29] then .endOpen
  else if n ∈ [23,24,28,53,54,55,58,59,83,84,85,88,89] then .endExact
  else .int

def model : Assignment := fun n => ((classify n).ty,Common.rowEmpty)

def compatible (a b : Kind) : Bool :=
  decide (a = b ∨ (a = .endExact ∧ b = .endOpen) ∨ (a = .outerExact ∧ b = .outerOpen))

theorem classified {a b : Kind} (g : compatible a b = true) : Subtype a.ty b.ty := by
  rcases of_decide_eq_true g with rfl|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact subtype_refl _
  · exact exactEmpty_below_width
  · exact common_record_mono 7 (subtype_refl _) exactEmpty_below_width

def atomOK : PresenceNormalForm.Atom Nat → Bool
  | .tyLe (.var l) (.var u) => compatible (classify l) (classify u)
  | _ => false

theorem atom_sound (a : PresenceNormalForm.Atom Nat) (g : atomOK a = true) :
    a.Holds CommonNominalFullCarrier.model model := by
  cases a with
  | tyLe l h =>
    cases l <;> cases h <;> try cases g
    exact classified g
  | rowLe _ _ => cases g

def fixedState : State :=
  (data.map (fun (p,l,r) => combined p l r)).getD prior

theorem ordinary_edges_checked : fixedState.normal.ordinary.all atomOK = true := by decide +kernel

theorem data_exists : data.isSome = true := by decide +kernel

theorem wanted_intervals : fixedState.normal.intervals = [(0,1),(1,2)] := by
  cases h : data with
  | none => have impossible := data_exists; simp [h] at impossible
  | some x => rcases x with ⟨a,b,c⟩; simp [fixedState,h,combined]

theorem wanted_rows :
    fixedState.equations = prior.equations ++ [rootOutput] ++ rootRows ++ leafRows 50 ++ leafRows 80 := by
  cases h : data with
  | none => have impossible := data_exists; simp [h] at impossible
  | some x => rcases x with ⟨a,b,c⟩; simp [fixedState,h,combined]

theorem same_assignment : Models fixedState model := by
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro a known
    exact atom_sound a (List.all_eq_true.mp ordinary_edges_checked a known)
  · intro e h
    rw [wanted_intervals] at h
    rcases List.mem_cons.mp h with rfl|here
    · exact subtype_refl _
    · cases List.mem_singleton.mp here
      exact common_record_mono 7 (subtype_refl _) exactEmpty_below_width
  · intro row h
    rw [wanted_rows] at h
    simp only [prior,rows,rootRows,leafRows,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with (((((rfl|rfl|rfl|rfl)|rfl)|rfl)|(rfl|rfl|rfl|rfl|rfl|rfl))|
      (rfl|rfl|rfl|rfl|rfl|rfl))|(rfl|rfl|rfl|rfl|rfl|rfl) <;> exact eqv_refl _

theorem problem_is_fixed {p : ProblemTree} {w : Code} (got : problemAndCode = some (p,w)) :
    p.current = fixedState := by
  unfold problemAndCode at got
  cases haveData : data with
  | none => simp [haveData] at got
  | some batch =>
    obtain ⟨root,l,r⟩ := batch
    rw [haveData] at got
    change (do
      let a ← parentCode (combined root l r) root
      let b ← childCode (combined root l r) l 50
      let c ← childCode (combined root l r) r 80
      pure (treeProblem (combined root l r),Code.node a (.cons (.node b .nil) (.cons (.node c .nil) .nil)))) = some (p,w) at got
    cases a : parentCode (combined root l r) root with
    | none => simp [a] at got
    | some aw =>
      cases b : childCode (combined root l r) l 50 with
      | none => simp [a,b] at got
      | some bw =>
        cases c : childCode (combined root l r) r 80 with
        | none => simp [a,b,c] at got
        | some cw =>
          have eq : (treeProblem (combined root l r),Code.node aw
            (.cons (.node bw .nil) (.cons (.node cw .nil) .nil))) = (p,w) := by
            simpa [a,b,c] using got
          cases eq
          simp [fixedState,haveData,treeProblem]

/-- The accepted tree is not vacuous: its actual compiler-generated
child demands and ordered dictionary share this explicit current model. -/
theorem nonvacuous :
    ∃ (p : ProblemTree) (w : Code) (a : GeneralDeclarativeWitnessRecordWhole350.Accepted p root answer),
      problemAndCode = some (p,w) ∧ Models p.current model ∧
      Evidence (registry a.global.table) (interpretation a.global.table.snapshot) model root
        (.node 92 [.node 93 [],.node 94 []]) ∧
      (∀ f ∈ a.diagnostic.fixed, ∀ e ∈ f.equations,Holds model e) := by
  have success := accepted
  unfold test at success
  cases codes : problemAndCode with
  | none => simp [codes] at success
  | some pair =>
    obtain ⟨p,w⟩ := pair
    have ok : GeneralDeclarativeWitnessRecordWhole350.check p root w answer = true := by
      simpa [codes] using success
    obtain ⟨a⟩ := checked ok
    have modelFit : Models p.current model := (problem_is_fixed codes).symm ▸ same_assignment
    have sound := selected a rfl model modelFit
    exact ⟨p,w,a,rfl,modelFit,sound.1,fun f h => (sound.2 f h).2⟩

end Yulang.GeneralDeclarativeWitnessOrderedModel350
