import Yulang.GeneralDeclarativeWitnessRepeatedFixture350

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 10000000
namespace Yulang.GeneralDeclarativeWitnessRepeatModel350
open GeneralDeclarativeWitnessRepeatedFixture350
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWitnessCompiler350 (Finished)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativeRecordSplit330 (bottom)
open GeneralNominalTopObservation (le_top)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open CommonNominalFullCarrier (Ty Subtype Equivalent record exactEmpty emptyRecord subtype_refl
  common_record_mono exactEmpty_below_width common_union_is_join common_inter_is_meet)
open GeneralDeclarativeExactDictionary337 (Evidence)
open GeneralDeclarativeWitnessRecordWhole350 (checked selected)
open GeneralSourceMetadataBundle291 (registry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeEndpointCase336 (endCode)
open GeneralDeclarativeEndpointMixedTail336 (width)
open Core.PresenceGeneration (TyTerm)

def int : Ty := .base .int
def typeAt (n : Nat) : Ty :=
  if n = 0 then record 7 .bottom (record 8 int exactEmpty)
  else if n = 1 then record 7 int (record 8 int exactEmpty)
  else if n = 2 then record 7 .top (record 8 .top emptyRecord)
  else if n ∈ [3,20] then .bottom
  else if n ∈ [6,7,22,25] then .top
  else if n ∈ [26,27,33] then exactEmpty
  else if n ∈ [28,34] then emptyRecord
  else if n ∈ [29,31] then .union .bottom int
  else if n ∈ [30,32] then .inter .top .top
  else int

def model : Assignment := fun n => (typeAt n,Common.rowEmpty)

def atom (a b : TyTerm Nat) : PresenceNormalForm.Atom Nat := .tyLe a b
def edge (a b : Nat) : PresenceNormalForm.Atom Nat := atom (.var a) (.var b)
def loTerm : TyTerm Nat := .union (.var 20) (.var 23)
def hiTerm : TyTerm Nat := .inter (.var 22) (.var 25)
def compound (a b : Nat) : List (PresenceNormalForm.Atom Nat) :=
  [edge 21 21,edge 21 21,edge 24 21,edge 21 24,atom (.var a) loTerm,atom loTerm (.var a),
   atom (.var b) hiTerm,atom hiTerm (.var b),edge a 21,edge 21 b]

def expectedAtoms : List (PresenceNormalForm.Atom Nat) :=
  [edge 20 21,edge 21 22,edge 23 24,edge 24 25,edge 26 27,edge 27 28] ++
    compound 29 30 ++ compound 31 32 ++
    [edge 27 27,edge 27 27,edge 33 26,edge 26 33,edge 34 28,edge 28 34,edge 33 27,edge 27 34]

def compiledMatches (f : Finished) : Bool :=
  decide (f.state.normal.ordinary = expectedAtoms ∧
    f.state.normal.intervals = [(0,1),(1,2)] ∧ f.state.equations = [lo,hi,center,theTie,fixedOut])

theorem actual_atoms :
    (finished.map compiledMatches).getD false = true := by decide +kernel

theorem center_at_aggregate : Subtype (.union .bottom int) int :=
  (common_union_is_join ..).mpr ⟨bottom _,subtype_refl _⟩

theorem upper_at_aggregate : Subtype int (.inter .top .top) :=
  (common_inter_is_meet ..).mpr ⟨le_top _,le_top _⟩

theorem atoms_fit (a : PresenceNormalForm.Atom Nat) (got : a ∈ expectedAtoms) :
    a.Holds CommonNominalFullCarrier.model model := by
  simp only [expectedAtoms,compound,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at got
  rcases got with (((rfl|rfl|rfl|rfl|rfl|rfl)|
    (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl))|
    (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl))|
    (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;>
    first | exact subtype_refl _ | exact le_top _ | exact bottom _ | exact exactEmpty_below_width | exact center_at_aggregate | exact upper_at_aggregate

theorem valid {run : Finished} (ran : finished = some run) :
    Models (fullState run) model := by
  have ok := actual_atoms
  rw [ran] at ok
  have ⟨ordinary,intervals,rows⟩ := of_decide_eq_true (show compiledMatches run = true from ok)
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro a chosen
    have listed : a ∈ run.state.normal.ordinary := chosen
    exact atoms_fit _ (ordinary ▸ listed)
  · intro pair chosen
    have listed : pair ∈ run.state.normal.intervals := chosen
    rw [intervals] at listed
    rcases List.mem_cons.mp listed with rfl|other
    · exact common_record_mono 7 (bottom _) (subtype_refl _)
    · cases List.mem_singleton.mp other
      exact common_record_mono 7 (le_top _) (common_record_mono 8 (le_top _) exactEmpty_below_width)
  · intro e written
    change e ∈ run.state.equations ++ evidenceRows at written
    rw [rows] at written
    simp only [evidenceRows,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at written
    rcases written with (rfl|rfl|rfl|rfl|rfl)|(rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;>
      exact eqv_refl _

theorem cover {run : Finished} (ran : finished = some run) : Models (removeTie (fullState run)) model :=
  ⟨(valid ran).1,fun e h => (valid ran).2 e (List.mem_filter.mp h).1⟩

/-- Nonvacuous I-58 example using a derived equality rather than a
literal tie row. The lower and upper endpoints do not determine the
actual center; the compiler receipt is satisfied by the same model. -/
theorem nonvacuous :
    ∃ (run : Finished) (wire : GeneralDeclarativeWitnessRecordReplay350.Wire)
      (a : GeneralDeclarativeWitnessRecordWhole350.Accepted
        (problem (removeTie (fullState run))) root answer),
      finished = some run ∧ buildNoLiteralTie run (removeTie (fullState run)) = some wire ∧
      Models (removeTie (fullState run)) model ∧
      Evidence (registry a.global.table) (interpretation a.global.table.snapshot) model root (.node 92 []) := by
  have yup := derived_tie_accepted
  unfold acceptedWith at yup
  cases run : finished with
  | none => simp [run] at yup
  | some f =>
    cases w : buildNoLiteralTie f (removeTie (fullState f)) with
    | none => simp [run,w] at yup
    | some wire =>
      have ok : GeneralDeclarativeWitnessRecordWhole350.check
        (problem (removeTie (fullState f))) root (.node wire .nil) answer = true := by
        simpa [run,w] using yup
      obtain ⟨a⟩ := checked ok
      have sound := selected a rfl model (cover run)
      exact ⟨f,wire,a,rfl,w,cover run,sound.1⟩

end Yulang.GeneralDeclarativeWitnessRepeatModel350
