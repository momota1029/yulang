import Yulang.GeneralDeclarativeWitnessTagFixture351

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32000
set_option maxHeartbeats 12000000
namespace Yulang.GeneralDeclarativeWitnessTagConcrete351
open GeneralDeclarativeWitnessTagFixture351
open GeneralDeclarativeWitnessCompiler350 (Accepted Finished)
open GeneralDeclarativeWitnessTagLocal351 (sound_local)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeWitnessAllocation350 (names)
open GeneralDeclarativeTaggedFixture340 (registry d a chosen whole checked covered wanted keep fallback targets)
open GeneralDeclarativeHiddenDecl324 (interpretation)
open GeneralDeclarativePlainFixture323 (source)
open GeneralDeclarativeTaggedFixtureModel340 (int boolean actualRoot entire)
open GeneralDeclarativeExactDictionary337 (Observed)
open GeneralDeclarativeEndpointBody336 (Meaning)
open GeneralNominalCommonBridge (Assignment variant_merge)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_trans eqv_symm variant_congr)
open CommonNominalFullCarrier (variant subtype_refl)

def model : Assignment := fun n =>
  (if n < 3 then actualRoot else if n = 3 then variant 7 int
   else if n = 4 then variant 7 boolean else if 6 ≤ n then entire else int,Common.rowEmpty)

def edges : List (Nat × Nat) :=
  [(7,13),(13,9),(13,13),(13,13),(14,7),(7,14),(15,9),(9,15),(14,13),(13,15),
    (13,13),(13,13),(16,7),(7,16),(17,9),(9,17),(16,13),(13,17)]

def printedRows : List Equation :=
  [sourceLow,sourceUpper,firstArm,lastArm,
    ⟨7,whole⟩,⟨8,whole⟩,⟨9,whole⟩,⟨10,whole⟩,⟨11,whole⟩,⟨12,whole⟩,
    ⟨1,.variant 7 (.variable 13)⟩,
    ⟨1,.variant 7 (.join (.variable 13) (.variable 13))⟩,⟨6,.variable 13⟩]

def normal : List (PresenceNormalForm.Atom Nat) :=
  edges.map (fun (l,h) => .tyLe (.var l) (.var h))

def matchesState (r : Run) (f : Finished) : Bool :=
  decide (f.state.normal.ordinary = normal ∧ f.state.normal.intervals = [(0,1),(1,2)] ∧
    f.state.equations = printedRows ∧ names r.ctx.spans = [(0,7,13,9),(1,7,13,9)])

theorem compiler_exact :
    (namedRun.map (fun (r,f) => matchesState r f)).getD false = true := by decide +kernel

theorem edge_sound (pair : Nat × Nat) (used : pair ∈ edges) :
    CommonNominalFullCarrier.Subtype (model pair.1).1 (model pair.2).1 := by
  simp only [edges,List.mem_cons,List.not_mem_nil,or_false] at used
  rcases used with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    exact subtype_refl _

theorem fitted {r : Run} {f : Finished} (known : namedRun = some (r,f)) :
    Models f.state model := by
  have stateEq := compiler_exact
  rw [known] at stateEq
  have ⟨atoms,links,written,_⟩ := of_decide_eq_true (show matchesState r f = true from stateEq)
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro row used
    rw [atoms] at used
    obtain ⟨pair,known,rfl⟩ := List.mem_map.mp used
    exact edge_sound pair known
  · intro pair known
    rw [links] at known
    rcases List.mem_cons.mp known with rfl|h
    · exact subtype_refl _
    · cases List.mem_singleton.mp h
      exact subtype_refl _
  · intro e inState
    rw [written] at inState
    simp only [printedRows,List.mem_cons,List.not_mem_nil,or_false] at inState
    rcases inState with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact eqv_refl _ | exact variant_merge 7 int boolean | exact eqv_trans (variant_merge 7 int boolean) (variant_congr 7 (eqv_symm (GeneralDeclarativePlainCapture323.union_same entire)))

theorem some_checked {r : Run} {f : Finished} (got : namedRun = some (r,f)) :
    ∃ wire, Nonempty (Accepted r.ctx f.state wire) := by
  have checkedResult := checked_named_compiler
  rw [got] at checkedResult
  change checkedCompiler r f = true at checkedResult
  unfold checkedCompiler at checkedResult
  cases built : GeneralDeclarativeWitnessOrderedFixture350.literalPlan f.state f.state with
  | none => simp [built] at checkedResult
  | some plan =>
    cases done : GeneralDeclarativeWitnessCompiler350.decode r.ctx f.state ⟨[],f.fixed,plan⟩ with
    | none => simp [built,done] at checkedResult
    | some good => exact ⟨_,⟨good⟩⟩

/-- Exact local source evidence and the ordinary compiler output agree
in an inhabited state. The retained payload is the whole joined
payload, not one arm or a fabricated literal source row. -/
theorem local_fixed_model :
    ∃ r f, namedRun = some (r,f) ∧ Models f.state model ∧
      Observed registry.constructors interpretation model a source ∧
      (∃ cap kids, Meaning registry interpretation model d chosen cap kids) ∧
      (model 6).1 = entire ∧ (model 13).1 = entire := by
  have tests := checked_named_compiler
  cases got : namedRun with
  | none => simp [got] at tests
  | some data =>
    obtain ⟨r,f⟩ := data
    have fit := fitted got
    obtain ⟨wire,⟨cert⟩⟩ := some_checked got
    obtain ⟨view,⟨cap,meaning⟩,_⟩ :=
      sound_local (r := registry) (d := d) (impl := chosen) (.named r.bounds) r.parsed
        (keep := keep) (fallback := fallback) (targets := targets) cert checked covered List.mem_cons_self rfl wanted
        rfl rfl model fit
    exact ⟨r,f,rfl,fit,view,⟨cap,_,meaning⟩,rfl,rfl⟩

end Yulang.GeneralDeclarativeWitnessTagConcrete351
