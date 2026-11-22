import Yulang.GeneralDeclarativeWitnessAuthFixture351

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 33000
set_option maxHeartbeats 15000000
namespace Yulang.GeneralDeclarativeWitnessAuthModel351
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeWitnessCompiler350 (Finished)
open GeneralDeclarativeWitnessAuthFixture351
open GeneralDeclarativeWitnessWriterFixture351 (sourceEq out compilerRun key)
open GeneralDeclarativeWitnessOrderedModel350 (fixedState same_assignment)
open GeneralDeclarativeWitnessOrderedFixture350 (leafRows)
open GeneralDeclarativeFootprint321 (stateNames preserves_models)
open GeneralDeclarativeWitnessAuthWhole351 (Accepted Wire checked selected)
open GeneralDeclarativeExactDictionary337 (Evidence)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralSourceMetadataBundle291 (registry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open CommonNominalFullCarrier (Ty record exactEmpty subtype_refl)

def isTail (n : Nat) : Bool := [103,104,105,108,109].contains n
def writerTy (n : Nat) : Ty := if isTail n then exactEmpty else .base .int

def model : Assignment := fun n =>
  if n = 10 then (record 8 (.base .int) exactEmpty,Common.rowEmpty)
  else if 100 ≤ n then (writerTy n,Common.rowEmpty)
  else GeneralDeclarativeWitnessOrderedModel350.model n

theorem old_names :
    (stateNames fixedState).all (fun n => decide (n ≠ 10 ∧ n < 100)) = true := by decide +kernel

theorem old_model : Models fixedState model := by
  refine (preserves_models fixedState (first := GeneralDeclarativeWitnessOrderedModel350.model)
    (last := model) ?_).mp same_assignment
  intro n inOld
  have exactNames : n ≠ 10 ∧ n < 100 := of_decide_eq_true (List.all_eq_true.mp old_names n inOld)
  simp [model,exactNames.1,Nat.not_le_of_lt exactNames.2]

def atomOK : PresenceNormalForm.Atom Nat → Bool
  | .tyLe (.var a) (.var b) => decide (100 ≤ a ∧ 100 ≤ b ∧ isTail a = isTail b)
  | _ => false

theorem atom_sound (a : PresenceNormalForm.Atom Nat) (cert : atomOK a = true) :
    a.Holds CommonNominalFullCarrier.model model := by
  cases a with
  | tyLe l r =>
    cases l <;> cases r <;> try cases cert
    rename_i a b
    have ⟨largeA,largeB,same⟩ := of_decide_eq_true cert
    have notA : a ≠ 10 := by omega
    have notB : b ≠ 10 := by omega
    change CommonNominalFullCarrier.Subtype (model a).1 (model b).1
    simp only [model,notA,notB,largeA,largeB,ite_false,ite_true,writerTy,same]
    exact subtype_refl _
  | rowLe _ _ => cases cert

theorem actual_writer_atom_boundaries :
    (compilerRun.map (fun f => f.state.normal.ordinary.all atomOK)).getD false = true := by decide +kernel

theorem fixed_shared_model {f : Finished} (run : compilerRun = some f) : Models (state f) model := by
  have good := actual_writer_atom_boundaries
  rw [run] at good
  have fitted : f.state.normal.ordinary.all atomOK = true := good
  refine ⟨⟨(PresenceNormalForm.all_append ..).mpr ⟨old_model.1.1,?_⟩,old_model.1.2⟩,?_⟩
  · intro a h
    exact atom_sound a (List.all_eq_true.mp fitted a h)
  · intro e h
    change e ∈ (swapUpper fixedState).equations ++ [sourceEq] ++ leafRows 100 at h
    rcases List.mem_append.mp h with one|two
    · rcases List.mem_append.mp one with last|written
      · obtain ⟨former,known,rfl⟩ := List.mem_map.mp last
        by_cases atUpper : former.left = 2
        · rw [ite_eq_left atUpper]
          exact eqv_refl _
        · rw [ite_eq_right atUpper]
          exact old_model.2 former known
      · cases List.mem_singleton.mp written
        exact eqv_refl _
    · simp only [leafRows,List.mem_cons,List.not_mem_nil,or_false] at two
      rcases two with rfl|rfl|rfl|rfl|rfl|rfl <;> exact eqv_refl _

theorem setup_runs {f : Finished} {w : Wire} (built : setup = some (f,w)) :
    compilerRun = some f := by
  unfold setup at built
  cases run : compilerRun with
  | none => simp [run] at built
  | some production =>
    rw [run] at built
    change (do
      let producerCode ← GeneralDeclarativeWitnessWriterFixture351.code (state production) production
        GeneralDeclarativeWitnessOrderedFixture350.ranks
      let top ← expectedRun (problem (state production) [key]) [] GeneralDeclarativeWitnessOrderedFixture350.root
        GeneralDeclarativeWitnessOrderedFixture350.parent GeneralDeclarativeWitnessCutDecl334.arg
        GeneralDeclarativeWitnessCutDecl334.pat rootRead
      let left ← expectedRun (problem (state production) [key]) [0] GeneralDeclarativeWitnessOrderedFixture350.q0
        GeneralDeclarativeWitnessOrderedFixture350.kid0 GeneralDeclarativeWitnessOrderedFixture350.childArg childPattern childRead
      let right ← expectedRun (problem (state production) [key]) [1] GeneralDeclarativeWitnessOrderedFixture350.q1
        GeneralDeclarativeWitnessOrderedFixture350.kid1 GeneralDeclarativeWitnessOrderedFixture350.childArg childPattern childRead
      let outer ← parentCode (state production) top
      let l ← childCode (state production) left 50
      let r ← childCode (state production) right 80
      pure (production,⟨producerCode,GeneralDeclarativeWitnessWriterFixture351.answer,
        .node outer (.cons (.node l .nil) (.cons (.node r .nil) .nil))⟩)) = some (f,w) at built
    obtain ⟨c,_,eq⟩ := GeneralSourceMetadataExprDomain291.bind_success built
    obtain ⟨a,_,eq⟩ := GeneralSourceMetadataExprDomain291.bind_success eq
    obtain ⟨l,_,eq⟩ := GeneralSourceMetadataExprDomain291.bind_success eq
    obtain ⟨r,_,eq⟩ := GeneralSourceMetadataExprDomain291.bind_success eq
    obtain ⟨p,_,eq⟩ := GeneralSourceMetadataExprDomain291.bind_success eq
    obtain ⟨left,_,eq⟩ := GeneralSourceMetadataExprDomain291.bind_success eq
    obtain ⟨right,_,eq⟩ := GeneralSourceMetadataExprDomain291.bind_success eq
    exact congrArg (fun pair : Finished × Wire => some pair.1) (Option.some.inj eq)

theorem nonvacuous :
    ∃ (f : Finished) (w : Wire) (a : Accepted (problem (state f) [key]) w answer),
      setup = some (f,w) ∧ Models (state f) model ∧
      Evidence (registry a.env.bundle) (interpretation a.env.bundle.snapshot) model
        GeneralDeclarativeWitnessOrderedFixture350.root (.node 92 [.node 93 [],.node 94 []]) ∧
      ∀ row ∈ a.writer.owned, Holds model row.equation := by
  have ok := accepted
  unfold test at ok
  cases built : setup with
  | none => simp [built] at ok
  | some q =>
    obtain ⟨f,w⟩ := q
    have passes : GeneralDeclarativeWitnessAuthWhole351.check (problem (state f) [key]) w answer = true := by
      simpa [built] using ok
    obtain ⟨a⟩ := checked passes
    have fit := fixed_shared_model (setup_runs built)
    refine ⟨f,w,a,rfl,fit,(selected a rfl model fit).1,?_⟩
    intro row included
    obtain ⟨_,_,_,_,_,_,_,_,verified⟩ :=
      GeneralDeclarativeWitnessCatalog351.proves_writes a.writer model fit row included
    exact verified

end Yulang.GeneralDeclarativeWitnessAuthModel351
