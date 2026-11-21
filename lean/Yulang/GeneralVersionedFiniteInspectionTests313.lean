import Yulang.GeneralNominalInspectionMatching
import Yulang.GeneralVersionedFirstHead313

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
/-! Finished inspection of a closed canonical actual value certifies its
constructor tests; unlike full matching, no binder realization, variable
linearity, or past dictionary is required. -/
namespace Yulang.GeneralVersionedFiniteInspectionTests313
open GeneralNominalRecursiveInspection GeneralNominalMaterialization
open GeneralNominalInspection (Query Bounds)
open GeneralNominalOriginTerms (Expr Head arity)
open GeneralNominalFiniteMeaning (At denote build)
open GeneralNominalInspectionAlignment
open GeneralNominalInspectionPositions (Input InputsAt structural_inputs nominal_inputs zip_reindex)
open GeneralNominalInspectionFiniteValues
open GeneralNominalCommonBridge (Assignment)

def Tests (m : Assignment) (schema : Schema) : Prop :=
  ∀ test ∈ schema.tests, Head m test.1 test.2

theorem actual_constructor {test : Test} {m : Assignment} {o : Origin}
    (parts : Fin (arity test) → Expr Nat)
    (actual : At m .actual o (denote (fun _ => .bottom) (.node test parts))) :
    Head m o test := by
  refine ⟨actual.1,?_⟩
  intro value observed
  have eq := actual.2 value observed
  cases test with
  | scalar base => exact eq
  | structural shape =>
    exact ⟨List.ofFn (fun i : Fin shape.arity => denote (fun _ => .bottom) (parts i)),
      List.length_ofFn ..,eq⟩
  | nominal name count =>
    exact ⟨List.ofFn (fun i : Fin count => Sum.inl (denote (fun _ => .bottom) (parts i))),
      List.length_ofFn ..,eq⟩

mutual
 theorem inspect_tests (state : GeneralNominalState.State) (m : Assignment)
    (valid : GeneralNominalState.Models state m) (query : Query) (bounds : Bounds state)
    (root : Origin) (term : Expr Nat)
    (finished : Finished (inspect state query bounds (some root)))
    (known : Input context m state bounds (some root) term) :
    Tests m (schema query root .actual) := by
  cases query with
  | variables names =>
    intro test member; simp only [schema] at member; cases member
  | deferred why => simp only [inspect,Finished,block] at finished; cases finished.1
  | scalar base =>
    simp only [inspect,finished_visit] at finished
    split at finished
    · simp only [Finished] at finished; cases finished.2.1
    · split at finished
      · rename_i observed desc
        split at finished
        · rename_i same
          obtain ⟨_,closed⟩ := known.1
          have eq := scalar_slot state m valid bounds.1 desc
          rw [← same] at eq
          obtain ⟨parts,finite⟩ := scalar_finite term closed.2.1 (CommonNominalFullCarrier.subtype_trans eq.2 known.2.1.1)
          have atRoot := known.2.2 root rfl
          rw [finite] at atRoot
          intro test member
          simp only [schema] at member
          cases List.mem_singleton.mp member
          exact actual_constructor parts atRoot
        · simp only [Finished] at finished; cases finished.2.1
      · simp only [Finished] at finished; cases finished.2.1
      · simp only [Finished,block] at finished; cases finished.1
  | node shape children =>
    simp only [inspect,finished_visit] at finished
    split at finished
    · rename_i lowerKind lower upperKind upper lowerAt upperAt
      split at finished
      · rename_i same
        obtain ⟨parts,finite,childInputs⟩ := structural_inputs state m valid bounds
          lowerKind upperKind lower upper lowerAt upperAt same.1 same.2 known
        have atRoot := known.2.2 root rfl
        rw [finite] at atRoot
        intro test member
        simp only [schema] at member
        rcases List.mem_cons.mp member with eq|nested
        · cases eq; exact actual_constructor parts atRoot
        · exact many_tests state m valid children _ (fun i => .structural root shape i) 0 _ finished childInputs test nested
      · simp only [Finished,block] at finished; cases finished.1
    · simp only [Finished] at finished; cases finished.2.1
    · simp only [Finished,block] at finished; cases finished.1
  | nominal name children =>
    obtain ⟨descriptor,intervals,recorded,same,found,complete,_⟩ := nominal_left state children bounds (some root) finished
    obtain ⟨parts,finite,childInputs⟩ := nominal_inputs state m valid bounds descriptor recorded found known
    have length := finished_length state children intervals _ 0 complete
    have atRoot := known.2.2 root rfl
    rw [finite] at atRoot
    rw [same] at atRoot childInputs
    intro test member
    simp only [schema] at member
    rcases List.mem_cons.mp member with eq|nested
    · cases eq
      rw [length]
      exact actual_constructor parts atRoot
    · exact many_tests state m valid children intervals (fun i => .nominal root name i) 0 _ complete childInputs test nested
 termination_by sizeOf query

 theorem many_tests (state : GeneralNominalState.State) (m : Assignment)
    (valid : GeneralNominalState.Models state m) (queries : List Query) (bounds : List (Bounds state))
    (origin : Nat → Origin) (offset : Nat) (terms : List (Expr Nat))
    (finished : Finished (inspectMany state queries bounds (fun i => some (origin i)) offset))
    (known : InputsAt context m state (fun i => some (origin i)) offset bounds terms) :
    Tests m (schemas queries origin .actual offset) := by
  cases queries with
  | nil =>
    intro test member; simp only [schemas] at member; cases member
  | cons query rest =>
    cases bounds with
    | nil => simp only [inspectMany,Finished] at finished; cases finished.2.2
    | cons head tail =>
      cases terms with
      | nil => cases known
      | cons term restTerms =>
        simp only [inspectMany,finished_append] at finished
        have first := finished
        intro test member
        simp only [schemas,Schema.append] at member
        exact (List.mem_append.mp member).elim
          (inspect_tests state m valid query head (origin offset) term first.1 known.1 test)
          (many_tests state m valid rest tail origin (offset+1) restTerms first.2 known.2 test)
 termination_by sizeOf queries
end

end Yulang.GeneralVersionedFiniteInspectionTests313
