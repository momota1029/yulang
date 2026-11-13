import Yulang.GeneralDictionaryActualSchema

/-! Full materialization-schema replay with changed target-source identities.
Renaming preserves path labels but can change source roots and need not be
injective. Type equivalence at source roots is explicit, not assumed to follow
from arbitrary reallocation. Actual-only schemas allow one-way capture Fits. -/
namespace Yulang.GeneralDictionaryActualSchemaOrigin
open GeneralDeclarations GeneralNominalMaterialization GeneralNominalRecursiveInspection
open CommonNominalFullCarrier GeneralDictionaryActualSchema

def renameOrigin (rename : Nat → Nat) : Origin → Origin
  | .source n => .source (rename n)
  | .nominal parent name index => .nominal (renameOrigin rename parent) name index
  | .structural parent shape index => .structural (renameOrigin rename parent) shape index

def renameUse (rename : Nat → Nat) (u : Use) : Use :=
  { u with origin := renameOrigin rename u.origin }

def renameSchema (rename : Nat → Nat) (s : Schema) : Schema :=
  ⟨s.variables.map (renameUse rename),
    s.tests.map (fun t => (renameOrigin rename t.1,t.2)),s.unknown⟩

theorem rename_empty (rename : Nat → Nat) : renameSchema rename {} = {} := rfl

theorem rename_append (rename : Nat → Nat) (a b : Schema) :
    renameSchema rename (a.append b) = (renameSchema rename a).append (renameSchema rename b) := by
  cases a; cases b
  simp [renameSchema,Schema.append,List.map_append]

theorem rename_test (rename : Nat → Nat) (s : Schema) (t : Origin × Test) :
    renameSchema rename { s with tests := t :: s.tests } =
      { renameSchema rename s with tests := (renameOrigin rename t.1,t.2) :: (renameSchema rename s).tests } := rfl

mutual
  theorem schema_rename (rename : Nat → Nat) (query : GeneralNominalInspection.Query)
      (origin : Origin) (mode : Mode) :
      renameSchema rename (schema query origin mode) = schema query (renameOrigin rename origin) mode := by
    cases query with
    | variables names =>
      simp only [schema,renameSchema,List.map_map]
      rfl
    | scalar base => simp only [schema,renameSchema]; rfl
    | deferred p => simp only [schema,renameSchema]; rfl
    | node shape children =>
      rw [schema,schema,rename_test,schemas_rename]
      rfl
    | nominal name children =>
      rw [schema,schema,rename_test,schemas_rename]
      rfl
  termination_by sizeOf query

  theorem schemas_rename (rename : Nat → Nat) (queries : List GeneralNominalInspection.Query)
      (origins : Nat → Origin) (mode : Mode) (index : Nat) :
      renameSchema rename (schemas queries origins mode index) =
        schemas queries (fun i => renameOrigin rename (origins i)) mode index := by
    cases queries with
    | nil => rw [schemas,schemas]; rfl
    | cons query rest =>
      rw [schemas,schemas,rename_append,schema_rename,schemas_rename]
  termination_by sizeOf queries
end

def renameRequest (rename : Nat → Nat) (r : Request) : Request :=
  { r with target := rename r.target }

theorem fold_rename (rename : Nat → Nat) (ss : List Schema) :
    renameSchema rename (ss.foldr Schema.append {}) =
      (ss.map (renameSchema rename)).foldr Schema.append {} := by
  induction ss with
  | nil => rfl
  | cons s rest ih => simp only [List.foldr_cons,List.map_cons,rename_append,ih]

/-- The renamed object is the actual generator applied to retargeted requests,
not an unrelated schema supplied as a premise. Patterns and modes are unchanged. -/
theorem generated_rename (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation) (rename : Nat → Nat) (rs : List Request) :
    renameSchema rename (generated state interpretation rs) =
      generated state interpretation (rs.map (renameRequest rename)) := by
  unfold generated
  rw [fold_rename]
  simp only [List.map_map]
  congr 2
  funext r
  exact schema_rename rename _ _ _

theorem equivalent_trans (a b c : Ty) (ab : Equivalent a b) (bc : Equivalent b c) :
    Equivalent a c := ⟨subtype_trans ab.1 bc.1,subtype_trans bc.2 ab.2⟩

theorem equivalent_symm (a b : Ty) (ab : Equivalent a b) : Equivalent b a := ⟨ab.2,ab.1⟩

/-- Root-source type equivalence induces a real observation simulation, even
when the current source IDs differ. No child observation is assumed. -/
theorem observes_pull (model : GeneralNominalCommonBridge.Assignment) (rename : Nat → Nat)
    (roots : ∀ n, Equivalent (model (rename n)).1 (model n).1)
    (origin : Origin) (actual : Ty) (seen : Observes model (renameOrigin rename origin) actual) :
    ∃ oldActual, Observes model origin oldActual ∧ Equivalent actual oldActual := by
  induction origin generalizing actual with
  | source n =>
    cases seen
    exact ⟨(model n).1,.source n,roots n⟩
  | nominal parent name index ih =>
    cases seen with
    | nominal parentSeen eq found =>
      obtain ⟨oldParent,oldSeen,same⟩ := ih _ parentSeen
      exact ⟨actual,.nominal oldSeen (equivalent_trans _ _ _ (equivalent_symm _ _ same) eq) found,
        ⟨subtype_refl _,subtype_refl _⟩⟩
  | structural parent shape index ih =>
    cases seen with
    | structural parentSeen length eq found =>
      obtain ⟨oldParent,oldSeen,same⟩ := ih _ parentSeen
      exact ⟨actual,.structural oldSeen length (equivalent_trans _ _ _ (equivalent_symm _ _ same) eq) found,
        ⟨subtype_refl _,subtype_refl _⟩⟩

theorem observes_push (model : GeneralNominalCommonBridge.Assignment) (rename : Nat → Nat)
    (roots : ∀ n, Equivalent (model (rename n)).1 (model n).1)
    (origin : Origin) (actual : Ty) (seen : Observes model origin actual) :
    ∃ currentActual, Observes model (renameOrigin rename origin) currentActual ∧ Equivalent currentActual actual := by
  induction seen with
  | source n => exact ⟨(model (rename n)).1,.source _,roots n⟩
  | nominal parentSeen eq found ih =>
    obtain ⟨currentParent,currentSeen,same⟩ := ih
    exact ⟨_,.nominal currentSeen (equivalent_trans _ _ _ same eq) found,
      ⟨subtype_refl _,subtype_refl _⟩⟩
  | structural parentSeen length eq found ih =>
    obtain ⟨currentParent,currentSeen,same⟩ := ih
    exact ⟨_,.structural currentSeen length (equivalent_trans _ _ _ same eq) found,
      ⟨subtype_refl _,subtype_refl _⟩⟩

theorem test_transport (test : Test) (a b : Ty) (same : Equivalent a b)
    (valid : test.Holds b) : test.Holds a := by
  cases test with
  | scalar base => exact equivalent_trans _ _ _ same valid
  | structural shape =>
    obtain ⟨values,length,equal⟩ := valid
    exact ⟨values,length,equivalent_trans _ _ _ same equal⟩
  | nominal name arity =>
    obtain ⟨arguments,length,equal⟩ := valid
    exact ⟨arguments,length,equivalent_trans _ _ _ same equal⟩

theorem variable_equivalent (declaration : Declaration) (capture : GeneralDeclarationDemands.Capture)
    (model : GeneralNominalCommonBridge.Assignment) (name : Nat) (mode : Mode)
    (a b : Ty) (same : Equivalent a b)
    (valid : VariableHolds declaration capture model name mode b) :
    VariableHolds declaration capture model name mode a := by
  unfold VariableHolds at valid ⊢
  by_cases output : name ∈ declaration.outputNames
  · simp only [output,ite_true] at valid ⊢
    exact equivalent_trans _ _ _ same valid
  · simp only [output,ite_false] at valid ⊢
    cases mode with
    | lower | upper => exact equivalent_trans _ _ _ same valid
    | actual => exact ⟨subtype_trans valid.1 same.2,subtype_trans same.1 valid.2⟩

/-- Full schema Models follows from atomic source and capture semantics.
Current capture origins correspond to renamed historical origins; target IDs
need not be equal, and no current schema Models premise occurs. -/
theorem replay (declaration : Declaration) (oldCapture currentCapture : GeneralDeclarationDemands.Capture)
    {oldState currentState : GeneralNominalState.State}
    (oldReport : Report oldState) (currentReport : Report currentState)
    (s : Schema) (rename : Nat → Nat) (model : GeneralNominalCommonBridge.Assignment)
    (roots : ∀ n, Equivalent (model (rename n)).1 (model n).1)
    (actualOnly : ActualOnly s)
    (outputs : ∀ name, name ∈ declaration.outputNames →
      Equivalent (model (currentCapture.outputs name)).1 (model (oldCapture.outputs name)).1)
    (inputs : ∀ name, name ∉ declaration.outputNames → ∀ actual,
      GeneralNominalCaptureMerges.Fits model (oldCapture.inputs name) actual →
      GeneralNominalCaptureMerges.Fits model (currentCapture.inputs name) actual)
    (origins : ∀ captured ∈ currentReport.captures, ∀ origin, captured.origin = some origin →
      ∃ old ∈ oldReport.captures, old.name = captured.name ∧
        ∃ oldOrigin, old.origin = some oldOrigin ∧ origin = renameOrigin rename oldOrigin)
    (valid : GeneralNominalMaterialization.Models oldState declaration oldCapture oldReport s model) :
    GeneralNominalMaterialization.Models currentState declaration currentCapture currentReport
      (renameSchema rename s) model := by
  refine ⟨?_,?_,?_,?_⟩
  · intro test member
    obtain ⟨oldTest,oldMember,rfl⟩ := List.mem_map.mp member
    obtain ⟨witness,seen⟩ := (valid.1 oldTest oldMember).1
    obtain ⟨currentWitness,currentSeen,_⟩ := observes_push model rename roots oldTest.1 witness seen
    refine ⟨⟨currentWitness,currentSeen⟩,?_⟩
    intro actual seen
    obtain ⟨oldActual,oldSeen,same⟩ := observes_pull model rename roots oldTest.1 actual seen
    exact test_transport oldTest.2 actual oldActual same ((valid.1 oldTest oldMember).2 oldActual oldSeen)
  · intro entry member
    obtain ⟨oldEntry,oldMember,rfl⟩ := List.mem_map.mp member
    obtain ⟨witness,seen⟩ := (valid.2.1 oldEntry oldMember).1
    obtain ⟨currentWitness,currentSeen,_⟩ := observes_push model rename roots oldEntry.origin witness seen
    refine ⟨⟨currentWitness,currentSeen⟩,?_⟩
    intro actual seen
    obtain ⟨oldActual,oldSeen,same⟩ := observes_pull model rename roots oldEntry.origin actual seen
    have oldMeaning := variable_equivalent declaration oldCapture model oldEntry.name oldEntry.mode
      actual oldActual same ((valid.2.1 oldEntry oldMember).2 oldActual oldSeen)
    change VariableHolds declaration currentCapture model oldEntry.name oldEntry.mode actual
    unfold VariableHolds at oldMeaning ⊢
    by_cases output : oldEntry.name ∈ declaration.outputNames
    · simp only [output,ite_true] at oldMeaning ⊢
      exact equivalent_trans _ _ _ oldMeaning (equivalent_symm _ _ (outputs _ output))
    · simp only [output,ite_false,actualOnly oldEntry oldMember] at oldMeaning ⊢
      exact inputs _ output actual oldMeaning
  · intro first one last two same firstActual lastActual a b oneSeen twoSeen
    obtain ⟨oldFirst,hFirst,rfl⟩ := List.mem_map.mp one
    obtain ⟨oldLast,hLast,rfl⟩ := List.mem_map.mp two
    obtain ⟨oldA,seenA,eqA⟩ := observes_pull model rename roots oldFirst.origin a oneSeen
    obtain ⟨oldB,seenB,eqB⟩ := observes_pull model rename roots oldLast.origin b twoSeen
    exact equivalent_trans _ _ _ eqA (equivalent_trans _ _ _
      (valid.2.2.1 oldFirst hFirst oldLast hLast same firstActual lastActual oldA oldB seenA seenB)
      (equivalent_symm _ _ eqB))
  · intro entry member captured present same actual origin known a b seen observed
    obtain ⟨oldEntry,oldMember,rfl⟩ := List.mem_map.mp member
    obtain ⟨old,oldMember',names,oldOrigin,oldKnown,originEq⟩ := origins captured present origin known
    obtain ⟨oldA,seenA,eqA⟩ := observes_pull model rename roots oldEntry.origin a seen
    rw [originEq] at observed
    obtain ⟨oldB,seenB,eqB⟩ := observes_pull model rename roots oldOrigin b observed
    exact equivalent_trans _ _ _ eqA (equivalent_trans _ _ _
      (valid.2.2.2 oldEntry oldMember old oldMember' (same.trans names.symm) actual
        oldOrigin oldKnown oldA oldB seenA seenB) (equivalent_symm _ _ eqB))
end Yulang.GeneralDictionaryActualSchemaOrigin
