import Yulang.GeneralDictionaryObservedFiniteRequests

/-! Recover finite scalar/nominal observations from successful actual inspection.
The restriction to closed queries and point descriptor arguments is explicit;
no semantic Evidence or desired observation certificate is assumed. -/
namespace Yulang.GeneralDictionary171InspectionObservation
open GeneralNominalInspection (Query)
open GeneralNominalRecursiveInspection
open GeneralDictionaryObservedFiniteRequests

inductive Closed : Query → Prop
  | scalar (base) : Closed (.scalar base)
  | nominal (name : Nat) (queries : List Query)
      (closed : ∀ query ∈ queries, Closed query) : Closed (.nominal name queries)

/-- Every present descriptor has only point type arguments. This is a
representation restriction, not inferred from semantic equality of endpoints. -/
def PointDescriptors (state : GeneralNominalState.State) : Prop :=
  ∀ slot descriptor, state.nominals slot = some descriptor →
    ∃ n, ∃ slots : Fin n → Fin state.base.slots,
      descriptor.arguments = List.ofFn fun i => .type (slots i, slots i)

private theorem finished_visit (bounds) (origin) (test) (report : Report state) :
    Finished (report.visit bounds origin test) ↔ Finished report := Iff.rfl

private theorem finished_append (first last : Report state) :
    Finished (first.append last) ↔ Finished first ∧ Finished last := by
  simp only [Finished, Report.append, List.append_eq_nil_iff]
  constructor
  · rintro ⟨⟨a,b⟩,⟨c,d⟩,e,f⟩; exact ⟨⟨a,c,e⟩,b,d,f⟩
  · rintro ⟨⟨a,c,e⟩,b,d,f⟩; exact ⟨⟨a,b⟩,⟨c,d⟩,e,f⟩

private theorem many_length (state : GeneralNominalState.State)
    (queries : List Query) (bounds : List (GeneralNominalInspection.Bounds state)) (origins : Nat → Option Origin) (index : Nat)
    (finished : Finished (inspectMany state queries bounds origins index)) :
    queries.length = bounds.length := by
  induction queries generalizing bounds index with
  | nil => cases bounds with
    | nil => rfl
    | cons b bs => simp [inspectMany,Finished] at finished
  | cons q qs ih => cases bounds with
    | nil => simp [inspectMany,Finished] at finished
    | cons b bs =>
      rw [inspectMany] at finished
      have rest := (finished_append _ _).mp (show Finished ((inspect state q b (origins index)).append (inspectMany state qs bs origins (index+1))) by exact finished)
      simpa using ih bs (index+1) rest.2

private theorem many_item (state : GeneralNominalState.State)
    (queries : List Query) (bounds : List (GeneralNominalInspection.Bounds state)) (origins : Nat → Option Origin) (index : Nat)
    (finished : Finished (inspectMany state queries bounds origins index))
    {i : Nat} {query : Query} {bound : GeneralNominalInspection.Bounds state}
    (qt : queries[i]? = some query) (bt : bounds[i]? = some bound) :
    Finished (inspect state query bound (origins (index+i))) := by
  induction queries generalizing bounds index i with
  | nil => simp at qt
  | cons q qs ih =>
    cases bounds with
    | nil => simp at bt
    | cons b bs =>
      rw [inspectMany] at finished
      have both := (finished_append _ _).mp (show Finished ((inspect state q b (origins index)).append (inspectMany state qs bs origins (index+1))) by exact finished)
      cases i with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at qt bt; subst query; subst bound; simpa using both.1
      | succ i =>
        have result := ih bs (index+1) both.2 qt bt
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using result

/-- Successful inspection supplies actual current scalar heads or ordered
nominal descriptors recursively. The conclusion retains the original slot. -/
theorem inspected_tree (state : GeneralNominalState.State) (points : PointDescriptors state)
    (query : Query) (closed : Closed query) (slot : Fin state.base.slots) (origin)
    (finished : Finished (inspect state query (slot,slot) origin)) :
    Nonempty (Tree state slot query) := by
  induction closed generalizing slot origin with
  | scalar base =>
    simp only [inspect, finished_visit] at finished
    split at finished
    · simp [Finished] at finished
    · rename_i absent
      split at finished
      · rename_i actual head
        split at finished
        · rename_i equal
          subst actual
          exact ⟨.scalar slot base head⟩
        · simp [Finished] at finished
      · simp [Finished] at finished
      · simp [Finished,block] at finished
  | nominal name queries closed ih =>
    simp only [inspect] at finished
    split at finished
    · split at finished <;> simp [Finished,block,Report.visit] at finished
    · rename_i descriptor recorded
      split at finished
      · rename_i equal
        obtain ⟨n,slots,parameters⟩ := points slot descriptor recorded
        have arguments := GeneralNominalLinearCaptureFacts.typeArguments_exact (fun i => (slots i, slots i))
        rw [parameters, arguments] at finished
        simp only [↓reduceIte] at finished
        have len := many_length state queries (List.ofFn fun i => (slots i,slots i)) _ _ finished
        have length : queries.length = n := by simpa using len
        let qs : Fin n → Query := fun i => queries[i.val]'(by omega)
        have same : List.ofFn qs = queries := by
          apply List.ext_getElem
          · simp [length]
          · intro i hi hj
            simp [qs]
        refine ⟨?_⟩
        rw [← equal, ← same]
        apply Tree.nominal slot descriptor recorded slots qs parameters
        intro i
        apply Classical.choice
        apply ih (qs i) (by simp [qs, List.getElem_mem]) (slots i)
        apply many_item state queries (List.ofFn fun i => (slots i,slots i)) _ 0 finished (i := i.val)
        · simp [qs, show i.val < queries.length by omega]
        · simp [i.isLt]
      · simp [Finished,Report.visit] at finished

/-- Each actual request is tied to its physical slot by source identity. Its
normalized translated query is inspected, rather than supplied as a Tree. -/
theorem observed_requests (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation)
    (points : PointDescriptors state) (requests : List GeneralNominalMaterialization.Request)
    (tested : ∀ request ∈ requests, ∃ slot : Fin state.base.slots,
      request.target = state.base.source slot ∧
      Closed (GeneralNominalInspection.translate state.constructors interpretation
        (GeneralDeclarationPatterns.normalize request.pattern)) ∧
      Finished (inspect state (GeneralNominalInspection.translate state.constructors interpretation
        (GeneralDeclarationPatterns.normalize request.pattern)) (slot,slot)
        (some (.source request.target)))) : Observed state interpretation requests := by
  intro request member
  obtain ⟨slot,target,closed,finished⟩ := tested request member
  exact ⟨slot,target,inspected_tree state points _ closed slot _ finished⟩

/-- Being finished alone is insufficient: variable queries intentionally capture
instead of checking a finite closed output. -/
theorem variables_finished (state : GeneralNominalState.State) (names : List Nat)
    (slot : Fin state.base.slots) (origin : Option Origin) :
    Finished (inspect state (.variables names) (slot,slot) origin) := by
  simp [inspect,Finished]

theorem no_variables_tree (state : GeneralNominalState.State) (slot : Fin state.base.slots)
    (names : List Nat) : ¬ Nonempty (Tree state slot (.variables names)) := by
  rintro ⟨tree⟩
  cases tree

end Yulang.GeneralDictionary171InspectionObservation
