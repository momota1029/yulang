import Yulang.GeneralDictionary171InspectionObservation

/-! Local point obligations only at physical slots actually inspected. No
point restriction on unrelated descriptors is needed. -/
namespace Yulang.GeneralDictionary171LocalInspectionObservation
open GeneralNominalInspection (Query)
open GeneralNominalRecursiveInspection
open GeneralDictionaryObservedFiniteRequests
open GeneralDictionary171InspectionObservation (Closed)

/-- Only lower slots of actual inspected bounds need point descriptors. -/
def PointInspection (state : GeneralNominalState.State) (report : Report state) : Prop :=
  ∀ bound ∈ report.inspected, ∀ descriptor, state.nominals bound.1 = some descriptor →
    ∃ n, ∃ slots : Fin n → Fin state.base.slots,
      descriptor.arguments = List.ofFn fun i => .type (slots i,slots i)

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

private theorem many_inspected (state : GeneralNominalState.State)
    (queries : List Query) (bounds : List (GeneralNominalInspection.Bounds state))
    (origins : Nat → Option Origin) (index : Nat)
    {i : Nat} {query : Query} {bound : GeneralNominalInspection.Bounds state}
    (qt : queries[i]? = some query) (bt : bounds[i]? = some bound)
    (other) (member : other ∈ (inspect state query bound (origins (index+i))).inspected) :
    other ∈ (inspectMany state queries bounds origins index).inspected := by
  induction queries generalizing bounds index i with
  | nil => simp at qt
  | cons q qs ih =>
    cases bounds with
    | nil => simp at bt
    | cons b bs =>
      rw [inspectMany]
      simp only [Report.append, List.mem_append]
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero,Option.some.injEq] at qt bt
        subst query; subst bound
        exact Or.inl (by simpa using member)
      | succ i =>
        exact Or.inr (ih bs (index+1) qt bt (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using member))

/-- Successful inspection supplies actual current scalar heads or ordered
nominal descriptors recursively. The conclusion retains the original slot. -/
theorem inspected_tree (state : GeneralNominalState.State)
    (query : Query) (closed : Closed query) (slot : Fin state.base.slots) (origin)
    (finished : Finished (inspect state query (slot,slot) origin))
    (points : PointInspection state (inspect state query (slot,slot) origin)) :
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
        have rootMember : (slot,slot) ∈ (inspect state (.nominal name queries) (slot,slot) origin).inspected := by
          simp [inspect,recorded,equal,Report.visit]
        obtain ⟨n,slots,parameters⟩ := points (slot,slot) rootMember descriptor recorded
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
        · apply many_item state queries (List.ofFn fun i => (slots i,slots i)) _ 0 finished (i := i.val) (query := qs i) (bound := (slots i,slots i))
          · simp [qs, show i.val < queries.length by omega]
          · simp [i.isLt]
        · intro other member desc present
          apply points other _ desc present
          simp only [inspect,recorded,equal,↓reduceIte,parameters,arguments,Report.visit,List.mem_cons]
          right
          apply many_inspected state queries (List.ofFn fun i => (slots i,slots i)) _ 0 (i := i.val) (query := qs i) (bound := (slots i,slots i))
          · simp [qs, show i.val < queries.length by omega]
          · simp [i.isLt]
          · exact member
      · simp [Finished,Report.visit] at finished


/-- Unrelated descriptors may be interval-valued or contain row parameters.
Only descriptors visited by each successful request inspection are restricted. -/
theorem observed_requests (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation)
    (requests : List GeneralNominalMaterialization.Request)
    (tested : ∀ request ∈ requests, ∃ slot : Fin state.base.slots,
      request.target = state.base.source slot ∧
      Closed (GeneralNominalInspection.translate state.constructors interpretation
        (GeneralDeclarationPatterns.normalize request.pattern)) ∧
      Finished (inspect state (GeneralNominalInspection.translate state.constructors interpretation
        (GeneralDeclarationPatterns.normalize request.pattern)) (slot,slot)
        (some (.source request.target))) ∧
      PointInspection state (inspect state (GeneralNominalInspection.translate state.constructors interpretation
        (GeneralDeclarationPatterns.normalize request.pattern)) (slot,slot)
        (some (.source request.target)))) : Observed state interpretation requests := by
  intro request member
  obtain ⟨slot,target,closed,finished,points⟩ := tested request member
  exact ⟨slot,target,inspected_tree state _ closed slot _ finished points⟩

/-- The earlier global point hypothesis is sufficient, but not required. -/
theorem of_global (state : GeneralNominalState.State)
    (points : GeneralDictionary171InspectionObservation.PointDescriptors state)
    (report : Report state) : PointInspection state report := by
  intro bound _ descriptor recorded
  exact points bound.1 descriptor recorded

end Yulang.GeneralDictionary171LocalInspectionObservation
