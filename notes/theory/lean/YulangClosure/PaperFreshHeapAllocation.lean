import YulangClosure.PaperTermSubstitution

/-! R29: a finite allocation auxiliary for the represented paper judgments.
The input order is explicitly de Bruijn order, with the head at index zero.
Payload typing below is not the paper heap judgment. Guardedness, source order,
source/native correspondence and the full rec preservation theorem remain OPEN.
-/
namespace YulangClosure.PaperTypes.FreshHeap

abbrev Block := List (Nat × Ty × Value)
abbrev Heap := List (Nat × Value)

def formals (b : Block) : GraphEnvironment := b.map fun e => (e.1, e.2.1)
def rhs (b : Block) : List Value := b.map fun e => e.2.2
def ids (b : Block) : List Nat := b.map Prod.fst

def lookupHeap : Heap → Nat → Option Value
  | [], _ => none
  | (r,v) :: rest, q => if r = q then some v else lookupHeap rest q

/-- Every entry, including any shadowed entry, has a type in the graph. -/
def HeapPayloadTyped (d : DeclarationTable) (g : GraphEnvironment)
    (gamma : TypeEnvironment) (h : Heap) : Prop :=
  ∀ r v, (r,v) ∈ h → ∃ a, lookupGraphEnvironment g r = some a ∧
    PaperValueTyped d g gamma v a

def BlockTyped (d : DeclarationTable) (g : GraphEnvironment)
    (gamma : TypeEnvironment) (b : Block) : Prop :=
  ∀ r a v, (r,a,v) ∈ b → PaperValueTyped d g ((formals b).map Prod.snd ++ gamma) v a

/-- No independent result vector or zip: each result retains its source identity. -/
def nodes (b : Block) (rho : Nat → Value) : Heap :=
  b.map fun e => (e.1, replaceTermValue (graphFormalReplacements (formals b) rho) e.2.2)

def allocate (b : Block) (rho : Nat → Value) (h : Heap) : Heap := nodes b rho ++ h

private theorem graph_skip (front old : GraphEnvironment) (q : Nat)
    (absent : q ∉ front.map Prod.fst) :
    lookupGraphEnvironment (front ++ old) q = lookupGraphEnvironment old q := by
  induction front with
  | nil => rfl
  | cons e rest ih =>
      rcases e with ⟨r,a⟩
      have neq : r ≠ q := by intro eq; subst q; exact absent (by simp)
      have tail : q ∉ rest.map Prod.fst := by intro hm; exact absent (by simp [hm])
      simpa only [List.cons_append, lookupGraphEnvironment, neq, ite_false] using ih tail

private theorem graph_member (front old : GraphEnvironment)
    (unique : (front.map Prod.fst).Nodup) {r : Nat} {a : Ty}
    (member : (r,a) ∈ front) : lookupGraphEnvironment (front ++ old) r = some a := by
  induction front with
  | nil => cases member
  | cons e rest ih =>
      rcases e with ⟨s,t⟩
      have hu := List.nodup_cons.mp unique
      rcases List.mem_cons.mp member with eq | hm
      · cases eq; simp [lookupGraphEnvironment]
      · have neq : s ≠ r := by
          intro eq; subst r
          exact hu.1 (List.mem_map.mpr ⟨(s,a),hm,rfl⟩)
        simpa only [List.cons_append, lookupGraphEnvironment, neq, ite_false] using ih hu.2 hm

theorem graph_old_lookup (b : Block) (old : GraphEnvironment)
    (fresh : ∀ r, r ∈ ids b → r ∉ old.map Prod.fst) :
    GraphLookupPreserved old (formals b ++ old) := by
  intro q a hq
  have oldMem := lookupGraphEnvironment_identity_mem hq
  have absent : q ∉ (formals b).map Prod.fst := by
    intro hm
    have hm' : q ∈ ids b := by simpa [formals, ids, List.map_map, Function.comp_def] using hm
    exact fresh q hm' oldMem
  rw [graph_skip _ _ _ absent]
  exact hq

theorem graph_new_lookup (b : Block) (old : GraphEnvironment)
    (unique : (ids b).Nodup) {r : Nat} {a : Ty}
    (member : (r,a) ∈ formals b) :
    lookupGraphEnvironment (formals b ++ old) r = some a := by
  apply graph_member _ _ _ member
  simpa [formals, ids, List.map_map, Function.comp_def] using unique

theorem rhs_values_typed {d g gamma b} (hb : BlockTyped d g gamma b) :
    ValuesTyped d g ((formals b).map Prod.snd ++ gamma) (rhs b) ((formals b).map Prod.snd) := by
  have aux : ∀ (xs : Block),
      (∀ r a v, (r,a,v) ∈ xs → PaperValueTyped d g ((formals b).map Prod.snd ++ gamma) v a) →
      ValuesTyped d g ((formals b).map Prod.snd ++ gamma) (rhs xs) ((formals xs).map Prod.snd) := by
    intro xs hx
    induction xs with
    | nil => exact .nil
    | cons e rest ih =>
        rcases e with ⟨r,a,v⟩
        exact .cons (hx r a v (by simp)) (ih (fun r a v hm => hx r a v (by simp [hm])))
  exact aux b hb

theorem block_substitution {d old gamma target rho b}
    (unique : (ids b).Nodup)
    (fresh : ∀ r, r ∈ ids b → r ∉ old.map Prod.fst)
    (hr : TermSubstitutionTyped d old gamma target rho)
    (hb : BlockTyped d old gamma b) :
    termSubstituteValues (graphFormalReplacements (formals b) rho) (rhs b) =
      some ((nodes b rho).map Prod.snd) ∧
    ValuesTyped d (formals b ++ old) target ((nodes b rho).map Prod.snd)
      ((formals b).map Prod.snd) := by
  have hv := rhs_values_typed hb
  have ht := graphFormalReplacements_typed (formals b) (graph_old_lookup b old fresh)
    (fun r a hm => graph_new_lookup b old unique hm) hr
  constructor
  · simp only [termSubstituteValues, hv.termSupported, ↓reduceIte]
    simp [nodes, rhs, List.map_map, Function.comp_def]
  · simpa [nodes, rhs, List.map_map, Function.comp_def] using (hv.graphWeaken (graph_old_lookup b old fresh)).termReplace ht

theorem each_rhs_substitution {d old gamma target rho b}
    (unique : (ids b).Nodup)
    (fresh : ∀ r, r ∈ ids b → r ∉ old.map Prod.fst)
    (hr : TermSubstitutionTyped d old gamma target rho)
    (hb : BlockTyped d old gamma b) {r a v} (hm : (r,a,v) ∈ b) :
    termSubstituteValue (graphFormalReplacements (formals b) rho) v =
      some (replaceTermValue (graphFormalReplacements (formals b) rho) v) ∧
    PaperValueTyped d (formals b ++ old) target
      (replaceTermValue (graphFormalReplacements (formals b) rho) v) a := by
  have hv := hb r a v hm
  have ht := graphFormalReplacements_typed (formals b) (graph_old_lookup b old fresh)
    (fun r a hm => graph_new_lookup b old unique hm) hr
  exact ⟨termSubstituteValue_success hv.termSupported,
    (hv.graphWeaken (graph_old_lookup b old fresh)).termReplace ht⟩

theorem nodes_length (b : Block) (rho : Nat → Value) : (nodes b rho).length = b.length := by
  simp [nodes]

theorem exact_front_suffix (b : Block) (rho : Nat → Value) (h : Heap) :
    allocate b rho h = nodes b rho ++ h := rfl

private theorem heap_member (front old : Heap)
    (unique : (front.map Prod.fst).Nodup) {r : Nat} {v : Value}
    (member : (r,v) ∈ front) : lookupHeap (front ++ old) r = some v := by
  induction front with
  | nil => cases member
  | cons e rest ih =>
      rcases e with ⟨s,t⟩
      have hu := List.nodup_cons.mp unique
      rcases List.mem_cons.mp member with eq | hm
      · cases eq; simp [lookupHeap]
      · have neq : s ≠ r := by
          intro eq; subst r
          exact hu.1 (List.mem_map.mpr ⟨(s,v),hm,rfl⟩)
        simpa only [List.cons_append, lookupHeap, neq, ite_false] using ih hu.2 hm

private theorem heap_skip (front old : Heap) (q : Nat)
    (absent : q ∉ front.map Prod.fst) : lookupHeap (front ++ old) q = lookupHeap old q := by
  induction front with
  | nil => rfl
  | cons e rest ih =>
      rcases e with ⟨r,v⟩
      have neq : r ≠ q := by intro eq; subst q; exact absent (by simp)
      have tail : q ∉ rest.map Prod.fst := by intro hm; exact absent (by simp [hm])
      simpa only [List.cons_append, lookupHeap, neq, ite_false] using ih tail

private theorem heap_lookup_mem {h : Heap} {r : Nat} {v : Value}
    (hv : lookupHeap h r = some v) : r ∈ h.map Prod.fst := by
  induction h with
  | nil => cases hv
  | cons e rest ih =>
      rcases e with ⟨s,w⟩
      by_cases eq : s = r
      · subst r; simp
      · exact List.mem_cons_of_mem _ (ih (by simpa [lookupHeap, eq] using hv))

theorem heap_new_lookup (b : Block) (rho : Nat → Value) (h : Heap)
    (unique : (ids b).Nodup) {r a v} (hm : (r,a,v) ∈ b) :
    lookupHeap (allocate b rho h) r =
      some (replaceTermValue (graphFormalReplacements (formals b) rho) v) := by
  apply heap_member
  · simpa [nodes, ids, List.map_map, Function.comp_def] using unique
  · exact List.mem_map_of_mem hm

theorem heap_unallocated_lookup (b : Block) (rho : Nat → Value) (h : Heap)
    (q : Nat) (absent : q ∉ ids b) :
    lookupHeap (allocate b rho h) q = lookupHeap h q := by
  apply heap_skip
  simpa [nodes, ids, List.map_map, Function.comp_def] using absent

/-- Old successful lookups remain identical; fresh queries intentionally acquire new nodes. -/
theorem heap_old_success (b : Block) (rho : Nat → Value) (h : Heap)
    (fresh : ∀ r, r ∈ ids b → r ∉ h.map Prod.fst) {q : Nat} {v : Value}
    (hq : lookupHeap h q = some v) : lookupHeap (allocate b rho h) q = some v := by
  have absent : q ∉ (nodes b rho).map Prod.fst := by
    intro hm
    exact fresh q (by simpa [nodes, ids, List.map_map, Function.comp_def] using hm) (heap_lookup_mem hq)
  rw [allocate, heap_skip _ _ _ absent, hq]

theorem old_payload_transport {d old new gamma h}
    (hp : GraphLookupPreserved old new) (hh : HeapPayloadTyped d old gamma h) :
    HeapPayloadTyped d new gamma h := by
  intro r v hm
  obtain ⟨a,ha,hv⟩ := hh r v hm
  exact ⟨a,hp r a ha,hv.graphWeaken hp⟩

theorem allocation_payload_typed {d old gamma target rho b h}
    (unique : (ids b).Nodup)
    (freshGraph : ∀ r, r ∈ ids b → r ∉ old.map Prod.fst)
    (hr : TermSubstitutionTyped d old gamma target rho)
    (hb : BlockTyped d old gamma b) (hh : HeapPayloadTyped d old target h) :
    HeapPayloadTyped d (formals b ++ old) target (allocate b rho h) := by
  intro r w hm
  change (r,w) ∈ nodes b rho ++ h at hm
  rcases List.mem_append.mp hm with hn | ho
  · unfold nodes at hn
    obtain ⟨⟨s,a,v⟩,hsource,he⟩ := List.mem_map.mp hn
    cases he
    exact ⟨a,graph_new_lookup b old unique (List.mem_map_of_mem hsource),
      (each_rhs_substitution unique freshGraph hr hb hsource).2⟩
  · exact old_payload_transport (graph_old_lookup b old freshGraph) hh r w ho

/-- Application to the payload/allocation component of the original rec obligation.
The input block is already in de Bruijn order. No source order or guard follows. -/
theorem finite_allocation {d old gamma target rho b h}
    (unique : (ids b).Nodup)
    (freshGraph : ∀ r, r ∈ ids b → r ∉ old.map Prod.fst)
    (freshHeap : ∀ r, r ∈ ids b → r ∉ h.map Prod.fst)
    (hr : TermSubstitutionTyped d old gamma target rho)
    (hb : BlockTyped d old gamma b) (hh : HeapPayloadTyped d old target h) :
    GraphLookupPreserved old (formals b ++ old) ∧
    (∀ r a, (r,a) ∈ formals b → lookupGraphEnvironment (formals b ++ old) r = some a) ∧
    (termSubstituteValues (graphFormalReplacements (formals b) rho) (rhs b) =
      some ((nodes b rho).map Prod.snd)) ∧
    (nodes b rho).length = b.length ∧
    allocate b rho h = nodes b rho ++ h ∧
    (∀ r a v, (r,a,v) ∈ b → lookupHeap (allocate b rho h) r =
      some (replaceTermValue (graphFormalReplacements (formals b) rho) v)) ∧
    (∀ q v, lookupHeap h q = some v → lookupHeap (allocate b rho h) q = some v) ∧
    HeapPayloadTyped d (formals b ++ old) target (allocate b rho h) := by
  exact ⟨graph_old_lookup b old freshGraph,
    fun r a hm => graph_new_lookup b old unique hm,
    (block_substitution unique freshGraph hr hb).1,
    nodes_length b rho, rfl,
    fun r a v hm => heap_new_lookup b rho h unique hm,
    fun q v hq => heap_old_success b rho h freshHeap hq,
    allocation_payload_typed unique freshGraph hr hb hh⟩

/-- Duplicate IDs with different types invalidate the later formal lookup. -/
theorem duplicate_graph_falsifier :
    lookupGraphEnvironment (formals [(7,.base .int,.variable 0),(7,.base .bool,.variable 1)]) 7 =
      some (.base .int) ∧
    lookupGraphEnvironment (formals [(7,.base .int,.variable 0),(7,.base .bool,.variable 1)]) 7 ≠
      some (.base .bool) := by simp [formals,lookupGraphEnvironment]

theorem old_collision_falsifier :
    lookupHeap ([(7,.graphReference 8)] ++ [(7,.graphReference 9)]) 7 ≠
      lookupHeap [(7,.graphReference 9)] 7 := by simp [lookupHeap]

theorem zip_truncation_falsifier :
    (List.zip [10,20] ([Value.graphReference 10])).length = 1 ∧
      (List.zip [10,20] ([Value.graphReference 10])).length ≠ ([10,20] : List Nat).length := by
  decide

theorem two_formal_order :
    nodes [(10,.base .int,.variable 0),(20,.base .bool,.variable 1)] Value.variable =
      [(10,.graphReference 10),(20,.graphReference 20)] ∧
    nodes [(20,.base .bool,.variable 0),(10,.base .int,.variable 1)] Value.variable =
      [(20,.graphReference 20),(10,.graphReference 10)] ∧
    ([(10,.graphReference 10),(20,.graphReference 20)] : Heap) ≠
      [(20,.graphReference 20),(10,.graphReference 10)] := by
  simp [nodes,formals,graphFormalReplacements,replaceTermValue]

theorem swapped_replacements_heap :
    ([(10,replaceTermValue (graphFormalReplacements [(10,.base .int),(20,.base .bool)] Value.variable)
          (.variable 0)),
      (20,replaceTermValue (graphFormalReplacements [(10,.base .int),(20,.base .bool)] Value.variable)
          (.variable 1))] : Heap) ≠
    [(10,replaceTermValue (graphFormalReplacements [(20,.base .bool),(10,.base .int)] Value.variable)
          (.variable 0)),
      (20,replaceTermValue (graphFormalReplacements [(20,.base .bool),(10,.base .int)] Value.variable)
          (.variable 1))] := by
  simp [graphFormalReplacements, replaceTermValue]

/-- Sequential substitution changes the actual allocated payloads. -/
theorem sequential_heap_falsifier :
    ([(10,replaceTermValue (fun n => if n = 1 then .variable 0 else .variable n)
      (replaceTermValue (fun n => if n = 0 then .variable 1 else .variable n)
        (.tuple [.variable 0,.variable 1])))] : Heap) =
      [(10,.tuple [.variable 0,.variable 0])] ∧
    ([(10,.tuple [.variable 0,.variable 0])] : Heap) ≠
      [(10,.tuple [.variable 1,.variable 0])] := by simp [replaceTermValue]

/-- Payload typing admits a self edge; the paper guard premise remains OPEN. -/
theorem self_alias_payload (d : DeclarationTable) (gamma : TypeEnvironment) (r : Nat) (a : Ty) :
    HeapPayloadTyped d [(r,a)] gamma [(r,.graphReference r)] ∧
    lookupHeap [(r,.graphReference r)] r = some (.graphReference r) := by
  constructor
  · intro s v hm
    have he : (s,v) = (r,Value.graphReference r) := by simpa using hm
    cases he
    exact ⟨a,by simp [lookupGraphEnvironment],.graphReference (by simp [lookupGraphEnvironment])⟩
  · simp [lookupHeap]

theorem self_alias_block (d : DeclarationTable) (gamma : TypeEnvironment) (r : Nat) (a : Ty) :
    nodes [(r,a,.variable 0)] Value.variable = [(r,.graphReference r)] ∧
    HeapPayloadTyped d (formals [(r,a,.variable 0)]) gamma
      (allocate [(r,a,.variable 0)] Value.variable []) ∧
    lookupHeap (allocate [(r,a,.variable 0)] Value.variable []) r = some (.graphReference r) := by
  have hn : nodes [(r,a,.variable 0)] Value.variable = [(r,.graphReference r)] := by
    simp [nodes, formals, replaceTermValue, graphFormalReplacements]
  refine ⟨hn, ?_⟩
  simpa only [allocate, hn, List.append_nil, formals, List.map_cons, List.map_nil] using
    self_alias_payload d gamma r a

end YulangClosure.PaperTypes.FreshHeap
