import YulangClosure.SimpleSubLatticeGrowingInference

/-!
Construct a finite shared row interpretation from syntactically saturated
finite structural constraints. This is a component of native correspondence,
not a replacement for original source typing or the complete native semantics.

Source references are rows first, followed by structural heads, separately for
each kind. A row denotes the join of its retained structural lower roots.
Finite join/meet suffixes are allocated explicitly; there are no alias nodes.
All structural ports use the SAME reference map, including negative ports.
-/
namespace YulangClosure.SimpleSub.NativeRowModel
open Regular (Comparison Reference lookupList renameNode renamePair NodeRel)
open Lattice

structure System where
  rows : Kind → Nat
  heads : (k : Kind) → List (Regular.Node k)
  clauses : List Comparison

def System.head (s : System) (k : Kind) (h : Nat) : Nat := s.rows k + h

def System.lower (s : System) (k : Kind) (r : Nat) : List Nat :=
  (List.range (s.heads k).length).filter (fun h => ⟨k,s.head k h,r⟩ ∈ s.clauses)

def System.upper (s : System) (k : Kind) (r : Nat) : List Nat :=
  (List.range (s.heads k).length).filter (fun h => ⟨k,r,s.head k h⟩ ∈ s.clauses)

@[simp] theorem lower_mem {s : System} {k r h} : h ∈ s.lower k r ↔
    h < (s.heads k).length ∧ ⟨k,s.head k h,r⟩ ∈ s.clauses := by
  simp [System.lower]

@[simp] theorem upper_mem {s : System} {k r h} : h ∈ s.upper k r ↔
    h < (s.heads k).length ∧ ⟨k,r,s.head k h⟩ ∈ s.clauses := by
  simp [System.upper]

/-- Independent finite syntax conditions, containing no semantic relation,
graph, certificate acceptance, or chosen variable valuation. -/
structure Saturated (s : System) : Prop where
  bounded : ∀ p, p ∈ s.clauses →
    p.lower < s.rows p.kind + (s.heads p.kind).length ∧
    p.upper < s.rows p.kind + (s.heads p.kind).length
  formed : ∀ k node, node ∈ s.heads k → node.uniqueLabels ∧
    ∀ ref, ref ∈ node.references →
      ref.identity < s.rows ref.kind + (s.heads ref.kind).length
  rowRow : ∀ k x y, x < s.rows k → y < s.rows k →
    ⟨k,x,y⟩ ∈ s.clauses → ∀ h, h ∈ s.lower k x → h ∈ s.lower k y
  rowHead : ∀ k x u, x < s.rows k →
    ⟨k,x,s.head k u⟩ ∈ s.clauses → ∀ h, h ∈ s.lower k x →
      ⟨k,s.head k h,s.head k u⟩ ∈ s.clauses
  headHead : ∀ k h u a b,
    lookupList (s.heads k) h = some a → lookupList (s.heads k) u = some b →
    ⟨k,s.head k h,s.head k u⟩ ∈ s.clauses →
      NodeRel (fun p => p ∈ s.clauses) a b

def suffixes {α : Type} : List α → List (List α)
  | [] => [[]]
  | a :: rest => (a :: rest) :: suffixes rest

theorem self_suffix {α : Type} (xs : List α) : xs ∈ suffixes xs := by
  cases xs <;> simp [suffixes]

theorem suffix_tail {α : Type} {xs tail : List α} {a : α}
    (h : a :: tail ∈ suffixes xs) : tail ∈ suffixes xs := by
  induction xs with
  | nil => simp [suffixes] at h
  | cons b rest ih =>
      rcases List.mem_cons.mp h with eq | h
      · cases eq; exact List.mem_cons_of_mem _ (self_suffix _)
      · exact List.mem_cons_of_mem _ (ih h)

theorem suffix_subset {α : Type} {xs tail : List α} (h : tail ∈ suffixes xs) :
    ∀ a, a ∈ tail → a ∈ xs := by
  induction xs with
  | nil => simp [suffixes] at h; subst tail; simp
  | cons b rest ih =>
      rcases List.mem_cons.mp h with eq | h
      · subst tail; exact fun _ h => h
      · exact fun a ha => List.mem_cons_of_mem _ (ih h a ha)

theorem suffix_length {α : Type} {xs tail : List α} (h : tail ∈ suffixes xs) :
    tail.length ≤ xs.length := by
  induction xs with
  | nil => simp [suffixes] at h; subst tail; exact Nat.le_refl _
  | cons b rest ih =>
      rcases List.mem_cons.mp h with eq | h
      · subst tail; exact Nat.le_refl _
      · exact Nat.le_trans (ih h) (by simp)

inductive Slot where
  | head (index : Nat)
  | lower (row : Nat) (suffix : List Nat)
  | upper (row : Nat) (suffix : List Nat)
  deriving DecidableEq, Repr

def System.slots (s : System) (k : Kind) : List Slot :=
  (List.range (s.heads k).length).map Slot.head ++
  (List.range (s.rows k)).flatMap (fun r =>
    (suffixes (s.lower k r)).map (Slot.lower r) ++
    (suffixes (s.upper k r)).map (Slot.upper r))

def System.index (s : System) (k : Kind) (slot : Slot) : Nat :=
  (s.slots k).idxOf slot

def System.names (s : System) (k : Kind) (i : Nat) : Nat :=
  if i < s.rows k then s.index k (.lower i (s.lower k i))
  else s.index k (.head (i - s.rows k))

def System.emit (s : System) (k : Kind) : Slot → Node k
  | .head h => .structural (renameNode s.names ((lookupList (s.heads k) h).getD .bottom))
  | .lower _ [] => .structural .bottom
  | .lower r (h :: tail) => .union (s.index k (.head h)) (s.index k (.lower r tail))
  | .upper _ [] => .structural .top
  | .upper r (h :: tail) => .intersection (s.index k (.head h)) (s.index k (.upper r tail))

def System.graph (s : System) : Graph := fun k => (s.slots k).map (s.emit k)

theorem slot_head {s : System} {k h} (bound : h < (s.heads k).length) :
    Slot.head h ∈ s.slots k := by
  simp [System.slots,bound]

theorem slot_lower {s : System} {k r xs} (bound : r < s.rows k)
    (tail : xs ∈ suffixes (s.lower k r)) : Slot.lower r xs ∈ s.slots k := by
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨r,List.mem_range.mpr bound,
    List.mem_append_left _ (List.mem_map.mpr ⟨xs,tail,rfl⟩)⟩

theorem slot_upper {s : System} {k r xs} (bound : r < s.rows k)
    (tail : xs ∈ suffixes (s.upper k r)) : Slot.upper r xs ∈ s.slots k := by
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨r,List.mem_range.mpr bound,
    List.mem_append_right _ (List.mem_map.mpr ⟨xs,tail,rfl⟩)⟩

theorem lookup_idxOf {α β : Type} [DecidableEq α] (xs : List α) (f : α → β)
    (a : α) (member : a ∈ xs) : lookupList (xs.map f) (xs.idxOf a) = some (f a) := by
  induction xs with
  | nil => cases member
  | cons b rest ih =>
      by_cases same : b = a
      · subst b; simp [lookupList]
      · have tail : a ∈ rest := (List.mem_cons.mp member).resolve_left (Ne.symm same)
        simpa [List.idxOf_cons,same,lookupList] using ih tail

theorem lookup_slot {s : System} {k slot} (member : slot ∈ s.slots k) :
    s.graph.lookup k (s.index k slot) = some (s.emit k slot) :=
  lookup_idxOf _ _ _ member

theorem lookup_head {s : System} {k h node} (found : lookupList (s.heads k) h = some node) :
    s.graph.lookup k (s.index k (.head h)) = some (.structural (renameNode s.names node)) := by
  have h := lookup_slot (slot_head (LatticeDecision.lookupList_index_lt found))
  simpa [System.emit,found] using h

theorem names_row {s : System} {k r} (bound : r < s.rows k) :
    s.names k r = s.index k (.lower r (s.lower k r)) := by simp [System.names,bound]

theorem names_head (s : System) (k : Kind) (h : Nat) :
    s.names k (s.head k h) = s.index k (.head h) := by
  have hn : ¬ s.rows k + h < s.rows k := by omega
  simp [System.names,System.head,hn]

theorem exists_slot {s : System} {k slot} (member : slot ∈ s.slots k) :
    Exists s.graph k (s.index k slot) := ⟨_,lookup_slot member⟩

theorem exists_name {s : System} {k i} (bound : i < s.rows k + (s.heads k).length) :
    Exists s.graph k (s.names k i) := by
  by_cases row : i < s.rows k
  · rw [names_row row]
    exact exists_slot (slot_lower row (self_suffix _))
  · have h : i - s.rows k < (s.heads k).length := by omega
    simpa [System.names,row] using exists_slot (slot_head h)

def System.relation (s : System) (pair : Comparison) : Prop :=
  ∃ p, p ∈ s.clauses ∧ pair = renamePair s.names p

theorem relation_member {s : System} {p} (member : p ∈ s.clauses) :
    s.relation (renamePair s.names p) := ⟨p,member,rfl⟩

theorem head_layer {s : System} {k h u a b} (sat : Saturated s)
    (ha : lookupList (s.heads k) h = some a)
    (hb : lookupList (s.heads k) u = some b)
    (member : ⟨k,s.head k h,s.head k u⟩ ∈ s.clauses) :
    Layer s.graph s.relation ⟨k,s.index k (.head h),s.index k (.head u)⟩ := by
  have rel := sat.headHead k h u a b ha hb member
  have mapped : NodeRel s.relation (renameNode s.names a) (renameNode s.names b) := by
    apply (Regular.nodeRel_rename s.names s.relation a b).mpr
    apply (Regular.nodeRel_iff _ _ _).mpr
    rcases (Regular.holdsExpansion_iff _ _).mp ((Regular.nodeRel_iff _ _ _).mp rel) with ⟨children,expanded,closed⟩
    exact (Regular.holdsExpansion_iff _ _).mpr ⟨children,expanded,fun p hp => relation_member (closed p hp)⟩
  rcases (Regular.holdsExpansion_iff _ _).mp ((Regular.nodeRel_iff _ _ _).mp mapped) with ⟨children,expanded,closed⟩
  exact .structural (by simpa [structuralExpand,lookup_head ha,lookup_head hb] using expanded) closed

theorem lower_inject {s : System} {k r xs h} (row : r < s.rows k)
    (tail : xs ∈ suffixes (s.lower k r)) (member : h ∈ xs) :
    Layer s.graph s.relation ⟨k,s.index k (.head h),s.index k (.lower r xs)⟩ := by
  induction xs with
  | nil => cases member
  | cons a rest ih =>
      have found : unionAt s.graph k (s.index k (.lower r (a :: rest))) =
          some (s.index k (.head a),s.index k (.lower r rest)) := by
        simp [unionAt,lookup_slot (slot_lower row tail),System.emit]
      rcases List.mem_cons.mp member with eq | member
      · subst a; exact .unionLeft found
      · exact .trans (ih (suffix_tail tail) member) (.unionRight found)

theorem lower_elim {s : System} {k r xs target} (row : r < s.rows k)
    (tail : xs ∈ suffixes (s.lower k r)) (present : Exists s.graph k target)
    (each : ∀ h, h ∈ xs → Layer s.graph s.relation ⟨k,s.index k (.head h),target⟩) :
    Layer s.graph s.relation ⟨k,s.index k (.lower r xs),target⟩ := by
  induction xs with
  | nil =>
      exact .bottom (by simp [bottomAt,lookup_slot (slot_lower row tail),System.emit]) present
  | cons h rest ih =>
      apply Layer.unionElim (a := s.index k (.head h)) (b := s.index k (.lower r rest))
      · simp [unionAt,lookup_slot (slot_lower row tail),System.emit]
      · exact each h (List.mem_cons_self)
      · exact ih (suffix_tail tail) (fun h hm => each h (List.mem_cons_of_mem _ hm))

theorem postfixed {s : System} (sat : Saturated s) :
    ∀ p, s.relation p → Layer s.graph s.relation p := by
  rintro _ ⟨⟨k,x,y⟩,member,rfl⟩
  obtain ⟨xb,yb⟩ := sat.bounded _ member
  change x < s.rows k + (s.heads k).length at xb
  change y < s.rows k + (s.heads k).length at yb
  change Layer s.graph s.relation ⟨k,s.names k x,s.names k y⟩
  by_cases xr : x < s.rows k
  · rw [names_row xr]
    apply lower_elim xr (self_suffix _) (exists_name yb)
    intro h hm
    by_cases yr : y < s.rows k
    · rw [names_row yr]
      exact lower_inject yr (self_suffix _) (sat.rowRow k x y xr yr member h hm)
    · have hy : y = s.head k (y - s.rows k) := by simp [System.head]; omega
      rw [hy,names_head]
      have ylt : y - s.rows k < (s.heads k).length := by omega
      rcases lookupList_present (s.heads k) h (lower_mem.mp hm).1 with ⟨a,ha⟩
      rcases lookupList_present (s.heads k) (y - s.rows k) ylt with ⟨b,hb⟩
      exact head_layer sat ha hb (sat.rowHead k x _ xr (hy ▸ member) h hm)
  · have hx : x = s.head k (x - s.rows k) := by simp [System.head]; omega
    rw [hx,names_head]
    by_cases yr : y < s.rows k
    · rw [names_row yr]
      apply lower_inject yr (self_suffix _)
      exact lower_mem.mpr ⟨by omega,hx ▸ member⟩
    · have hy : y = s.head k (y - s.rows k) := by simp [System.head]; omega
      rw [hy,names_head]
      rcases lookupList_present (s.heads k) (x - s.rows k) (by omega) with ⟨a,ha⟩
      rcases lookupList_present (s.heads k) (y - s.rows k) (by omega) with ⟨b,hb⟩
      exact head_layer sat ha hb (hx ▸ hy ▸ member)

/-- A canonical graph and single reference map satisfy every retained bound.
No model, successful decision, or semantic consistency is an input. -/
theorem canonical_bounds {s : System} (sat : Saturated s) :
    ∀ p, p ∈ s.clauses → RegularSub s.graph (renamePair s.names p) := by
  intro p hp
  exact coinduction (postfixed sat) _ (relation_member hp)

@[simp] theorem slot_head_iff {s : System} {k h} :
    Slot.head h ∈ s.slots k ↔ h < (s.heads k).length := by simp [System.slots]

@[simp] theorem slot_lower_iff {s : System} {k r xs} :
    Slot.lower r xs ∈ s.slots k ↔ r < s.rows k ∧ xs ∈ suffixes (s.lower k r) := by
  simp [System.slots]

@[simp] theorem slot_upper_iff {s : System} {k r xs} :
    Slot.upper r xs ∈ s.slots k ↔ r < s.rows k ∧ xs ∈ suffixes (s.upper k r) := by
  simp [System.slots]

theorem rename_unique (names : Renaming) {k} (node : Regular.Node k) :
    (renameNode names node).uniqueLabels ↔ node.uniqueLabels := by
  cases node <;> simp [renameNode,Regular.Node.uniqueLabels,List.map_map,Function.comp_def]

theorem rename_references (names : Renaming) {k} (node : Regular.Node k) :
    (renameNode names node).references =
      node.references.map (fun r => ⟨r.kind,names r.kind r.identity⟩) := by
  cases node <;> simp [renameNode,Regular.Node.references,List.map_map,
    List.map_flatMap,List.flatMap_map,Function.comp_def]

theorem canonical_valid {s : System} (sat : Saturated s) : s.graph.Valid := by
  intro k node nodeMem
  change node ∈ (s.slots k).map (s.emit k) at nodeMem
  rcases List.mem_map.mp nodeMem with ⟨slot,slotMem,rfl⟩
  cases slot with
  | head h =>
      rcases lookupList_present (s.heads k) h (slot_head_iff.mp slotMem) with ⟨node,found⟩
      have formed := sat.formed k node (Regular.lookupList_mem found)
      simp only [System.emit,found,Option.getD_some,Node.uniqueLabels]
      refine ⟨(rename_unique _ _).mpr formed.1,?_⟩
      intro ref hmem
      rw [Node.references,rename_references] at hmem
      rcases List.mem_map.mp hmem with ⟨old,oldMem,rfl⟩
      exact exists_name (formed.2 old oldMem)
  | lower r xs =>
      obtain ⟨row,tail⟩ := slot_lower_iff.mp slotMem
      cases xs with
      | nil => simp [System.emit,Node.uniqueLabels,Regular.Node.uniqueLabels,Node.references,Regular.Node.references]
      | cons h rest =>
          refine ⟨True.intro,?_⟩
          intro ref hmem
          rcases (show ref = ⟨k,s.index k (.head h)⟩ ∨ ref = ⟨k,s.index k (.lower r rest)⟩ from
            by simpa [System.emit,Node.references] using hmem) with rfl | rfl
          · exact exists_slot (slot_head (lower_mem.mp (suffix_subset tail h List.mem_cons_self)).1)
          · exact exists_slot (slot_lower row (suffix_tail tail))
  | upper r xs =>
      obtain ⟨row,tail⟩ := slot_upper_iff.mp slotMem
      cases xs with
      | nil => simp [System.emit,Node.uniqueLabels,Regular.Node.uniqueLabels,Node.references,Regular.Node.references]
      | cons h rest =>
          refine ⟨True.intro,?_⟩
          intro ref hmem
          rcases (show ref = ⟨k,s.index k (.head h)⟩ ∨ ref = ⟨k,s.index k (.upper r rest)⟩ from
            by simpa [System.emit,Node.references] using hmem) with rfl | rfl
          · exact exists_slot (slot_head (upper_mem.mp (suffix_subset tail h List.mem_cons_self)).1)
          · exact exists_slot (slot_upper row (suffix_tail tail))

theorem check_head {s : System} {k h fuel} (bound : h < (s.heads k).length)
    (positive : 0 < fuel) : checkFinite s.graph fuel k (s.index k (.head h)) = true := by
  rcases lookupList_present (s.heads k) h bound with ⟨node,found⟩
  cases fuel with
  | zero => omega
  | succ fuel => simp [checkFinite,lookup_head found]

theorem check_lower {s : System} {k r xs fuel} (row : r < s.rows k)
    (tail : xs ∈ suffixes (s.lower k r)) (enough : xs.length < fuel) :
    checkFinite s.graph fuel k (s.index k (.lower r xs)) = true := by
  induction xs generalizing fuel with
  | nil =>
      cases fuel with
      | zero => omega
      | succ fuel => simp [checkFinite,lookup_slot (slot_lower row tail),System.emit]
  | cons h rest ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have head := check_head (lower_mem.mp (suffix_subset tail h List.mem_cons_self)).1 (fuel := fuel) (by simp at enough; omega)
          have rest := ih (suffix_tail tail) (fuel := fuel) (by simpa using enough)
          simp [checkFinite,lookup_slot (slot_lower row tail),System.emit,head,rest]

theorem check_upper {s : System} {k r xs fuel} (row : r < s.rows k)
    (tail : xs ∈ suffixes (s.upper k r)) (enough : xs.length < fuel) :
    checkFinite s.graph fuel k (s.index k (.upper r xs)) = true := by
  induction xs generalizing fuel with
  | nil =>
      cases fuel with
      | zero => omega
      | succ fuel => simp [checkFinite,lookup_slot (slot_upper row tail),System.emit]
  | cons h rest ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have head := check_head (upper_mem.mp (suffix_subset tail h List.mem_cons_self)).1 (fuel := fuel) (by simp at enough; omega)
          have rest := ih (suffix_tail tail) (fuel := fuel) (by simpa using enough)
          simp [checkFinite,lookup_slot (slot_upper row tail),System.emit,head,rest]

theorem lower_length (s : System) (k : Kind) (r : Nat) :
    (s.lower k r).length ≤ (s.heads k).length := by
  simpa [System.lower] using List.length_filter_le (fun h => decide (⟨k,s.head k h,r⟩ ∈ s.clauses)) (List.range (s.heads k).length)

theorem upper_length (s : System) (k : Kind) (r : Nat) :
    (s.upper k r).length ≤ (s.heads k).length := by
  simpa [System.upper] using List.length_filter_le (fun h => decide (⟨k,r,s.head k h⟩ ∈ s.clauses)) (List.range (s.heads k).length)

theorem graph_length (s : System) (k : Kind) : (s.heads k).length ≤ (s.graph k).length := by
  simp [System.graph,System.slots]

/-- Guard checking is proved for the graph actually built here. Alias cycles
never become lattice edges: only finite suffixes are traversed before a head. -/
theorem canonical_guard_checked (s : System) : checkGuarded s.graph = true := by
  let fuel := (s.graph .value).length + (s.graph .effect).length + 1
  have enough : ∀ k, (s.heads k).length < fuel := by
    intro k; have h := graph_length s k; cases k <;> dsimp [fuel] <;> omega
  have all : ∀ k i, i < (s.graph k).length → checkFinite s.graph fuel k i = true := by
    intro k i hi
    rcases lookupList_present (s.graph k) i hi with ⟨node,found⟩
    rcases List.mem_map.mp (Regular.lookupList_mem found) with ⟨slot,member,eq⟩
    have atSlot : checkFinite s.graph fuel k (s.index k slot) = true := by
      cases slot with
      | head h => exact check_head (slot_head_iff.mp member) (by have := enough k; omega)
      | lower r xs =>
          obtain ⟨row,tail⟩ := slot_lower_iff.mp member
          exact check_lower row tail (Nat.lt_of_le_of_lt (Nat.le_trans (suffix_length tail) (lower_length s k r)) (enough k))
      | upper r xs =>
          obtain ⟨row,tail⟩ := slot_upper_iff.mp member
          exact check_upper row tail (Nat.lt_of_le_of_lt (Nat.le_trans (suffix_length tail) (upper_length s k r)) (enough k))
    have same : checkFinite s.graph fuel k i = checkFinite s.graph fuel k (s.index k slot) := by
      cases fuel with
      | zero => rfl
      | succ fuel => simp only [checkFinite,show s.graph.lookup k i = some node from found,lookup_slot member,eq]
    exact same.trans atSlot
  exact Bool.and_eq_true_iff.mpr ⟨List.all_eq_true.mpr (fun i hi => all .value i (List.mem_range.mp hi)),
    List.all_eq_true.mpr (fun i hi => all .effect i (List.mem_range.mp hi))⟩

theorem canonical_guarded (s : System) : s.graph.Guarded := checkGuarded_sound (canonical_guard_checked s)

/-- Computed finite certificate acceptance follows from finite syntactic
saturation. It is a conclusion, not another model-existence premise. -/
theorem canonical_decided {s : System} (sat : Saturated s) :
    LatticeDecision.decideDemands s.graph (s.clauses.map (renamePair s.names)) = true := by
  apply (LatticeDecision.decideDemands_exact _ _).mpr
  refine ⟨canonical_valid sat,canonical_guard_checked s,?_⟩
  intro pair member
  rcases List.mem_map.mp member with ⟨p,hp,rfl⟩
  exact canonical_bounds sat p hp

/-- Apply the constructed interpretation to the original graph-indexed
history theorem. Only actual source/history correspondence remains external. -/
theorem canonical_original_history {s : System} (sat : Saturated s)
    {ref birth first events}
    (history : LatticeInference.ConstraintHistory s.graph ref birth first
      ⟨s.clauses.map (renamePair s.names),events⟩) :
    s.graph.Valid ∧ s.graph.Guarded ∧ LatticeInference.Holds s.graph first.obligations := by
  exact LatticeInference.accepted_original_demands history (canonical_decided sat)

/-- Alias-only components are interpreted as bottom, without equating
distinct positive joins and negative meets. -/
theorem empty_lower_bottom {s : System} {k r} (row : r < s.rows k)
    (empty : s.lower k r = []) :
    s.graph.lookup k (s.names k r) = some (.structural .bottom) := by
  rw [names_row row]
  have h := lookup_slot (slot_lower row (self_suffix (s.lower k r)))
  simpa [System.emit,empty] using h

theorem upper_intro {s : System} {k r xs source} (row : r < s.rows k)
    (tail : xs ∈ suffixes (s.upper k r)) (present : Exists s.graph k source)
    (each : ∀ h, h ∈ xs → Layer s.graph s.relation ⟨k,source,s.index k (.head h)⟩) :
    Layer s.graph s.relation ⟨k,source,s.index k (.upper r xs)⟩ := by
  induction xs with
  | nil =>
      exact .top (by simp [topAt,lookup_slot (slot_upper row tail),System.emit]) present
  | cons h rest ih =>
      apply Layer.intersectionIntro (a := s.index k (.head h)) (b := s.index k (.upper r rest))
      · simp [intersectionAt,lookup_slot (slot_upper row tail),System.emit]
      · exact each h List.mem_cons_self
      · exact ih (suffix_tail tail) (fun h hm => each h (List.mem_cons_of_mem _ hm))

/-- The canonical lower join lies below the separately constructed upper
meet. The two nodes are never silently identified. -/
theorem canonical_interval {s : System} (sat : Saturated s) {k r} (row : r < s.rows k) :
    RegularSub s.graph ⟨k,s.names k r,s.index k (.upper r (s.upper k r))⟩ := by
  apply regular_fold
  apply Layer.mono (coinduction (postfixed sat))
  apply upper_intro row (self_suffix _) (exists_name (Nat.lt_of_lt_of_le row (Nat.le_add_right _ _)))
  intro h hm
  have main := postfixed sat _ (relation_member (upper_mem.mp hm).2)
  simpa only [renamePair,names_head] using main

open LatticeInference LatticeInference.Completion LatticeGrowingInference
open ScopedPublication

/-- Instantiation of the existing original publication theorem. It retains
all its actual inventory, source metadata and locally indexed history inputs.
The terminal target and successful decision are now constructed from `s`.
No source/native correspondence is inferred from a native `Ok`. -/
theorem canonical_completed_publication
    {s : System} (sat : Saturated s)
    {n count bounds beforeCap afterCap beforeUse afterUse roots uses q base}
    {inventory clients : Store}
    (lawful : LawfulStore base s.names
      (inventory ++ clients.map (Constraint.rename (publicationTransport n count afterUse q))))
    (bounded : ScopedPublication.BoundsBounded n bounds)
    (images : ScopedPublication.InactiveImages n beforeUse afterUse q)
    (closed : ScopedPublication.StoppedClosed (bounds.map (ScopedPublication.Bound.rename q)) afterCap)
    (stops : ∀ k i, afterCap k i = false → afterUse k i = false)
    (useBounds : ∀ use, use ∈ uses → use < count)
    (coverage : ∀ clause,
      ScopedPublication.Published n (bounds.map (ScopedPublication.Bound.rename q)) afterCap afterUse
        (roots.map (ScopedPublication.Row.rename q)) uses clause → clause ∈ inventory) :
    let result := completedStore base s.names
      (inventory ++ clients.map (Constraint.rename (publicationTransport n count afterUse q)))
    ∀ {events ref birth finalEvents},
      GrowingHistory ref birth result.1 ⟨result.2,events⟩ s.graph
        ⟨s.clauses.map (renamePair s.names),finalEvents⟩ →
      Extends base s.graph ∧ s.graph.Valid ∧ s.graph.Guarded ∧
        PublishedSatisfied s.graph (fun k i => s.names k (publicationTransport n count afterUse q k i))
          n bounds beforeCap beforeUse roots uses ∧
        StoreSatisfied s.graph (fun k i => s.names k (publicationTransport n count afterUse q k i)) clients := by
  intro result events ref birth finalEvents history
  exact completed_decided_growing_publication_with_clients lawful bounded images closed stops useBounds coverage
    history (canonical_decided sat)

/-- Original Term/Store application without any supplied semantic model.
The remaining readback equation is syntactic and can be checked directly. -/
theorem canonical_decoded_store {s : System} (sat : Saturated s) {store : Store}
    (decoded : decodeStore s.graph s.names store = some (s.clauses.map (renamePair s.names))) :
    StoreSatisfied s.graph s.names store := by
  apply decoded_store_satisfied decoded
  intro pair member
  rcases List.mem_map.mp member with ⟨p,hp,rfl⟩
  exact canonical_bounds sat p hp

def recursiveSystem : System where
  rows := fun _ => 1
  heads := fun k => match k with
    | .value => [.function 0 0 0 0]
    | .effect => [.atom 7]
  clauses := [⟨.value,1,0⟩,⟨.value,0,1⟩,⟨.value,0,0⟩,⟨.value,1,1⟩,
    ⟨.effect,1,0⟩,⟨.effect,0,1⟩,⟨.effect,0,0⟩,⟨.effect,1,1⟩]

theorem recursive_member (p : Comparison) :
    p ∈ recursiveSystem.clauses ↔ p.lower < 2 ∧ p.upper < 2 := by
  rcases p with ⟨k,x,y⟩
  cases k <;> simp [recursiveSystem] <;> omega

theorem recursive_saturated : Saturated recursiveSystem := by
  constructor
  · intro p hp
    have h := (recursive_member p).mp hp
    cases p.kind <;> simpa [recursiveSystem] using h
  · intro k node member
    cases k <;> simp only [recursiveSystem,List.mem_singleton] at member <;>
      subst node <;> simp [Regular.Node.uniqueLabels,Regular.Node.references,recursiveSystem]
  · intro k x y hx hy pair h hm
    have xx : x = 0 := by simpa [recursiveSystem] using hx
    have yy : y = 0 := by simpa [recursiveSystem] using hy
    simpa [xx,yy] using hm
  · intro k x u hx pair h hm
    apply (recursive_member _).mpr
    have up := (recursive_member _).mp pair
    have low := (lower_mem.mp hm).1
    cases k <;> simp [recursiveSystem,System.head] at low up ⊢ <;> omega
  · intro k h u a b ha hb pair
    have hl := LatticeDecision.lookupList_index_lt ha
    have ul := LatticeDecision.lookupList_index_lt hb
    have hh : h = 0 := by cases k <;> simpa [recursiveSystem] using hl
    have uu : u = 0 := by cases k <;> simpa [recursiveSystem] using ul
    subst h; subst u
    cases k <;> simp only [recursiveSystem,lookupList,Option.some.injEq] at ha hb <;>
      subst a <;> subst b <;> simp [NodeRel,recursiveSystem]

def recursiveFunction : Term .value := .function (.var 0) (.var 0) (.var 0) (.var 0)

def recursiveStore : Store :=
  [⟨.value,recursiveFunction,.var 0⟩,⟨.value,.var 0,recursiveFunction⟩,
   ⟨.value,.var 0,.var 0⟩,⟨.value,recursiveFunction,recursiveFunction⟩,
   ⟨.effect,.atom 7,.var 0⟩,⟨.effect,.var 0,.atom 7⟩,
   ⟨.effect,.var 0,.var 0⟩,⟨.effect,.atom 7,.atom 7⟩]

theorem recursive_decoded :
    decodeStore recursiveSystem.graph recursiveSystem.names recursiveStore =
      some (recursiveSystem.clauses.map (renamePair recursiveSystem.names)) := rfl

/-- A real original Store has one shared recursive Function row, reused in
both value ports and both effect ports. Its graph/assignment are computed. -/
theorem recursive_store_constructed :
    recursiveSystem.graph.Valid ∧ recursiveSystem.graph.Guarded ∧
      StoreSatisfied recursiveSystem.graph recursiveSystem.names recursiveStore :=
  ⟨canonical_valid recursive_saturated,canonical_guarded _,
    canonical_decoded_store recursive_saturated recursive_decoded⟩

theorem recursive_decision_constructed :
    LatticeDecision.decideDemands recursiveSystem.graph
      (recursiveSystem.clauses.map (renamePair recursiveSystem.names)) = true :=
  canonical_decided recursive_saturated

def aliasSystem : System where
  rows := fun k => match k with | .value => 2 | .effect => 0
  heads := fun _ => []
  clauses := [⟨.value,0,1⟩,⟨.value,1,0⟩]

theorem alias_saturated : Saturated aliasSystem := by
  constructor
  · intro p hp
    simp only [aliasSystem,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl <;> decide
  · intro k node member; cases member
  · intro k x y hx hy pair h hm
    simp [System.lower,aliasSystem] at hm
  · intro k x u hx pair h hm
    simp [System.lower,aliasSystem] at hm
  · intro k h u a b ha hb pair
    cases h <;> cases ha

theorem alias_cycle_constructed :
    aliasSystem.graph.lookup .value (aliasSystem.names .value 0) = some (.structural .bottom) ∧
    aliasSystem.graph.lookup .value (aliasSystem.names .value 1) = some (.structural .bottom) ∧
    LatticeDecision.decideDemands aliasSystem.graph
      (aliasSystem.clauses.map (renamePair aliasSystem.names)) = true :=
  ⟨rfl,rfl,canonical_decided alias_saturated⟩

def unconstrainedSystem : System where
  rows := fun k => match k with | .value => 1 | .effect => 0
  heads := fun _ => []
  clauses := []

/-- Even the simplest interval does not identify its lower join and upper
meet. This is a discriminator for that proposed construction, not a source
program counterexample or a change to source semantics. -/
theorem lower_join_upper_meet_need_not_equal :
    unconstrainedSystem.graph.lookup .value (unconstrainedSystem.names .value 0) =
      some (.structural .bottom) ∧
    unconstrainedSystem.graph.lookup .value (unconstrainedSystem.index .value (.upper 0 [])) =
      some (.structural .top) ∧
    LatticeDecision.decideDemands unconstrainedSystem.graph
      [⟨.value,unconstrainedSystem.index .value (.upper 0 []),unconstrainedSystem.names .value 0⟩] = false := by
  decide

end YulangClosure.SimpleSub.NativeRowModel
