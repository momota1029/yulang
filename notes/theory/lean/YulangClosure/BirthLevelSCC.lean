import YulangClosure.Contracts

/-!
Birth-level Value qualification, following the authoritative
`notes/design/2026-10-24-birth-level-scc-intrusion.md`, §§2–4, and BL1 of
`notes/theory/2026-10-24-birth-level-scc-intrusion.md`.

The executable finite closure below is a specification algorithm, not a model
of the native Kosaraju implementation. Helper vertices have planning levels,
not Value births. Compression commutes with filtering only after the local
`PlanningInvariant` has been supplied for actual source-planning edges.
The original reference relation is retained unchanged. This module proves
graph qualification; it does not assert source inference soundness, lawful
generalization, or source-scoped coverage of parent/copy equalities.
-/
namespace YulangClosure.BirthLevelSCC

variable {V H : Type}

/-- Ordinary finite reachability, including the zero-edge path. -/
inductive Reach (edge : V → V → Prop) : V → V → Prop
  | refl {a} : Reach edge a a
  | cons {a b c} : edge a b → Reach edge b c → Reach edge a c

theorem Reach.trans {edge : V → V → Prop} {a b c : V}
    (ab : Reach edge a b) (bc : Reach edge b c) : Reach edge a c := by
  induction ab with
  | refl => exact bc
  | cons h _ ih => exact Reach.cons h (ih bc)

theorem Reach.mono {edge other : V → V → Prop}
    (map : ∀ a b, edge a b → other a b) {a b : V}
    (path : Reach edge a b) : Reach other a b := by
  induction path with
  | refl => exact Reach.refl
  | cons h _ ih => exact Reach.cons (map _ _ h) ih

/-- Filtering changes adjacency used for qualification, not the original Ref. -/
def SameLevel (edge : V → V → Prop) (level : V → Nat) (a b : V) : Prop :=
  edge a b ∧ level a = level b

theorem levelPath_source {edge : V → V → Prop} {birth : V → Nat}
    {k : Nat} {a b : V} (path : LevelPath edge birth k a b) : birth a = k := by
  cases path with
  | refl h => exact h
  | cons h _ _ _ => exact h

theorem levelPath_target {edge : V → V → Prop} {birth : V → Nat}
    {k : Nat} {a b : V} (path : LevelPath edge birth k a b) : birth b = k := by
  induction path with
  | refl h => exact h
  | cons _ _ _ _ ih => exact ih

theorem levelPath_toReach {edge : V → V → Prop} {birth : V → Nat}
    {k : Nat} {a b : V} (path : LevelPath edge birth k a b) :
    Reach (SameLevel edge birth) a b := by
  induction path with
  | refl _ => exact Reach.refl
  | cons ha hb h _ ih => exact Reach.cons ⟨h, ha.trans hb.symm⟩ ih

theorem reach_toLevelPath {edge : V → V → Prop} {birth : V → Nat}
    {a b : V} (path : Reach (SameLevel edge birth) a b)
    {k : Nat} (ha : birth a = k) : LevelPath edge birth k a b := by
  induction path with
  | refl => exact LevelPath.refl ha
  | cons h _ ih =>
    have hb := h.2.symm.trans ha
    exact LevelPath.cons ha hb h.1 (ih hb)

/-- Warshall closure over an explicit finite enumeration; repeats are harmless. -/
def finiteReach [DecidableEq V] (edge : V → V → Bool) : List V → V → V → Bool
  | [], a, b => decide (a = b) || edge a b
  | pivot :: rest, a, b =>
      finiteReach edge rest a b ||
        (finiteReach edge rest a pivot && finiteReach edge rest pivot b)

theorem finiteReach_refl [DecidableEq V] (edge : V → V → Bool)
    (vertices : List V) (a : V) : finiteReach edge vertices a a = true := by
  induction vertices with
  | nil => simp [finiteReach]
  | cons _ _ ih => simp [finiteReach, ih]

theorem finiteReach_edge [DecidableEq V] {edge : V → V → Bool}
    (vertices : List V) {a b : V} (h : edge a b = true) :
    finiteReach edge vertices a b = true := by
  induction vertices with
  | nil => simp [finiteReach, h]
  | cons _ _ ih => simp [finiteReach, ih]

theorem finiteReach_sound [DecidableEq V] {edge : V → V → Bool}
    (vertices : List V) {a b : V} (h : finiteReach edge vertices a b = true) :
    Reach (fun x y => edge x y = true) a b := by
  induction vertices generalizing a b with
  | nil =>
    simp only [finiteReach, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · subst b; exact Reach.refl
    · exact Reach.cons h Reach.refl
  | cons pivot rest ih =>
    simp only [finiteReach, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨left, right⟩
    · exact ih h
    · exact (ih left).trans (ih right)

/-- Closure can compose at each vertex already admitted as an intermediate. -/
theorem finiteReach_join [DecidableEq V] {edge : V → V → Bool}
    (vertices : List V) {a b c : V} (member : b ∈ vertices)
    (ab : finiteReach edge vertices a b = true)
    (bc : finiteReach edge vertices b c = true) :
    finiteReach edge vertices a c = true := by
  induction vertices generalizing a b c with
  | nil => cases member
  | cons pivot rest ih =>
    simp only [List.mem_cons] at member
    rcases member with same | member
    · subst b
      simp [finiteReach, finiteReach_refl] at ab bc
      simp only [finiteReach, Bool.or_eq_true, Bool.and_eq_true]
      exact Or.inr ⟨ab, bc⟩
    · simp only [finiteReach, Bool.or_eq_true, Bool.and_eq_true] at ab bc ⊢
      rcases ab with ab | ⟨ap, pb⟩
      · rcases bc with bc | ⟨bp, pc⟩
        · exact Or.inl (ih member ab bc)
        · exact Or.inr ⟨ih member ab bp, pc⟩
      · rcases bc with bc | ⟨_, pc⟩
        · exact Or.inr ⟨ap, ih member pb bc⟩
        · exact Or.inr ⟨ap, pc⟩

theorem finiteReach_complete [DecidableEq V] {edge : V → V → Bool}
    (vertices : List V) (covers : ∀ v, v ∈ vertices) {a b : V}
    (path : Reach (fun x y => edge x y = true) a b) :
    finiteReach edge vertices a b = true := by
  induction path with
  | refl => exact finiteReach_refl edge vertices _
  | @cons a b c h _ ih =>
    exact finiteReach_join vertices (covers b) (finiteReach_edge vertices h) ih

theorem finiteReach_iff [DecidableEq V] (edge : V → V → Bool)
    (vertices : List V) (covers : ∀ v, v ∈ vertices) (a b : V) :
    finiteReach edge vertices a b = true ↔
      Reach (fun x y => edge x y = true) a b :=
  ⟨finiteReach_sound vertices, finiteReach_complete vertices covers⟩

def filteredEdge (edge : V → V → Bool) (level : V → Nat) (a b : V) : Bool :=
  edge a b && decide (level a = level b)

/-- SCC membership in the level-induced graph, including singleton SCCs. -/
def eligible [DecidableEq V] (vertices : List V) (edge : V → V → Bool)
    (level : V → Nat) (a b : V) : Bool :=
  finiteReach (filteredEdge edge level) vertices a b &&
    finiteReach (filteredEdge edge level) vertices b a

theorem filteredEdge_iff (edge : V → V → Bool) (level : V → Nat) (a b : V) :
    filteredEdge edge level a b = true ↔
      SameLevel (fun x y => edge x y = true) level a b := by
  simp [filteredEdge, SameLevel]

theorem eligible_refl [DecidableEq V] (vertices : List V)
    (edge : V → V → Bool) (level : V → Nat) (a : V) :
    eligible vertices edge level a a = true := by
  simp [eligible, finiteReach_refl]

theorem eligible_reach_iff [DecidableEq V] (vertices : List V)
    (covers : ∀ v, v ∈ vertices) (edge : V → V → Bool) (level : V → Nat)
    (a b : V) : eligible vertices edge level a b = true ↔
      Reach (SameLevel (fun x y => edge x y = true) level) a b ∧
      Reach (SameLevel (fun x y => edge x y = true) level) b a := by
  have convert (x y : V) :
      Reach (fun x y => filteredEdge edge level x y = true) x y ↔
        Reach (SameLevel (fun x y => edge x y = true) level) x y := by
    constructor
    · exact Reach.mono (fun a b h => (filteredEdge_iff edge level a b).mp h)
    · exact Reach.mono (fun a b h => (filteredEdge_iff edge level a b).mpr h)
  simp only [eligible, Bool.and_eq_true, finiteReach_iff _ vertices covers, convert]

theorem mutual_sameLevel_iff {edge : V → V → Prop} {birth : V → Nat}
    {a b : V} :
    (Reach (SameLevel edge birth) a b ∧ Reach (SameLevel edge birth) b a) ↔
      ∃ k, LevelPath edge birth k a b ∧ LevelPath edge birth k b a := by
  constructor
  · rintro ⟨ab, ba⟩
    have pab := reach_toLevelPath ab rfl
    exact ⟨birth a, pab, reach_toLevelPath ba (levelPath_target pab)⟩
  · rintro ⟨k, ab, ba⟩
    exact ⟨levelPath_toReach ab, levelPath_toReach ba⟩

/-- Direct application to the unchanged occurrence qualification contract. -/
theorem finite_qualifies_iff [DecidableEq V] {T I : Type}
    (vertices : List V) (covers : ∀ v, v ∈ vertices)
    (edge : V → V → Bool) (birth : V → Nat)
    (event : ExtrusionOccurrence V T I) :
    eligible vertices edge birth event.origin event.receiver = true ↔
      Qualifies (fun x y => edge x y = true) birth event := by
  exact (eligible_reach_iff vertices covers edge birth _ _).trans mutual_sameLevel_iff

/-! Helper expansion and contraction. No birth is assigned to a helper. -/

abbrev Node (V H : Type) := Sum V H

def planningLevel (birth : V → Nat) (helperLevel : H → Nat) : Node V H → Nat
  | .inl value => birth value
  | .inr helper => helperLevel helper

/-- Every edge entering a helper preserves actual expression-planning level.
Edges entering semantic Values may cross birth levels and remain in `edge`. -/
def PlanningInvariant (edge : Node V H → Node V H → Prop)
    (birth : V → Nat) (helperLevel : H → Nat) : Prop :=
  ∀ source helper, edge source (.inr helper) →
    planningLevel birth helperLevel source = helperLevel helper

/-- A nonempty path whose internal vertices are all helpers. -/
inductive Incidence (edge : Node V H → Node V H → Prop) : Node V H → V → Prop
  | direct {source target} : edge source (.inl target) → Incidence edge source target
  | helper {source intermediate target} :
      edge source (.inr intermediate) → Incidence edge (.inr intermediate) target →
      Incidence edge source target

/-- The semantic reference represented by helper-only paths, before filtering. -/
def projectedRef (edge : Node V H → Node V H → Prop) (a b : V) : Prop :=
  Incidence edge (.inl a) b

theorem Incidence.toReach {edge : Node V H → Node V H → Prop}
    {source : Node V H} {target : V} (path : Incidence edge source target) :
    Reach edge source (.inl target) := by
  induction path with
  | direct h => exact Reach.cons h Reach.refl
  | helper h _ ih => exact Reach.cons h ih

theorem Incidence.erase {edge : Node V H → Node V H → Prop}
    {level : Node V H → Nat} {source : Node V H} {target : V}
    (path : Incidence (SameLevel edge level) source target) :
    Incidence edge source target := by
  induction path with
  | direct h => exact Incidence.direct h.1
  | helper h _ ih => exact Incidence.helper h.1 ih

theorem Incidence.level_eq {edge : Node V H → Node V H → Prop}
    {level : Node V H → Nat} {source : Node V H} {target : V}
    (path : Incidence (SameLevel edge level) source target) :
    level source = level (.inl target) := by
  induction path with
  | direct h => exact h.2
  | helper h _ ih => exact h.2.trans ih

/-- The local edge discipline derives preservation for every helper-only path. -/
theorem Incidence.filter {edge : Node V H → Node V H → Prop}
    {birth : V → Nat} {helperLevel : H → Nat}
    (invariant : PlanningInvariant edge birth helperLevel)
    {source : Node V H} {target : V} (path : Incidence edge source target)
    (endpoints : planningLevel birth helperLevel source = birth target) :
    Incidence (SameLevel edge (planningLevel birth helperLevel)) source target := by
  induction path with
  | direct h => exact Incidence.direct ⟨h, endpoints⟩
  | @helper source helper target h _ ih =>
    have edgeLevel := invariant source helper h
    exact Incidence.helper ⟨h, edgeLevel⟩ (ih (edgeLevel.symm.trans endpoints))

theorem projection_filter_iff {edge : Node V H → Node V H → Prop}
    {birth : V → Nat} {helperLevel : H → Nat}
    (invariant : PlanningInvariant edge birth helperLevel) (a b : V) :
    projectedRef (SameLevel edge (planningLevel birth helperLevel)) a b ↔
      SameLevel (projectedRef edge) birth a b := by
  constructor
  · intro path; exact ⟨path.erase, path.level_eq⟩
  · rintro ⟨path, equal⟩; exact path.filter invariant equal

/-- Compression is proved by splitting at each encountered semantic Value. -/
theorem compress_aux {edge : Node V H → Node V H → Prop}
    {source target : Node V H} (path : Reach edge source target) :
    ∀ value, target = .inl value →
      match source with
      | .inl start => Reach (projectedRef edge) start value
      | .inr helper => ∃ middle, Incidence edge (.inr helper) middle ∧
          Reach (projectedRef edge) middle value := by
  induction path with
  | @refl source =>
    intro value same
    subst source
    exact Reach.refl
  | @cons source middle target h _ ih =>
    intro value same
    have tail := ih value same
    cases source with
    | inl start =>
      cases middle with
      | inl next => exact Reach.cons (Incidence.direct h) tail
      | inr helper =>
        obtain ⟨next, incidence, rest⟩ := tail
        exact Reach.cons (Incidence.helper h incidence) rest
    | inr helper =>
      cases middle with
      | inl next => exact ⟨next, Incidence.direct h, tail⟩
      | inr nextHelper =>
        obtain ⟨next, incidence, rest⟩ := tail
        exact ⟨next, Incidence.helper h incidence, rest⟩

theorem compression_iff {edge : Node V H → Node V H → Prop} (a b : V) :
    Reach edge (.inl a) (.inl b) ↔ Reach (projectedRef edge) a b := by
  constructor
  · intro path; exact compress_aux path b rfl
  · intro path
    induction path with
    | refl => exact Reach.refl
    | cons h _ ih => exact h.toReach.trans ih

/-- Filtering and helper compression commute for all finite paths. -/
theorem filtered_compression_iff {edge : Node V H → Node V H → Prop}
    {birth : V → Nat} {helperLevel : H → Nat}
    (invariant : PlanningInvariant edge birth helperLevel) (a b : V) :
    Reach (SameLevel edge (planningLevel birth helperLevel)) (.inl a) (.inl b) ↔
      Reach (SameLevel (projectedRef edge) birth) a b := by
  rw [compression_iff]
  constructor
  · exact Reach.mono (fun x y h => (projection_filter_iff invariant x y).mp h)
  · exact Reach.mono (fun x y h => (projection_filter_iff invariant x y).mpr h)

/-- Exact original qualification from a finite implementation representation.
Only local helper edge discipline is assumed, never whole-path preservation. -/
theorem finite_helper_qualifies_iff [DecidableEq V] [DecidableEq H] {T I : Type}
    (vertices : List (Node V H)) (covers : ∀ v, v ∈ vertices)
    (edge : Node V H → Node V H → Bool) (birth : V → Nat) (helperLevel : H → Nat)
    (invariant : PlanningInvariant (fun x y => edge x y = true) birth helperLevel)
    (event : ExtrusionOccurrence V T I) :
    eligible vertices edge (planningLevel birth helperLevel)
      (.inl event.origin) (.inl event.receiver) = true ↔
    Qualifies (projectedRef (fun x y => edge x y = true)) birth event := by
  rw [eligible_reach_iff vertices covers, filtered_compression_iff invariant,
    filtered_compression_iff invariant]
  exact mutual_sameLevel_iff

/-! Kernel-reduced finite counterexamples to the superseded global-SCC rule. -/

inductive Three where
  | left | right | bridge
  deriving DecidableEq

def threeVertices : List Three := [.left, .right, .bridge]
def threeBirth : Three → Nat | .left => 1 | .right => 1 | .bridge => 2
def threeEdge : Three → Three → Bool
  | .left, .bridge => true
  | .bridge, .right => true
  | .right, .left => true
  | _, _ => false

theorem three_covers (v : Three) : v ∈ threeVertices := by
  cases v <;> simp [threeVertices]

/-- Equal-birth endpoints in one global SCC can require a different-birth
intermediate. Comparing only endpoint births after global SCC is insufficient. -/
theorem endpoint_filter_counterexample :
    threeBirth .left = threeBirth .right ∧
    finiteReach threeEdge threeVertices .left .right = true ∧
    finiteReach threeEdge threeVertices .right .left = true ∧
    eligible threeVertices threeEdge threeBirth .left .right = false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem endpoint_filter_not_qualified {T I : Type}
    (event : ExtrusionOccurrence Three T I)
    (origin : event.origin = .left) (receiver : event.receiver = .right) :
    ¬ Qualifies (fun x y => threeEdge x y = true) threeBirth event := by
  intro h
  have accepted := (finite_qualifies_iff threeVertices three_covers threeEdge
    threeBirth event).mpr h
  rw [origin, receiver] at accepted
  cases accepted

inductive Two where
  | outer | inner
  deriving DecidableEq

def twoVertices : List Two := [.outer, .inner]
def twoBirth : Two → Nat | .outer => 1 | .inner => 2
def twoEdge : Two → Two → Bool
  | .outer, .inner => true
  | .inner, .outer => true
  | _, _ => false

theorem two_covers (v : Two) : v ∈ twoVertices := by
  cases v <;> simp [twoVertices]

/-- Graph shape of the nested outer/inner reference cycle: retain both edges,
but neither cross-birth occurrence receives eligibility. -/
theorem cross_birth_cycle_rejected :
    finiteReach twoEdge twoVertices .outer .inner = true ∧
    finiteReach twoEdge twoVertices .inner .outer = true ∧
    eligible twoVertices twoEdge twoBirth .outer .inner = false ∧
    eligible twoVertices twoEdge twoBirth .inner .outer = false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem cross_birth_not_qualified {T I : Type}
    (event : ExtrusionOccurrence Two T I)
    (origin : event.origin = .outer) (receiver : event.receiver = .inner) :
    ¬ Qualifies (fun x y => twoEdge x y = true) twoBirth event := by
  intro h
  have accepted := (finite_qualifies_iff twoVertices two_covers twoEdge
    twoBirth event).mpr h
  rw [origin, receiver] at accepted
  cases accepted

end YulangClosure.BirthLevelSCC
