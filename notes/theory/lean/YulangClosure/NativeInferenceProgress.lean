import YulangClosure.OriginalInferenceTermination
import YulangClosure.NativeValuePorts

/-! Source-owned Context descriptor closure. This is not a whole-drain
termination theorem: row, view, scoped-flow and generation births remain owned
by their native constructors. In particular bootstrap annotation fibers retain
nonidentity singleton filters. No finite universe or completed run is assumed.
-/
namespace YulangClosure.NativeInferenceProgress
open NativeMergeExpansion NativeContextExpansion
open NativeReplayCurrent (sourceContext admittedChild Pair)

/-- Native source-local contexts, including the negative annotation initializer. -/
def Atom (t : Tables) (context : Nat) : Prop :=
  context = 0 ∨ ∃ weight, context ≠ 0 ∧ t.contexts context = some (.prefix weight 0)

/-- One actual replay composition of retained source-local fibers. -/
def Shallow (t : Tables) (context : Nat) : Prop :=
  Atom t context ∨ ∃ lower upper,
    t.contexts context = some (.replay lower upper) ∧
    lower < context ∧ upper < context ∧
    Atom t lower ∧ Atom t upper ∧ (lower ≠ 0 ∨ upper ≠ 0)

theorem source_context_atom {t : Tables} {upper : Endpoint}
    (available : sourceAvailable t upper = true) :
    Atom t (sourceContext (admissionTables t) upper) := by
  cases upper <;> try { exact Or.inl rfl }
  rename_i view
  cases found : t.views view with
  | none => simp [sourceAvailable, found] at available
  | some v =>
    cases weight : v.closedWeight with
    | none => exact Or.inl (by simp [sourceContext, admissionTables, found, weight])
    | some w =>
      simp only [sourceAvailable, found, weight, Bool.and_eq_true_iff, decide_eq_true_eq] at available
      right
      refine ⟨w, ?_, ?_⟩
      · simpa [sourceContext, admissionTables, found, weight] using available.1
      · simpa [sourceContext, admissionTables, found, weight] using available.2

theorem admitted_context_atom {t : Tables} {a : Availability} {q : Nat → Nat}
    {parent child : Key} {pair : Pair}
    (computed : admit t a q parent pair = some child) : Atom t child.context := by
  have payload := admit_payload computed
  simp only [admit] at computed
  split at computed
  · rename_i guards
    have available := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp guards).1).1
    rw [payload.2.1]
    exact source_context_atom available
  · cases computed

/-- The actual checked-bound constructor selects zero before any callback
completion is published, on both registered and newly inserted branches. -/
theorem filter_bound_identity {t : Tables} {a : Availability} {levels q : Nat → Nat}
    {parent : Key} {view : Nat} {fiber : Fiber}
    (computed : applyFilter t a levels q parent view = some (.bound fiber)) :
    fiber.key.context = 0 := by
  cases lower : (NativeReplayCurrent.currentPair q parent).1 <;>
    simp only [applyFilter, lower] at computed
  all_goals try { exact (apply_bound_exact computed).2.1 }
  split at computed
  · split at computed
    · cases computed; rfl
    · cases computed
  · exact (apply_bound_exact computed).2.1

/-- Complete Context consumption: every inline filter and the unconsumed
continuation is included. This does not infer callback termination from success. -/
theorem decompose_fibers_identity {t : Tables} {a : Availability} {levels q : Nat → Nat}
    {parent : Key} {parsed : Parsed} {body : Body}
    (computed : decompose t a levels q parent parsed = some body)
    (post : (if parsed.filters = [] then parent.context else parsed.residual) = 0) :
    ∀ fiber ∈ body.fibers, fiber.key.context = 0 := by
  have details := decompose_exact computed
  intro fiber member
  obtain ⟨leaf, selected, inLeaf⟩ := List.mem_flatMap.mp member
  cases leaf with
  | localReturn => cases inLeaf
  | children keys => cases inLeaf
  | conflict pair => cases inLeaf
  | bound actual =>
    have same : fiber = actual := List.mem_singleton.mp inLeaf
    subst fiber
    change Leaf.bound actual ∈ body.checks.map Check.leaf ++ body.continuation.toList at selected
    rcases List.mem_append.mp selected with checked | continuation
    · obtain ⟨check, member, same⟩ := List.mem_map.mp checked
      obtain ⟨weight, _, result⟩ := aligned_member_right details.2.1 member
      obtain ⟨_, payload, _, _, _, applied⟩ := check_filter_exact result
      rw [same] at applied
      exact filter_bound_identity applied
    · have applied := details.2.2.2.2.2.1 _ (Option.mem_toList.mp continuation)
      exact (apply_bound_exact applied).2.1.trans (details.2.2.1.trans post)

theorem decompose_children_atom {t : Tables} {a : Availability} {levels q : Nat → Nat}
    {parent : Key} {parsed : Parsed} {body : Body}
    (computed : decompose t a levels q parent parsed = some body) :
    ∀ child ∈ body.children, Atom t child.context := by
  have details := decompose_exact computed
  intro child member
  obtain ⟨leaf, selected, inLeaf⟩ := List.mem_flatMap.mp member
  cases leaf with
  | localReturn => cases inLeaf
  | bound fiber => cases inLeaf
  | conflict pair => cases inLeaf
  | children keys =>
    have applied : ∃ context pair, applyEffect t a levels q parent context pair = some (.children keys) := by
      change Leaf.children keys ∈ body.checks.map Check.leaf ++ body.continuation.toList at selected
      rcases List.mem_append.mp selected with checked | continuation
      · obtain ⟨check, member, same⟩ := List.mem_map.mp checked
        obtain ⟨weight, _, result⟩ := aligned_member_right details.2.1 member
        obtain ⟨_, payload, _, _, _, applied⟩ := check_filter_exact result
        rw [same] at applied
        exact ⟨_, _, filter_children_from_apply applied⟩
      · exact ⟨_, _, details.2.2.2.2.2.1 _ (Option.mem_toList.mp continuation)⟩
    obtain ⟨context, pair, applied⟩ := applied
    obtain ⟨pairs, _, admitted⟩ := apply_children_admitted applied
    obtain ⟨input, _, actual⟩ := aligned_member_right admitted inLeaf
    exact admitted_context_atom actual

/-- The Value port constructor keeps actual source indices/scoped payloads in
its owner. At an identity post-context no directed context can be allocated. -/
theorem value_port_context_atom (arena : NativeValuePorts.Arena)
    (weight : Option Nat) (swap : Bool) :
    let result := NativeValuePorts.buildContext arena weight 0 swap
    result.2 = 0 ∨ ∃ w, result.2 ≠ 0 ∧ result.1.contextAt result.2 = some (.prefix w 0) := by
  have exactResult := NativeValuePorts.build_context_exact arena weight 0 swap
  unfold NativeValuePorts.ContextResult at exactResult
  obtain ⟨inherited, base, found⟩ := exactResult
  have zero : inherited = 0 := by simpa using base
  cases weight with
  | none => exact Or.inl (found.trans zero)
  | some w =>
    right
    refine ⟨w, ?_, ?_⟩
    · intro impossible
      simp [NativeValuePorts.Arena.contextAt, impossible] at found
    · simpa [zero] using found

def initialScan (root : Nat) : Scan :=
  ⟨[(root, .outer)], [], [], root, false, false, false⟩

def ParsedClean (root : Nat) (p : Parsed) : Prop :=
  p.residual = 0 ∧ p.directed = false ∧ (p.filters = [] → root = 0)

theorem total_next {t : Tables} {s u : Scan} (pending : s.pending ≠ [])
    (next : scanStep t s = some u) :
    OriginalInferenceTermination.scanTotal t s = OriginalInferenceTermination.scanTotal t u := by
  rw [OriginalInferenceTermination.scanTotal, ite_eq_right pending, next]

theorem total_reject {t : Tables} {s : Scan} (pending : s.pending ≠ [])
    (next : scanStep t s = none) : OriginalInferenceTermination.scanTotal t s = none := by
  rw [OriginalInferenceTermination.scanTotal, ite_eq_right pending, next]

theorem total_finish {t : Tables} {s : Scan} (empty : s.pending = []) :
    OriginalInferenceTermination.scanTotal t s = finish s := by
  rw [OriginalInferenceTermination.scanTotal, ite_eq_left empty]

theorem total_bind {t : Tables} {s : Scan} (pending : s.pending ≠ []) :
    OriginalInferenceTermination.scanTotal t s =
      (scanStep t s).bind (OriginalInferenceTermination.scanTotal t) := by
  rw [OriginalInferenceTermination.scanTotal, ite_eq_right pending]
  cases scanStep t s <;> rfl

theorem atomic_scan_clean {t : Tables} {root : Nat} {p : Parsed}
    (shape : Atom t root)
    (computed : OriginalInferenceTermination.scanTotal t (initialScan root) = some p) :
    ParsedClean root p := by
  rcases shape with rfl | ⟨w, nonzero, found⟩
  · let last : Scan := ⟨[], [], [], 0, false, false, false⟩
    have next : scanStep t (initialScan 0) = some last := by simp [scanStep, initialScan, last]
    rw [total_next (by simp [initialScan]) next, total_finish (by rfl)] at computed
    simp [finish, last] at computed
    subst p
    simp [ParsedClean]
  · have positive : 0 < root := Nat.pos_of_ne_zero nonzero
    by_cases valid : weightValid t w = true
    · let first : Scan := ⟨[(0, .outer)], [(root, .outer)], [w], 0, false, false, false⟩
      let last : Scan := {first with pending := []}
      have next : scanStep t (initialScan root) = some first := by
        simp [scanStep, initialScan, first, found, nonzero, positive, valid, attach]
      have final : scanStep t first = some last := by simp [scanStep, first, last]
      rw [total_next (by simp [initialScan]) next,
        total_next (by simp [first]) final, total_finish (by rfl)] at computed
      simp [finish, first, last] at computed
      subst p
      simp [ParsedClean]
    · have rejected : scanStep t (initialScan root) = none := by
        simp [scanStep, initialScan, found, nonzero, positive, valid]
      rw [total_reject (by simp [initialScan]) rejected] at computed
      cases computed

theorem replay_scan_clean {t : Tables} {root lower upper : Nat} {p : Parsed}
    (found : t.contexts root = some (.replay lower upper))
    (left : lower < root) (right : upper < root)
    (lowerAtom : Atom t lower) (upperAtom : Atom t upper)
    (nontrivial : lower ≠ 0 ∨ upper ≠ 0)
    (computed : OriginalInferenceTermination.scanTotal t (initialScan root) = some p) :
    ParsedClean root p := by
  have rootNonzero : root ≠ 0 := by omega
  have lowerNe : lower ≠ root := by omega
  have upperNe : upper ≠ root := by omega
  rcases lowerAtom with rfl | ⟨lw, lowerNonzero, lowerFound⟩
  · rcases upperAtom with rfl | ⟨uw, upperNonzero, upperFound⟩
    · simp at nontrivial
    · by_cases valid : weightValid t uw = true
      · simp [initialScan, total_bind, total_finish, scanStep, finish, found, Nat.pos_iff_ne_zero,
          rootNonzero, left, right, upperNe, upperNonzero, upperFound, valid, attach] at computed
        subst p
        simp [ParsedClean]
      · simp [initialScan, total_bind, scanStep, found, Nat.pos_iff_ne_zero,
          rootNonzero, left, right, upperNe, upperNonzero, upperFound, valid, attach] at computed
  · rcases upperAtom with rfl | ⟨uw, upperNonzero, upperFound⟩
    · by_cases valid : weightValid t lw = true
      · simp [initialScan, total_bind, total_finish, scanStep, finish, found, Nat.pos_iff_ne_zero,
          rootNonzero, left, right, lowerNe, lowerNonzero, lowerFound, valid, attach] at computed
        subst p
        simp [ParsedClean]
      · simp [initialScan, total_bind, scanStep, found, Nat.pos_iff_ne_zero,
          rootNonzero, left, right, lowerNe, lowerNonzero, lowerFound, valid, attach] at computed
    · by_cases same : lower = upper
      · subst upper
        rw [lowerFound] at upperFound
        cases upperFound
        by_cases valid : weightValid t lw = true
        · simp [initialScan, total_bind, total_finish, scanStep, finish, found, Nat.pos_iff_ne_zero,
            rootNonzero, left, lowerNe, lowerNonzero, lowerFound, valid, attach] at computed
          subst p
          simp [ParsedClean]
        · simp [initialScan, total_bind, scanStep, found, Nat.pos_iff_ne_zero,
            rootNonzero, left, lowerNe, lowerNonzero, lowerFound, valid, attach] at computed
      · by_cases lv : weightValid t lw = true <;> by_cases uv : weightValid t uw = true
        all_goals simp [initialScan, total_bind, total_finish, scanStep, finish, found, Nat.pos_iff_ne_zero,
          rootNonzero, left, right, lowerNe, upperNe, lowerNonzero, upperNonzero,
          lowerFound, upperFound, Ne.symm same, lv, uv, attach] at computed
        split at computed <;> subst p <;> simp [ParsedClean]

/-- The parser is the proved total native scan. The complete checked callback
projection follows it, including the unconsumed continuation and all emissions. -/
def consume (t : Tables) (a : Availability) (levels q : Nat → Nat) (parent : Key) : Option Body :=
  (OriginalInferenceTermination.scanTotal t (initialScan parent.context)).bind
    (decompose t a levels q parent)

theorem shallow_scan_clean {t : Tables} {root : Nat} {p : Parsed}
    (shape : Shallow t root)
    (computed : OriginalInferenceTermination.scanTotal t (initialScan root) = some p) :
    ParsedClean root p := by
  rcases shape with atomic | ⟨lower, upper, found, left, right, lowerAtom, upperAtom, nontrivial⟩
  · exact atomic_scan_clean atomic computed
  · exact replay_scan_clean found left right lowerAtom upperAtom nontrivial computed

/-- This closes the cyclic Context-shape seam: a shallow Replay can produce
source-local callback requests and identity bound fibers, never a deeper bound
Context. Full endpoint/source/transformer payloads remain in the existing Body. -/
theorem consume_context_closure {t : Tables} {a : Availability} {levels q : Nat → Nat}
    {parent : Key} {body : Body} (shape : Shallow t parent.context)
    (computed : consume t a levels q parent = some body) :
    body.postContext = 0 ∧
    (∀ fiber ∈ body.fibers, fiber.key.context = 0) ∧
    (∀ child ∈ body.children, Atom t child.context) := by
  obtain ⟨parsed, scanned, decomposed⟩ := Option.bind_eq_some_iff.mp computed
  have clean := shallow_scan_clean shape scanned
  have post : (if parsed.filters = [] then parent.context else parsed.residual) = 0 := by
    split
    · exact clean.2.2 ‹_›
    · exact clean.1
  exact ⟨(decompose_exact decomposed).2.2.1.trans post,
    decompose_fibers_identity decomposed post, decompose_children_atom decomposed⟩

/-- Refine the existing native expansion result to the total-parser consumption
segment. Entry/current-pair/parser/publication failure gates are preserved by
`computed`; this implication does not admit an input rejected by `expand`. -/
theorem expand_consumes {t : Tables} {a : Availability} {levels q : Nat → Nat}
    {fuel : Nat} {parent : Key} {body : Body}
    (computed : expand t a levels q fuel parent = some body) :
    consume t a levels q parent = some body := by
  unfold expand at computed
  split at computed
  · split at computed
    · rename_i identity
      simp only [Option.bind_some] at computed
      have scan : OriginalInferenceTermination.scanTotal t (initialScan parent.context) =
          some ⟨[], 0, false, false, false⟩ := by
        rw [identity]
        let last : Scan := ⟨[], [], [], 0, false, false, false⟩
        have next : scanStep t (initialScan 0) = some last := by
          simp [scanStep, initialScan, last]
        rw [total_next (by simp [initialScan]) next, total_finish (by rfl)]
        simp [finish, last]
      simp only [consume, scan, Option.bind_some]
      exact computed
    · split at computed
      · obtain ⟨parsed, scanned, decomposed⟩ := Option.bind_eq_some_iff.mp computed
        have scan := (OriginalInferenceTermination.scanTotal_success_iff t
          (initialScan parent.context) parsed).2 (scan_computes_run scanned)
        simp only [consume, scan, Option.bind_some]
        exact decomposed
      · cases computed
  · cases computed

theorem native_expand_context_closure {t : Tables} {a : Availability} {levels q : Nat → Nat}
    {fuel : Nat} {parent : Key} {body : Body} (shape : Shallow t parent.context)
    (computed : expand t a levels q fuel parent = some body) :
    body.postContext = 0 ∧
    (∀ fiber ∈ body.fibers, fiber.key.context = 0) ∧
    (∀ child ∈ body.children, Atom t child.context) :=
  consume_context_closure shape (expand_consumes computed)

/-- Native signature initialization is allowed to attach a singleton filter.
There is no assumption that bootstrap fibers already passed Context. -/
def signatureFiber (t : Tables) (bound : Bound) (sources : Option Nat) (transformer : Nat) : Fiber :=
  exactFiber bound (sourceContext (admissionTables t) bound.pair.2) sources transformer

theorem signature_fiber_atom {t : Tables} (bound : Bound) (sources : Option Nat) (transformer : Nat)
    (available : sourceAvailable t bound.pair.2 = true) :
    Atom t (signatureFiber t bound sources transformer).key.context :=
  source_context_atom available

/-- Stored complete-key lookup used by transport, not a claim that a memo is
completion. Only actual successful Context results can add these zero entries. -/
theorem post_atom (t : Tables) (entries : List (Key × Nat))
    (zero : ∀ entry ∈ entries, entry.2 = 0) (key : Key) (atomic : Atom t key.context) :
    Atom t (postCheck entries key) := by
  induction entries with
  | nil => exact atomic
  | cons entry rest ih =>
    simp only [postCheck]
    split
    · exact Or.inl (zero entry (by simp))
    · exact ih (fun e member => zero e (List.mem_cons_of_mem _ member))

/-- Exact retained-fiber transport used by extrusion, parent/copy equality and
representative canonicalization. Source sets and transformers are untouched. -/
theorem transport_atom (t : Tables) (entries : List (Key × Nat))
    (zero : ∀ entry ∈ entries, entry.2 = 0) (fiber : Fiber) (target : Bound)
    (atomic : Atom t fiber.key.context) :
    Atom t (transport (postCheck entries) fiber target).key.context ∧
    (transport (postCheck entries) fiber target).key.sources = fiber.key.sources ∧
    (transport (postCheck entries) fiber target).key.transformer = fiber.key.transformer :=
  ⟨post_atom t entries zero fiber.key atomic, rfl, rfl⟩

/-- Context coordinate of the actual Replay constructor, including its only
identity simplification. The ordered lower/upper inputs remain separate. -/
def replayContext (lower upper allocated : Nat) : Nat :=
  if lower = 0 ∧ upper = 0 then 0 else allocated

theorem replay_context_shallow {t : Tables} {lower upper allocated : Nat}
    (lowerAtom : Atom t lower) (upperAtom : Atom t upper)
    (constructed : (lower = 0 ∧ upper = 0) ∨
      (t.contexts allocated = some (.replay lower upper) ∧ lower < allocated ∧ upper < allocated)) :
    Shallow t (replayContext lower upper allocated) := by
  unfold replayContext
  split
  · exact Or.inl (Or.inl rfl)
  · rename_i nontrivial
    rcases constructed with identity | ⟨found, left, right⟩
    · exact False.elim (nontrivial identity)
    · exact Or.inr ⟨lower, upper, found, left, right, lowerAtom, upperAtom, by omega⟩

/-- Successful atomic branches of `rename_contexts_impl`: Identity maps to
Identity; a source prefix rebuilds its mapped weight and mapped Identity child.
The full native renamer still supports every other Context constructor. -/
inductive RenamedAtom (t : Tables) : Nat → Nat → Prop
  | identity : RenamedAtom t 0 0
  | sourcePrefix (old fresh weight mappedWeight : Nat)
      (oldNonzero : old ≠ 0) (freshNonzero : fresh ≠ 0)
      (source : t.contexts old = some (.prefix weight 0))
      (constructed : t.contexts fresh = some (.prefix mappedWeight 0)) :
      RenamedAtom t old fresh

theorem renamed_atom (t : Tables) {old fresh : Nat} (renamed : RenamedAtom t old fresh) :
    Atom t fresh := by
  cases renamed with
  | identity => exact Or.inl rfl
  | sourcePrefix old fresh weight mappedWeight oldNonzero freshNonzero source constructed =>
    exact Or.inr ⟨mappedWeight, freshNonzero, constructed⟩

/-- Constructor projection with the complete Effect keys, actual bound objects,
and published post-context coordinates. This is not `inferStep`: it isolates
Context descriptor creation without erasing the source/transformer payload. -/
structure State where
  requests : List Key := []
  fibers : List Fiber := []
  checked : List (Key × Nat) := []

def Invariant (t : Tables) (s : State) : Prop :=
  (∀ key ∈ s.requests, Shallow t key.context) ∧
  (∀ fiber ∈ s.fibers, Atom t fiber.key.context) ∧
  (∀ entry ∈ s.checked, entry.2 = 0)

inductive Step (t : Tables) : State → State → Prop
  | source (s : State) (key : Key)
      (available : sourceAvailable t key.upper = true)
      (selected : key.context = sourceContext (admissionTables t) key.upper) :
      Step t s {s with requests := key :: s.requests}
  | signature (s : State) (bound : Bound) (sources : Option Nat) (transformer : Nat)
      (available : sourceAvailable t bound.pair.2 = true) :
      Step t s {s with fibers := signatureFiber t bound sources transformer :: s.fibers}
  | context (s : State) (parent : Key) (a : Availability) (levels q : Nat → Nat) (body : Body)
      (selected : parent ∈ s.requests)
      (computed : consume t a levels q parent = some body) :
      Step t s {
        requests := body.children ++ s.requests
        fibers := body.fibers ++ s.fibers
        checked := if body.parsed.filters = [] then s.checked else (parent, body.postContext) :: s.checked}
  | replay (s : State) (lower upper : Fiber) (key : Key) (allocated : Nat)
      (lowerSelected : lower ∈ s.fibers) (upperSelected : upper ∈ s.fibers)
      (constructed : (lower.key.context = 0 ∧ upper.key.context = 0) ∨
        (t.contexts allocated = some (.replay lower.key.context upper.key.context) ∧
          lower.key.context < allocated ∧ upper.key.context < allocated))
      (selected : key.context = replayContext lower.key.context upper.key.context allocated) :
      Step t s {s with requests := key :: s.requests}
  | transport (s : State) (fiber : Fiber) (target : Bound) (selected : fiber ∈ s.fibers) :
      Step t s {s with fibers := NativeMergeExpansion.transport (postCheck s.checked) fiber target :: s.fibers}

  | fresh (s : State) (parent child : Fiber) (selected : parent ∈ s.fibers)
      (renamed : RenamedAtom t (postCheck s.checked parent.key) child.key.context) :
      Step t s {s with fibers := child :: s.fibers}

/-- Each native construction case preserves descriptor closure; there is no
assumed finite table, fuel, callback transcript or final store here. -/
theorem step_invariant {t : Tables} {s u : State} (step : Step t s u)
    (invariant : Invariant t s) : Invariant t u := by
  rcases invariant with ⟨requests, fibers, checked⟩
  cases step with
  | source key available selected =>
    refine ⟨?_, fibers, checked⟩
    intro child member
    rcases List.mem_cons.mp member with rfl | old
    · rw [selected]; exact Or.inl (source_context_atom available)
    · exact requests child old
  | signature bound sources transformer available =>
    refine ⟨requests, ?_, checked⟩
    intro fiber member
    rcases List.mem_cons.mp member with rfl | old
    · exact signature_fiber_atom bound sources transformer available
    · exact fibers fiber old
  | context parent a levels q body selected computed =>
    obtain ⟨post, newFibers, newChildren⟩ := consume_context_closure (requests parent selected) computed
    refine ⟨?_, ?_, ?_⟩
    · intro key member
      rcases List.mem_append.mp member with new | old
      · exact Or.inl (newChildren key new)
      · exact requests key old
    · intro fiber member
      rcases List.mem_append.mp member with new | old
      · exact Or.inl (newFibers fiber new)
      · exact fibers fiber old
    · split
      · exact checked
      · intro entry member
        rcases List.mem_cons.mp member with rfl | old
        · exact post
        · exact checked entry old
  | replay lower upper key allocated lowerSelected upperSelected constructed selected =>
    refine ⟨?_, fibers, checked⟩
    intro child member
    rcases List.mem_cons.mp member with rfl | old
    · rw [selected]
      exact replay_context_shallow (fibers lower lowerSelected) (fibers upper upperSelected) constructed
    · exact requests child old
  | transport fiber target selected =>
    refine ⟨requests, ?_, checked⟩
    intro child member
    rcases List.mem_cons.mp member with rfl | old
    · exact (transport_atom t s.checked checked fiber target (fibers fiber selected)).1
    · exact fibers child old
  | fresh parent child selected renamed =>
    refine ⟨requests, ?_, checked⟩
    intro fiber member
    rcases List.mem_cons.mp member with rfl | old
    · exact renamed_atom t renamed
    · exact fibers fiber old

inductive Reachable (t : Tables) : State → Prop
  | initial : Reachable t {}
  | step {s u : State} : Reachable t s → Step t s u → Reachable t u

theorem reachable_context_closure {t : Tables} {s : State} (history : Reachable t s) :
    Invariant t s := by
  induction history with
  | initial => simp [Invariant]
  | step _ step ih => exact step_invariant step ih

theorem atom_extension {t u : Tables} (ext : NativeContextTables.TableExtension t u)
    {context : Nat} (atomic : Atom t context) : Atom u context := by
  rcases atomic with zero | ⟨weight, nonzero, found⟩
  · exact Or.inl zero
  · exact Or.inr ⟨weight, nonzero, ext.contexts _ _ found⟩

theorem shallow_extension {t u : Tables} (ext : NativeContextTables.TableExtension t u)
    {context : Nat} (shape : Shallow t context) : Shallow u context := by
  rcases shape with atomic | ⟨lower, upper, found, left, right, lowerAtom, upperAtom, nontrivial⟩
  · exact Or.inl (atom_extension ext atomic)
  · exact Or.inr ⟨lower, upper, ext.contexts _ _ found, left, right,
      atom_extension ext lowerAtom, atom_extension ext upperAtom, nontrivial⟩

theorem invariant_extension {t u : Tables} (ext : NativeContextTables.TableExtension t u)
    {s : State} (invariant : Invariant t s) : Invariant u s :=
  ⟨fun key member => shallow_extension ext (invariant.1 key member),
    fun fiber member => atom_extension ext (invariant.2.1 fiber member), invariant.2.2⟩

/-- No globally fixed universe: table extension and source/filter/view births
can be interleaved with every construction step. The actual native table Run
supplies its extension by `NativeContextTables.run_table_extension`. -/
inductive GrowingReachable : Tables → State → Prop
  | initial (t : Tables) : GrowingReachable t {}
  | step {t : Tables} {s u : State} : GrowingReachable t s → Step t s u → GrowingReachable t u
  | tables {t u : Tables} {s : State} : GrowingReachable t s →
      NativeContextTables.TableExtension t u → GrowingReachable u s

theorem growing_context_closure {t : Tables} {s : State} (history : GrowingReachable t s) :
    Invariant t s := by
  induction history with
  | initial => simp [Invariant]
  | step _ step ih => exact step_invariant step ih
  | tables _ ext ih => exact invariant_extension ext ih

/-- Apply the descriptor result to the actual full-expression interner's
allocation result. This establishes the FreshUse prefix constructor's output,
including a nonzero ID; no preexisting mapped node is assumed. -/
theorem fresh_prefix_constructed (arena : NativeValuePorts.Arena) (mappedWeight : Nat) :
    let next := arena.context (.prefix mappedWeight 0)
    next.2 ≠ 0 ∧ next.1.contextAt next.2 = some (.prefix mappedWeight 0) := by
  refine ⟨?_, (NativeValuePorts.context_constructed arena (.prefix mappedWeight 0)).1⟩
  simp [NativeValuePorts.Arena.context]

end YulangClosure.NativeInferenceProgress
