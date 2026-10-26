import YulangClosure.NativeMergeExpansion

/-!
Finite current-disposition graph construction for the Effect operand fragment.
Vertices keep the complete ORIGINAL relation key. A generation change updates
the representative observation and exact retained-bound carriers; it does not
pretend that a post-check carrier has the original stored context.

The graph is constructed by local events. Emitted children are registered by
the event, including back-references to an already registered active vertex.
No recursive coverage, acyclic-dependency or completed-memo law is an input.
An all-depth result is relative to explicit current frontier vertices and
retained bound fibers. Authentication of this event projection, complete Context
factoring, Value ports and accepted native drain remains separate.
-/
namespace YulangClosure.NativeReplayCurrent

open NativeMergeExpansion
open NativeReplayCoverage (product)

abbrev Pair := Endpoint × Endpoint

def currentPair (q : Nat → Nat) (key : Key) : Pair :=
  (renameEndpoint q key.lower, renameEndpoint q key.upper)

def operand (tables : Effect.Tables) (q : Nat → Nat) (key : Key) : Effect.Outcome :=
  Effect.checkOperand q tables (currentPair q key).1 (currentPair q key).2

theorem currentPair_absorb (old current : Nat → Nat)
    (absorbs : ∀ row, current (old row) = current row) (key : Key) :
    Effect.renamePair current (currentPair old key) = currentPair current key := by
  simp [Effect.renamePair, currentPair, renameEndpoint_absorb old current absorbs]

theorem operand_transport (tables : Effect.Tables) (old current : Nat → Nat)
    (absorbs : ∀ row, current (old row) = current row) (key : Key) :
    operand tables current key = Effect.renameOutcome current (operand tables old key) := by
  have h := Effect.operand_expansion_transport old current absorbs tables
    (renameEndpoint old key.lower) (renameEndpoint old key.upper)
  simpa only [operand, currentPair, renameEndpoint_absorb old current absorbs] using h

theorem dependencyPath_trans {edges : List (Key × Key)} {a b c : Key}
    (first : DependencyPath edges a b) (second : DependencyPath edges b c) :
    DependencyPath edges a c := by
  induction first with
  | refl => exact second
  | step edge rest ih => exact .step edge (ih second)

/-- The two actual successful local Effect returns. The reflexive case
retains the Context-stage prohibition on a nonidentity scoped self-relation. -/
def LocalReturn (tables : Effect.Tables) (q : Nat → Nat) (key : Key) : Prop :=
  operand tables q key = .localReturn ∨
    (currentPair q key).1 = (currentPair q key).2 ∧ key.transformer = 0

theorem localReturn_transport (tables : Effect.Tables) (old current : Nat → Nat)
    (absorbs : ∀ row, current (old row) = current row) (key : Key)
    (h : LocalReturn tables old key) : LocalReturn tables current key := by
  rcases h with returned | ⟨same, identity⟩
  · left
    rw [operand_transport tables old current absorbs, returned]
    rfl
  · right
    refine ⟨?_, identity⟩
    have mapped := congrArg (renameEndpoint current) same
    simpa only [currentPair, renameEndpoint_absorb old current absorbs] using mapped

inductive Body where
  | localReturn
  | children (keys : List Key)
  | bound (fiber : Fiber)
  deriving DecidableEq, Repr

inductive Disposition where
  | retained
  | queued
  | active
  | expanded (body : Body)
  | returned (body : Body)
  deriving DecidableEq, Repr

def Body.transport (q : Nat → Nat) (post : Key → Nat) : Body → Body
  | .bound fiber => .bound (carrier q post fiber)
  | body => body

def Disposition.transport (q : Nat → Nat) (post : Key → Nat) : Disposition → Disposition
  | .expanded body => .expanded (body.transport q post)
  | .returned body => .returned (body.transport q post)
  | state => state

structure Graph where
  q : Nat → Nat := id
  vertices : List Key := []
  status : Key → Disposition := fun _ => .retained
  fibers : List Fiber := []
  paths : List (Key × Key) := []

def BoundCurrent (g : Graph) (key : Key) (fiber : Fiber) : Prop :=
  fiber ∈ g.fibers ∧ fiber.bound.pair = currentPair g.q key ∧
  fiber.key.lower = fiber.bound.pair.1 ∧ fiber.key.upper = fiber.bound.pair.2 ∧
  fiber.key.sources = key.sources ∧ fiber.key.transformer = key.transformer ∧
  DependencyPath g.paths key fiber.key

def BodyCurrent (tables : Effect.Tables) (g : Graph) (key : Key) : Body → Prop
  | .localReturn => LocalReturn tables g.q key
  | .children keys => operand tables g.q key = .children (keys.map (currentPair g.q)) ∧
      ∀ child ∈ keys, child ∈ g.vertices
  | .bound fiber => BoundCurrent g key fiber

def DispositionCurrent (tables : Effect.Tables) (g : Graph) (key : Key) : Disposition → Prop
  | .expanded body | .returned body => BodyCurrent tables g key body
  | .retained | .queued | .active => True

def Invariant (tables : Effect.Tables) (g : Graph) : Prop :=
  ∀ key ∈ g.vertices, DispositionCurrent tables g key (g.status key)

def register (g : Graph) (keys : List Key) : Graph :=
  { g with vertices := attachAll keys g.vertices
           status := fun key => if key ∈ g.vertices then g.status key else .retained }

def write (g : Graph) (key : Key) (status : Disposition) : Graph :=
  { g with status := fun other => if other = key then status else g.status other }

@[simp] theorem register_member (g : Graph) (keys : List Key) (key : Key) :
    key ∈ (register g keys).vertices ↔ key ∈ g.vertices ∨ key ∈ keys :=
  mem_attachAll keys g.vertices key

theorem body_register {tables : Effect.Tables} {g : Graph} {key : Key} {body : Body}
    (h : BodyCurrent tables g key body) (keys : List Key) :
    BodyCurrent tables (register g keys) key body := by
  cases body with
  | localReturn => exact h
  | children children => exact ⟨h.1, fun child hc => (register_member _ _ _).mpr (Or.inl (h.2 child hc))⟩
  | bound => exact h

theorem register_invariant {tables : Effect.Tables} {g : Graph}
    (h : Invariant tables g) (keys : List Key) : Invariant tables (register g keys) := by
  intro key member
  by_cases old : key ∈ g.vertices
  · simp only [register, old, ↓reduceIte]
    have prior := h key old
    cases state : g.status key <;> simp only [state, DispositionCurrent] at prior ⊢
    all_goals exact body_register prior keys
  · simp [register, old, DispositionCurrent]

theorem body_write {tables : Effect.Tables} {g : Graph} {key : Key} {body : Body}
    (h : BodyCurrent tables g key body) (target : Key) (state : Disposition) :
    BodyCurrent tables (write g target state) key body := by
  cases body <;> exact h

theorem write_invariant {tables : Effect.Tables} {g : Graph} (h : Invariant tables g)
    (key : Key) (state : Disposition) (valid : DispositionCurrent tables g key state) :
    Invariant tables (write g key state) := by
  intro other member
  by_cases same : other = key
  · subst other
    simp only [write, ↓reduceIte]
    cases state <;> exact valid
  · simp only [write, same, ↓reduceIte]
    have prior := h other member
    cases state : g.status other <;> simp only [state, DispositionCurrent] at prior ⊢ <;> exact prior

def expandChildren (g : Graph) (key : Key) (children : List Key) : Graph :=
  write (register g children) key (.expanded (.children children))

theorem expandChildren_invariant {tables : Effect.Tables} {g : Graph}
    (h : Invariant tables g) (key : Key) (children : List Key)
    (computed : operand tables g.q key = .children (children.map (currentPair g.q))) :
    Invariant tables (expandChildren g key children) := by
  apply write_invariant (register_invariant h children)
  exact ⟨computed, fun child hc => (register_member _ _ _).mpr (Or.inr hc)⟩

def attachBound (g : Graph) (key : Key) (bound : Bound) (context : Nat) : Graph :=
  let fiber := exactFiber bound context key.sources key.transformer
  write { g with fibers := attach fiber g.fibers, paths := g.paths ++ [(key, fiber.key)] }
    key (.expanded (.bound fiber))

theorem attachBound_invariant {tables : Effect.Tables} {g : Graph}
    (h : Invariant tables g) (key : Key) (bound : Bound) (context : Nat)
    (pair : bound.pair = currentPair g.q key) :
    Invariant tables (attachBound g key bound context) := by
  let fiber := exactFiber bound context key.sources key.transformer
  let next := { g with fibers := attach fiber g.fibers, paths := g.paths ++ [(key, fiber.key)] }
  have bodies : ∀ other body, BodyCurrent tables g other body → BodyCurrent tables next other body := by
    intro other body valid
    cases body with
    | localReturn => exact valid
    | children => exact valid
    | bound old =>
        rcases valid with ⟨held, endpoints, lower, upper, sources, transformer, path⟩
        exact ⟨(mem_attach _ _ _).mpr (Or.inl held), endpoints, lower, upper,
          sources, transformer, path.weaken (fun _ he => List.mem_append_left _ he)⟩
  have prior : Invariant tables next := by
    intro other member
    have valid := h other member
    cases state : g.status other <;> simp only [state, DispositionCurrent] at valid ⊢
    all_goals exact bodies other _ valid
  apply write_invariant prior
  refine ⟨(mem_attach _ _ _).mpr (Or.inr rfl), pair, rfl, rfl, rfl, rfl, ?_⟩
  exact .step (List.mem_append_right _ (by simp [fiber])) (.refl _)

def mergeGraph (g : Graph) (copyInputs : List Bound) (target parentIndex : Nat)
    (q : Nat → Nat) (post : Key → Nat) : Graph :=
  { g with q := q
           status := fun key => (g.status key).transport q post
           fibers := merge copyInputs target parentIndex q post g.fibers
           paths := g.paths ++ mergeEdges copyInputs target parentIndex q post g.fibers }

theorem carrier_exact_endpoints (q : Nat → Nat) (post : Key → Nat) (fiber : Fiber)
    (lower : fiber.key.lower = fiber.bound.pair.1)
    (upper : fiber.key.upper = fiber.bound.pair.2) :
    (carrier q post fiber).key.lower = (carrier q post fiber).bound.pair.1 ∧
    (carrier q post fiber).key.upper = (carrier q post fiber).bound.pair.2 := by
  by_cases same : renameBound q fiber.bound = fiber.bound
  · simpa [carrier, same] using And.intro lower upper
  · simp [carrier, same, transport, exactFiber]

theorem bound_current_merge {g : Graph} {key : Key} {fiber : Fiber}
    (h : BoundCurrent g key fiber) (copyInputs : List Bound) (target parentIndex : Nat)
    (q : Nat → Nat) (post : Key → Nat) (absorbs : ∀ row, q (g.q row) = q row) :
    BoundCurrent (mergeGraph g copyInputs target parentIndex q post) key (carrier q post fiber) := by
  rcases h with ⟨held, pair, lower, upper, sources, transformer, path⟩
  have retained := copy_retains copyInputs target parentIndex post g.fibers fiber held
  have route := canonical_carrier_path q post _ fiber retained
  have payload := carrier_payload q post fiber
  have endpoints := carrier_exact_endpoints q post fiber lower upper
  refine ⟨canonical_carrier q post _ fiber retained, ?_, endpoints.1, endpoints.2,
    payload.1.trans sources, payload.2.1.trans transformer, ?_⟩
  · rw [carrier_bound, bound_pair_rename, pair]
    exact currentPair_absorb g.q q absorbs key
  · apply dependencyPath_trans (path.weaken (fun _ he => List.mem_append_left _ he))
    exact route.weaken (fun _ he => List.mem_append_right _ (List.mem_append_right _ he))

theorem body_current_merge {tables : Effect.Tables} {g : Graph} {key : Key} {body : Body}
    (h : BodyCurrent tables g key body) (copyInputs : List Bound) (target parentIndex : Nat)
    (q : Nat → Nat) (post : Key → Nat) (absorbs : ∀ row, q (g.q row) = q row) :
    BodyCurrent tables (mergeGraph g copyInputs target parentIndex q post) key
      (body.transport q post) := by
  cases body with
  | localReturn => exact localReturn_transport tables g.q q absorbs key h
  | children children =>
      refine ⟨?_, h.2⟩
      change operand tables q key = .children (children.map (currentPair q))
      rw [operand_transport tables g.q q absorbs, h.1]
      simp only [Effect.renameOutcome, List.map_map]
      congr 1
      apply List.map_congr_left
      intro child _
      exact currentPair_absorb g.q q absorbs child
  | bound fiber => exact bound_current_merge h copyInputs target parentIndex q post absorbs

theorem merge_invariant {tables : Effect.Tables} {g : Graph} (h : Invariant tables g)
    (copyInputs : List Bound) (target parentIndex : Nat) (q : Nat → Nat) (post : Key → Nat)
    (absorbs : ∀ row, q (g.q row) = q row) :
    Invariant tables (mergeGraph g copyInputs target parentIndex q post) := by
  intro key member
  have valid := h key member
  cases state : g.status key <;>
    simp only [mergeGraph, state, Disposition.transport, DispositionCurrent] at valid ⊢
  all_goals exact body_current_merge valid copyInputs target parentIndex q post absorbs


/-- A current frontier is a present graph owner, not an admission/completion bit. -/
def Frontier (g : Graph) (key : Key) : Prop :=
  g.status key = .retained ∨ g.status key = .queued ∨ g.status key = .active

/-- The finite-depth consumer is independent of `Invariant` and of a stored
child-closure proof. Every recursive step rereads the current operand equation.
Bound leaves retain their exact current fiber and original-parent path. -/
def CurrentAt (tables : Effect.Tables) (g : Graph) : Nat → Key → Prop
  | 0, key => key ∈ g.vertices
  | depth + 1, key => key ∈ g.vertices ∧
      (Frontier g key ∨ (∃ fiber, BoundCurrent g key fiber) ∨
        LocalReturn tables g.q key ∨
        ∃ (children : List Key), operand tables g.q key = .children (children.map (currentPair g.q)) ∧
          ∀ child ∈ children, CurrentAt tables g depth child)

theorem invariant_all_depths {tables : Effect.Tables} {g : Graph}
    (h : Invariant tables g) (depth : Nat) :
    ∀ key ∈ g.vertices, CurrentAt tables g depth key := by
  induction depth with
  | zero => exact fun _ member => member
  | succ depth ih =>
      intro key member
      refine ⟨member, ?_⟩
      have valid := h key member
      cases state : g.status key with
      | retained => exact Or.inl (Or.inl state)
      | queued => exact Or.inl (Or.inr (Or.inl state))
      | active => exact Or.inl (Or.inr (Or.inr state))
      | expanded body | returned body =>
          simp only [state, DispositionCurrent] at valid
          cases body with
          | localReturn => exact Or.inr (Or.inr (Or.inl valid))
          | children children =>
              exact Or.inr (Or.inr (Or.inr ⟨children, valid.1,
                fun child hc => ih child (valid.2 child hc)⟩))
          | bound fiber => exact Or.inr (Or.inl ⟨fiber, valid⟩)

def isFrontier : Disposition → Bool
  | .retained | .queued | .active => true
  | .expanded _ | .returned _ => false

/-- Computed finite list of still-unexpanded owners. This is not the native
worklist: retained Replay and active frame owners are included separately. -/
def unfinished (g : Graph) : List Key := g.vertices.filter (fun key => isFrontier (g.status key))

theorem frontier_mem_unfinished (g : Graph) (key : Key) (member : key ∈ g.vertices) :
    Frontier g key ↔ key ∈ unfinished g := by
  cases state : g.status key <;> simp [Frontier, unfinished, state, isFrontier, member]

/-- Closed operand expansion modulo concrete retained row obligations. This
does not interpret a retained row obligation as already semantically solved. -/
def ClosedAt (tables : Effect.Tables) (g : Graph) : Nat → Key → Prop
  | 0, key => key ∈ g.vertices
  | depth + 1, key => key ∈ g.vertices ∧
      ((∃ fiber, BoundCurrent g key fiber) ∨ LocalReturn tables g.q key ∨
        ∃ (children : List Key), operand tables g.q key = .children (children.map (currentPair g.q)) ∧
          ∀ child ∈ children, ClosedAt tables g depth child)

theorem no_frontier_all_depths {tables : Effect.Tables} {g : Graph}
    (h : Invariant tables g) (drained : unfinished g = []) (depth : Nat) :
    ∀ key ∈ g.vertices, ClosedAt tables g depth key := by
  induction depth with
  | zero => exact fun _ member => member
  | succ depth ih =>
      intro key member
      refine ⟨member, ?_⟩
      have notFrontier : ¬ Frontier g key := by
        intro frontier
        have found := (frontier_mem_unfinished g key member).mp frontier
        rw [drained] at found
        exact List.not_mem_nil found
      have valid := h key member
      cases state : g.status key with
      | retained => exact False.elim (notFrontier (Or.inl state))
      | queued => exact False.elim (notFrontier (Or.inr (Or.inl state)))
      | active => exact False.elim (notFrontier (Or.inr (Or.inr state)))
      | expanded body | returned body =>
          simp only [state, DispositionCurrent] at valid
          cases body with
          | localReturn => exact Or.inr (Or.inl valid)
          | children children =>
              exact Or.inr (Or.inr ⟨children, valid.1, fun child hc => ih child (valid.2 child hc)⟩)
          | bound fiber => exact Or.inl ⟨fiber, valid⟩

/-- An unfinished closed claim has a concrete finite owner-list falsifier;
an empty queue alone does not discharge this list. -/
theorem unfinished_witness (g : Graph) (notEmpty : unfinished g ≠ []) :
    ∃ key, key ∈ g.vertices ∧ Frontier g key := by
  obtain ⟨key, member⟩ := List.exists_mem_of_ne_nil _ notEmpty
  have own := (List.mem_filter.mp member).1
  exact ⟨key, own, (frontier_mem_unfinished g key own).mpr member⟩

structure State where
  replay : Replay.State Nat := {}
  graph : Graph := {}

/-- `keyOf` is the exact child interning constructor for ONE fixed ordered pair
of physical BoundKeys. Its argument keeps both complete attached relation IDs.
Its payload includes stored Context, source set and full Effect transformer. -/
inductive Step (tables : Effect.Tables) (keyOf : Nat × Nat → Key) : State → State → Prop
  | lower (s : State) (fiber : Nat) :
      Step tables keyOf s { s with replay := Replay.step s.replay (.lower fiber) }
  | upper (s : State) (fiber : Nat) :
      Step tables keyOf s { s with replay := Replay.step s.replay (.upper fiber) }
  | replay (s : State) (incoming : Bool) :
      Step tables keyOf s
        { replay := Replay.step s.replay (.replay incoming)
          graph := register s.graph ((Replay.children s.replay incoming).map keyOf) }
  /-- Erasure of successful Replay creation by another physical input pair.
The whole native graph is shared; only this selected generator's heads are local. -/
  | external (s : State) (keys : List Key) :
      Step tables keyOf s { s with graph := register s.graph keys }
  | queue (s : State) (key : Key) (member : key ∈ s.graph.vertices)
      (retained : s.graph.status key = .retained) :
      Step tables keyOf s { s with graph := write s.graph key .queued }
  | activate (s : State) (key : Key) (member : key ∈ s.graph.vertices)
      (queued : s.graph.status key = .queued) :
      Step tables keyOf s { s with graph := write s.graph key .active }
  | localReturn (s : State) (key : Key) (member : key ∈ s.graph.vertices)
      (active : s.graph.status key = .active)
      (computed : operand tables s.graph.q key = .localReturn) :
      Step tables keyOf s { s with graph := write s.graph key (.expanded .localReturn) }
  | reflexive (s : State) (key : Key) (member : key ∈ s.graph.vertices)
      (active : s.graph.status key = .active)
      (same : (currentPair s.graph.q key).1 = (currentPair s.graph.q key).2)
      (identity : key.transformer = 0) :
      Step tables keyOf s { s with graph := write s.graph key (.expanded .localReturn) }
  | children (s : State) (key : Key) (children : List Key) (member : key ∈ s.graph.vertices)
      (active : s.graph.status key = .active)
      (computed : operand tables s.graph.q key = .children (children.map (currentPair s.graph.q))) :
      Step tables keyOf s { s with graph := expandChildren s.graph key children }
  | bound (s : State) (key : Key) (bound : Bound) (context : Nat)
      (member : key ∈ s.graph.vertices) (active : s.graph.status key = .active)
      (pair : bound.pair = currentPair s.graph.q key) :
      Step tables keyOf s { s with graph := attachBound s.graph key bound context }
  /-- An erased successful terminal event for this expansion owner. It never
acknowledges a newly registered occurrence sharing the same relation key. The
actual ordered ack/ReturnReady association must be read back from one execution. -/
  | returned (s : State) (key : Key) (body : Body) (member : key ∈ s.graph.vertices)
      (expanded : s.graph.status key = .expanded body) :
      Step tables keyOf s { s with graph := write s.graph key (.returned body) }
  | merge (s : State) (copyInputs : List Bound) (target parentIndex : Nat)
      (q : Nat → Nat) (post : Key → Nat) (absorbs : ∀ row, q (s.graph.q row) = q row) :
      Step tables keyOf s { s with graph := mergeGraph s.graph copyInputs target parentIndex q post }

structure Accounted (tables : Effect.Tables) (keyOf : Nat × Nat → Key) (s : State) : Prop where
  origins : Replay.OriginInvariant s.replay
  current : Invariant tables s.graph
  roots : ∀ batch ∈ s.replay.operations, ∀ pair ∈ batch, keyOf pair ∈ s.graph.vertices

theorem initial_accounted (tables : Effect.Tables) (keyOf : Nat × Nat → Key) :
    Accounted tables keyOf ({} : State) := by
  constructor
  · exact Replay.initial_origins
  · intro key h; cases h
  · intro batch h; cases h

theorem step_accounted {tables : Effect.Tables} {keyOf : Nat × Nat → Key} {s u : State}
    (step : Step tables keyOf s u) (h : Accounted tables keyOf s) : Accounted tables keyOf u := by
  rcases h with ⟨origins, current, roots⟩
  cases step with
  | lower fiber =>
      refine ⟨Replay.step_origins origins (.lower fiber), ?_, ?_⟩
      · exact current
      · simp only [Replay.step]; split <;> exact roots
  | upper fiber =>
      refine ⟨Replay.step_origins origins (.upper fiber), ?_, ?_⟩
      · exact current
      · simp only [Replay.step]; split <;> exact roots
  | replay incoming =>
      refine ⟨Replay.step_origins origins (.replay incoming), register_invariant current _, ?_⟩
      intro batch member pair present
      change batch ∈ s.replay.operations ++ [Replay.children s.replay incoming] at member
      rcases List.mem_append.mp member with old | fresh
      · exact (register_member _ _ _).mpr (Or.inl (roots batch old pair present))
      · have same := List.mem_singleton.mp fresh
        subst batch
        exact (register_member _ _ _).mpr (Or.inr (List.mem_map.mpr ⟨pair, present, rfl⟩))
  | external keys =>
      refine ⟨origins, register_invariant current keys, ?_⟩
      intro batch member pair present
      exact (register_member _ _ _).mpr (Or.inl (roots batch member pair present))
  | queue key member retained =>
      exact ⟨origins, write_invariant current key .queued trivial, roots⟩
  | activate key member queued =>
      exact ⟨origins, write_invariant current key .active trivial, roots⟩
  | localReturn key member active computed =>
      exact ⟨origins, write_invariant current key (.expanded .localReturn) (Or.inl computed), roots⟩
  | reflexive key member active same identity =>
      exact ⟨origins, write_invariant current key (.expanded .localReturn) (Or.inr ⟨same, identity⟩), roots⟩
  | children key children member active computed =>
      refine ⟨origins, expandChildren_invariant current key children computed, ?_⟩
      intro batch member pair present
      exact (register_member _ _ _).mpr (Or.inl (roots batch member pair present))
  | bound key bound context member active pair =>
      exact ⟨origins, attachBound_invariant current key bound context pair, roots⟩
  | returned key body member expanded =>
      have valid := current key member
      simp only [expanded, DispositionCurrent] at valid
      exact ⟨origins, write_invariant current key (.returned body) valid, roots⟩
  | merge copyInputs target parentIndex q post absorbs =>
      exact ⟨origins, merge_invariant current copyInputs target parentIndex q post absorbs, roots⟩

inductive Reachable (tables : Effect.Tables) (keyOf : Nat × Nat → Key) : State → Prop
  | initial : Reachable tables keyOf {}
  | step {s u} : Reachable tables keyOf s → Step tables keyOf s u → Reachable tables keyOf u

theorem reachable_accounted {tables : Effect.Tables} {keyOf : Nat × Nat → Key} {s : State}
    (h : Reachable tables keyOf s) : Accounted tables keyOf s := by
  induction h with
  | initial => exact initial_accounted tables keyOf
  | step _ step ih => exact step_accounted step ih

/-- Historical creation is now connected to a CURRENT recursively unfoldable
finite graph. The graph invariant is derived from empty and explicit events. -/
theorem historical_child_current {tables : Effect.Tables} {keyOf : Nat × Nat → Key} {s : State}
    (h : Reachable tables keyOf s) {operation index : Nat} {batch : List (Nat × Nat)} {pair : Nat × Nat}
    (owner : s.replay.operations[operation]? = some batch) (child : batch[index]? = some pair) :
    ∀ depth, CurrentAt tables s.graph depth (keyOf pair) := by
  have inv := reachable_accounted h
  have root := inv.roots batch (List.mem_of_getElem? owner) pair (List.mem_of_getElem? child)
  exact fun depth => invariant_all_depths inv.current depth _ root

theorem dependency_skip_current {tables : Effect.Tables} {keyOf : Nat × Nat → Key} {s : State}
    (h : Reachable tables keyOf s) {pair : Nat × Nat} (seen : pair ∈ s.replay.dependencies) :
    pair ∉ Replay.children s.replay false ∧
      ∀ depth, CurrentAt tables s.graph depth (keyOf pair) := by
  have inv := reachable_accounted h
  obtain ⟨batch, owner, child⟩ := (inv.origins.dependencyOrigin pair).mp seen
  exact ⟨by simp [Replay.children, seen], fun depth =>
    invariant_all_depths inv.current depth _ (inv.roots batch owner pair child)⟩

theorem old_old_current {tables : Effect.Tables} {keyOf : Nat × Nat → Key} {s : State}
    (h : Reachable tables keyOf s) {pair : Nat × Nat}
    (old : pair ∈ product s.replay.oldLower s.replay.oldUpper) :
    ∀ depth, CurrentAt tables s.graph depth (keyOf pair) :=
  (dependency_skip_current h ((reachable_accounted h).origins.oldProduct pair old)).2

theorem fired_product_current {tables : Effect.Tables} {keyOf : Nat × Nat → Key} {s : State}
    (h : Reachable tables keyOf s) (incoming : Bool) (lower upper : Nat)
    (present : (lower, upper) ∈ product s.replay.lower s.replay.upper) :
    let next : State :=
      { replay := Replay.step s.replay (.replay incoming)
        graph := register s.graph ((Replay.children s.replay incoming).map keyOf) }
    ∀ depth, CurrentAt tables next.graph depth (keyOf (lower, upper)) := by
  have next := Reachable.step h (Step.replay s incoming)
  have retained := Replay.replay_retains_all_products (reachable_accounted h).origins incoming lower upper present
  exact (dependency_skip_current next retained).2

/-- Empty concrete frontier eliminates *all* pending cases at every depth.
The remaining leaves are actual current bound carriers, not a completed bit. -/
theorem historical_child_closed {tables : Effect.Tables} {keyOf : Nat × Nat → Key} {s : State}
    (h : Reachable tables keyOf s) (drained : unfinished s.graph = [])
    {operation index : Nat} {batch : List (Nat × Nat)} {pair : Nat × Nat}
    (owner : s.replay.operations[operation]? = some batch) (child : batch[index]? = some pair) :
    ∀ depth, ClosedAt tables s.graph depth (keyOf pair) := by
  have inv := reachable_accounted h
  have root := inv.roots batch (List.mem_of_getElem? owner) pair (List.mem_of_getElem? child)
  exact fun depth => no_frontier_all_depths inv.current drained depth _ root

/-- Pending acknowledgements and repeated merges cannot erase a queued owner. -/
theorem merge_queued (g : Graph) (key : Key) (queued : g.status key = .queued)
    (copyInputs : List Bound) (target parentIndex : Nat) (q : Nat → Nat) (post : Key → Nat) :
    (mergeGraph g copyInputs target parentIndex q post).status key = .queued := by
  simp [mergeGraph, queued, Disposition.transport]

theorem register_active_backreference (g : Graph) (key : Key) (member : key ∈ g.vertices)
    (active : g.status key = .active) (children : List Key) :
    (register g children).status key = .active ∧ key ∈ (register g children).vertices := by
  exact ⟨by simp [register, member, active], (register_member _ _ _).mpr (Or.inl member)⟩


/-- Edges are installed local expansions, including edges back to the same
registered owner. No rank, topological ordering, or acyclicity is required. -/
inductive Walk (g : Graph) : Key → Nat → Key → Prop
  | refl (key : Key) : Walk g key 0 key
  | step {first child last : Key} {length : Nat} {children : List Key}
      (expanded : g.status first = .expanded (.children children) ∨
        g.status first = .returned (.children children))
      (member : child ∈ children) (rest : Walk g child length last) :
      Walk g first (length + 1) last

/-- Failure at a finite expansion depth produces an actual installed-edge path
to a retained/queued/active owner, shorter than that depth. This is a precise
remaining source readback target, not a recursively current-children premise. -/
theorem missing_depth_has_frontier {tables : Effect.Tables} {g : Graph}
    (h : Invariant tables g) (depth : Nat) : ∀ key ∈ g.vertices,
    ¬ ClosedAt tables g depth key →
      ∃ last length, length < depth ∧ Walk g key length last ∧
        last ∈ g.vertices ∧ Frontier g last := by
  classical
  induction depth with
  | zero =>
      intro key member absent
      exact False.elim (absent member)
  | succ depth ih =>
      intro key member absent
      have valid := h key member
      have pending (frontier : Frontier g key) :
          ∃ last length, length < depth + 1 ∧ Walk g key length last ∧
            last ∈ g.vertices ∧ Frontier g last :=
        ⟨key, 0, Nat.zero_lt_succ _, .refl key, member, frontier⟩
      cases state : g.status key with
      | retained => exact pending (Or.inl state)
      | queued => exact pending (Or.inr (Or.inl state))
      | active => exact pending (Or.inr (Or.inr state))
      | expanded body | returned body =>
          simp only [state, DispositionCurrent] at valid
          cases body with
          | localReturn => exact False.elim (absent ⟨member, Or.inr (Or.inl valid)⟩)
          | bound fiber => exact False.elim (absent ⟨member, Or.inl ⟨fiber, valid⟩⟩)
          | children children =>
              have bad : ∃ child, child ∈ children ∧ ¬ ClosedAt tables g depth child := by
                apply Classical.byContradiction
                intro none
                apply absent
                refine ⟨member, Or.inr (Or.inr ⟨children, valid.1, ?_⟩)⟩
                intro child hc
                apply Classical.byContradiction
                intro failure
                exact none ⟨child, hc, failure⟩
              obtain ⟨child, selected, failure⟩ := bad
              obtain ⟨last, length, bound, route, present, frontier⟩ :=
                ih child (valid.2 child selected) failure
              refine ⟨last, length + 1, Nat.succ_lt_succ bound, ?_, present, frontier⟩
              apply Walk.step (children := children) (child := child) _ selected route
              first | exact Or.inl state | exact Or.inr state

theorem historical_child_closed_or_frontier {tables : Effect.Tables}
    {keyOf : Nat × Nat → Key} {s : State} (h : Reachable tables keyOf s)
    {operation index : Nat} {batch : List (Nat × Nat)} {pair : Nat × Nat}
    (owner : s.replay.operations[operation]? = some batch) (child : batch[index]? = some pair)
    (depth : Nat) :
    ClosedAt tables s.graph depth (keyOf pair) ∨
      ∃ last length, length < depth ∧ Walk s.graph (keyOf pair) length last ∧
        last ∈ unfinished s.graph := by
  classical
  by_cases closed : ClosedAt tables s.graph depth (keyOf pair)
  · exact Or.inl closed
  · have inv := reachable_accounted h
    have root := inv.roots batch (List.mem_of_getElem? owner) pair (List.mem_of_getElem? child)
    obtain ⟨last, length, bound, route, present, frontier⟩ :=
      missing_depth_has_frontier inv.current depth _ root closed
    exact Or.inr ⟨last, length, bound, route,
      (frontier_mem_unfinished s.graph last present).mp frontier⟩

theorem walk_merge {g : Graph} {first last : Key} {length : Nat}
    (route : Walk g first length last) (copyInputs : List Bound) (target parentIndex : Nat)
    (q : Nat → Nat) (post : Key → Nat) :
    Walk (mergeGraph g copyInputs target parentIndex q post) first length last := by
  induction route with
  | refl key => exact .refl key
  | step expanded selected rest ih =>
      apply Walk.step (member := selected) (rest := ih)
      rcases expanded with expanded | returned
      · exact Or.inl (by simp [mergeGraph, expanded, Disposition.transport, Body.transport])
      · exact Or.inr (by simp [mergeGraph, returned, Disposition.transport, Body.transport])

/-- The native level rule CONSTRUCTS the retained residual owner; no bound
existence or completed replay premise is supplied. The context is the actual
post-Context residual ID, not asserted equal to the original stored ID. -/
theorem row_residual_step {tables : Effect.Tables} {keyOf : Nat × Nat → Key} {s : State}
    (h : Reachable tables keyOf s) (key : Key) (member : key ∈ s.graph.vertices)
    (active : s.graph.status key = .active) (levels : Nat → Nat)
    (owner : Nat) (upper : Endpoint) (pair : currentPair s.graph.q key = (.row owner, upper))
    (different : upper ≠ .row owner) (residualContext : Nat) :
    ∃ bound, residualBound levels owner upper = some bound ∧
      Step tables keyOf s { s with graph := attachBound s.graph key bound residualContext } ∧
      Invariant tables (attachBound s.graph key bound residualContext) := by
  obtain ⟨bound, computed, endpoints⟩ := residual_bound_constructed levels owner upper different
  have shape : bound.pair = currentPair s.graph.q key := endpoints.trans pair.symm
  exact ⟨bound, computed, Step.bound s key bound residualContext member active shape,
    attachBound_invariant (reachable_accounted h).current key bound residualContext shape⟩


/-- Raw immutable table readback for `candidate_context_source`: a view's
closed weight selects its already-interned PrefixLeft(weight,Identity) ID.
No semantic interpretation or context equality is assumed by these tables. -/
structure AdmissionTables where
  closedWeight : Nat → Option Nat
  prefixIdentity : Nat → Nat

def sourceContext (tables : AdmissionTables) : Endpoint → Nat
  | .allowance view => (tables.closedWeight view).map tables.prefixIdentity |>.getD 0
  | _ => 0

theorem sourceContext_rename (tables : AdmissionTables) (q : Nat → Nat) (upper : Endpoint) :
    sourceContext tables (renameEndpoint q upper) = sourceContext tables upper := by
  cases upper <;> rfl

/-- Exact same-kind Effect `enqueue_task -> candidate_context_admit -> relation`
payload: child-local Context, processing-parent sources and complete transformer.
It is NOT the parent's stored Context or its post-check residual Context. -/
def admittedChild (tables : AdmissionTables) (q : Nat → Nat) (parent : Key) (pair : Pair) : Key :=
  ⟨renameEndpoint q pair.1, renameEndpoint q pair.2,
    sourceContext tables pair.2, parent.sources, parent.transformer⟩

theorem admitted_child_payload (tables : AdmissionTables) (q : Nat → Nat)
    (parent : Key) (pair : Pair) :
    (admittedChild tables q parent pair).context = sourceContext tables pair.2 ∧
    (admittedChild tables q parent pair).sources = parent.sources ∧
    (admittedChild tables q parent pair).transformer = parent.transformer := ⟨rfl, rfl, rfl⟩

theorem admitted_child_current_pair (tables : AdmissionTables) (q : Nat → Nat)
    (idempotent : ∀ row, q (q row) = q row) (parent : Key) (pair : Pair) :
    currentPair q (admittedChild tables q parent pair) = Effect.renamePair q pair := by
  simp [currentPair, admittedChild, Effect.renamePair, renameEndpoint_absorb q q idempotent]

theorem operand_children_canonical (tables : Effect.Tables) (q : Nat → Nat)
    (idempotent : ∀ row, q (q row) = q row) (key : Key) (pairs : List Pair)
    (computed : operand tables q key = .children pairs) :
    pairs.map (Effect.renamePair q) = pairs := by
  have same := operand_transport tables q q idempotent key
  rw [computed] at same
  exact (Effect.Outcome.children.inj same).symm

/-- Full child keys are computed from the actual local constructor and tables,
then registered automatically. This theorem does not take a child-currentness
or child-closure hypothesis and does not use the pair-admission memo. -/
theorem concrete_operand_children {tables : Effect.Tables} {keyOf : Nat × Nat → Key} {s : State}
    (h : Reachable tables keyOf s) (admission : AdmissionTables)
    (idempotent : ∀ row, s.graph.q (s.graph.q row) = s.graph.q row)
    (key : Key) (member : key ∈ s.graph.vertices) (active : s.graph.status key = .active)
    (pairs : List Pair) (computed : operand tables s.graph.q key = .children pairs) :
    let children := pairs.map (admittedChild admission s.graph.q key)
    let next := { s with graph := expandChildren s.graph key children }
    Step tables keyOf s next ∧ Reachable tables keyOf next ∧
      (∀ child ∈ children, child.context = sourceContext admission child.upper ∧
        child.sources = key.sources ∧ child.transformer = key.transformer) ∧
      ∀ depth, CurrentAt tables next.graph depth key := by
  let children := pairs.map (admittedChild admission s.graph.q key)
  have shape : operand tables s.graph.q key = .children (children.map (currentPair s.graph.q)) := by
    rw [computed]
    have normal := operand_children_canonical tables s.graph.q idempotent key pairs computed
    congr 1
    dsimp [children]
    rw [List.map_map]
    calc
      pairs = pairs.map (Effect.renamePair s.graph.q) := normal.symm
      _ = pairs.map (fun pair => currentPair s.graph.q (admittedChild admission s.graph.q key pair)) := by
        apply List.map_congr_left
        intro pair _
        exact (admitted_child_current_pair admission s.graph.q idempotent key pair).symm
  have step := Step.children (keyOf := keyOf) s key children member active shape
  have next := Reachable.step h step
  refine ⟨step, next, ?_, ?_⟩
  · intro child present
    obtain ⟨pair, selected, same⟩ := List.mem_map.mp present
    subst child
    simp [admittedChild, sourceContext_rename]
  · intro depth
    apply invariant_all_depths (reachable_accounted next).current depth
    exact (register_member _ _ _).mpr (Or.inl member)

end YulangClosure.NativeReplayCurrent
