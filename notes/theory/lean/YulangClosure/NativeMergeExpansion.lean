import YulangClosure.NativeReplayCoverage

/-!
Constructive components of MERGE-EXPANSION-COVER-1.

`canonicalize` is the frozen-prefix incidence scan: duplicate attachments are
elided, every changed bound gets its post-check relation and a transport event.
`merge` retains source storage, copies fibers selected by the addressed physical bounds, then scans the whole
prefix. `run` implements the two actual Replay quadrants and the independent
dependency skip, and derives indexed HISTORICAL operation ownership from empty.

The erased keys below retain exact rigid IDs, context/source IDs and the Effect
transformer. They do not interpret contexts or effects. Authentication of this
projection against one native execution, recursive current expansion validity,
diagnostics and the actual drain/ack return are separate OPEN obligations.
In particular, no admission memo is a completion certificate here.
-/
namespace YulangClosure.NativeMergeExpansion

open NativeReplayCoverage (product mem_product replayDelta replay_quadrants_cover)

def attach [DecidableEq α] (item : α) (items : List α) : List α :=
  if item ∈ items then items else items ++ [item]

@[simp] theorem mem_attach [DecidableEq α] (item value : α) (items : List α) :
    value ∈ attach item items ↔ value ∈ items ∨ value = item := by
  by_cases present : item ∈ items
  · simp only [attach, present, ↓reduceIte]
    constructor
    · exact Or.inl
    · rintro (h | rfl)
      · exact h
      · exact present
  · simp [attach, present]

def attachAll [DecidableEq α] : List α → List α → List α
  | [], prior => prior
  | item :: rest, prior => attachAll rest (attach item prior)

@[simp] theorem mem_attachAll [DecidableEq α] (added prior : List α) (value : α) :
    value ∈ attachAll added prior ↔ value ∈ prior ∨ value ∈ added := by
  induction added generalizing prior with
  | nil => simp [attachAll]
  | cons item rest ih =>
      simp only [attachAll, ih, mem_attach, List.mem_cons]
      exact or_assoc

inductive Endpoint where
  | row (id : Nat)
  | allowance (view : Nat)
  | support (view : Nat)
  | contribution (id : Nat)
  | annotationMember (view member : Nat)
  | bottom
  | emptyNegative
  deriving DecidableEq, Repr

def renameEndpoint (q : Nat → Nat) : Endpoint → Endpoint
  | .row id => .row (q id)
  | rigid => rigid

inductive Polarity where
  | positive | negative
  deriving DecidableEq, Repr

structure Bound where
  owner : Nat
  polarity : Polarity
  endpoint : Endpoint
  deriving DecidableEq, Repr

def Bound.pair (bound : Bound) : Endpoint × Endpoint :=
  match bound.polarity with
  | .positive => (bound.endpoint, .row bound.owner)
  | .negative => (.row bound.owner, bound.endpoint)

def renameBound (q : Nat → Nat) (bound : Bound) : Bound :=
  ⟨q bound.owner, bound.polarity, renameEndpoint q bound.endpoint⟩

theorem renameEndpoint_absorb (old current : Nat → Nat)
    (absorbs : ∀ row, current (old row) = current row) (endpoint : Endpoint) :
    renameEndpoint current (renameEndpoint old endpoint) = renameEndpoint current endpoint := by
  cases endpoint <;> simp [renameEndpoint, absorbs]

theorem renameBound_absorb (old current : Nat → Nat)
    (absorbs : ∀ row, current (old row) = current row) (bound : Bound) :
    renameBound current (renameBound old bound) = renameBound current bound := by
  simp [renameBound, absorbs, renameEndpoint_absorb old current absorbs]

theorem bound_pair_rename (q : Nat → Nat) (bound : Bound) :
    (renameBound q bound).pair =
      (renameEndpoint q bound.pair.1, renameEndpoint q bound.pair.2) := by
  rcases bound with ⟨owner, polarity, endpoint⟩
  cases polarity <;> rfl

/-- A same-kind Effect fiber has no deferred Function demand. The transformer
and source-set IDs are retained, not interpreted or replaced by default IDs. -/
structure Key where
  lower : Endpoint
  upper : Endpoint
  context : Nat
  sources : Option Nat
  transformer : Nat
  deriving DecidableEq, Repr

structure Fiber where
  bound : Bound
  key : Key
  deriving DecidableEq, Repr

def exactFiber (bound : Bound) (context : Nat) (sources : Option Nat)
    (transformer : Nat) : Fiber :=
  ⟨bound, bound.pair.1, bound.pair.2, context, sources, transformer⟩

def allowanceFiber (owner view : Nat) (sources : Option Nat) (transformer : Nat) : Fiber :=
  exactFiber ⟨owner, .negative, .allowance view⟩ 0 sources transformer

structure Discharge where
  parent : Key
  filters : List Nat
  residual : Nat
  deriving DecidableEq, Repr

/-- Projection of successful publication, after the callback for every filter.
Identity and empty-filter Context executions do not publish discharge. Parser
authentication and callback execution are not concluded from this projection. -/
def publish (event : Discharge) (prior : List (Key × Nat)) : List (Key × Nat) :=
  if event.parent.context = 0 ∨ event.filters = [] then prior
  else (event.parent, event.residual) :: prior

def publications : List Discharge → List (Key × Nat) → List (Key × Nat)
  | [], prior => prior
  | event :: rest, prior => publications rest (publish event prior)

def postCheck : List (Key × Nat) → Key → Nat
  | [], key => key.context
  | (parent, residual) :: rest, key =>
      if parent = key then residual else postCheck rest key

theorem identity_publication_unchanged (event : Discharge) (prior : List (Key × Nat))
    (key : Key) (identity : key.context = 0) :
    postCheck (publish event prior) key = postCheck prior key := by
  unfold publish
  split
  · rfl
  · rename_i allowed
    have different : event.parent ≠ key := by
      intro same
      exact allowed (Or.inl (same ▸ identity))
    simp [postCheck, different]

theorem identity_publications_unchanged (events : List Discharge)
    (prior : List (Key × Nat)) (key : Key) (identity : key.context = 0) :
    postCheck (publications events prior) key = postCheck prior key := by
  induction events generalizing prior with
  | nil => rfl
  | cons event rest ih =>
      exact (ih (publish event prior)).trans
        (identity_publication_unchanged event prior key identity)

theorem identity_postCheck (events : List Discharge) (key : Key)
    (identity : key.context = 0) :
    postCheck (publications events []) key = 0 :=
  (identity_publications_unchanged events [] key identity).trans identity

def transport (post : Key → Nat) (fiber : Fiber) (target : Bound) : Fiber :=
  exactFiber target (post fiber.key) fiber.key.sources fiber.key.transformer

inductive TransportReason where
  | parentCopy (parentIndex : Nat)
  | equalityCanonicalization
  deriving DecidableEq, Repr

structure Move where
  before : Fiber
  after : Fiber
  reason : TransportReason
  deriving DecidableEq, Repr

def canonicalMove (q : Nat → Nat) (post : Key → Nat) (fiber : Fiber) : Option Move :=
  let target := renameBound q fiber.bound
  if target = fiber.bound then none
  else some ⟨fiber, transport post fiber target, .equalityCanonicalization⟩

def canonicalMoves (q : Nat → Nat) (post : Key → Nat) (prior : List Fiber) : List Move :=
  prior.filterMap (canonicalMove q post)

/-- The source scans a frozen count, so newly attached images are not recursively
rescanned in this pass. Interning/attach deduplication does not drop their keys. -/
def canonicalize (q : Nat → Nat) (post : Key → Nat) (prior : List Fiber) : List Fiber :=
  attachAll ((canonicalMoves q post prior).map Move.after) prior

def carrier (q : Nat → Nat) (post : Key → Nat) (fiber : Fiber) : Fiber :=
  if renameBound q fiber.bound = fiber.bound then fiber
  else transport post fiber (renameBound q fiber.bound)

theorem canonical_carrier (q : Nat → Nat) (post : Key → Nat)
    (prior : List Fiber) (fiber : Fiber) (present : fiber ∈ prior) :
    carrier q post fiber ∈ canonicalize q post prior := by
  by_cases same : renameBound q fiber.bound = fiber.bound
  · exact (mem_attachAll _ _ _).mpr (Or.inl (by simpa [carrier, same] using present))
  · apply (mem_attachAll _ _ _).mpr
    right
    apply List.mem_map.mpr
    refine ⟨⟨fiber, transport post fiber (renameBound q fiber.bound),
      .equalityCanonicalization⟩, ?_, ?_⟩
    · exact List.mem_filterMap.mpr ⟨fiber, present, by simp [canonicalMove, same]⟩
    · simp [carrier, same]

theorem changed_carrier_has_transport (q : Nat → Nat) (post : Key → Nat)
    (prior : List Fiber) (fiber : Fiber) (present : fiber ∈ prior)
    (changed : renameBound q fiber.bound ≠ fiber.bound) :
    Move.mk fiber (carrier q post fiber) .equalityCanonicalization ∈
      canonicalMoves q post prior := by
  exact List.mem_filterMap.mpr ⟨fiber, present, by simp [canonicalMove, carrier, changed]⟩

theorem carrier_bound (q : Nat → Nat) (post : Key → Nat) (fiber : Fiber) :
    (carrier q post fiber).bound = renameBound q fiber.bound := by
  by_cases same : renameBound q fiber.bound = fiber.bound
  · simp [carrier, same]
  · simp [carrier, same, transport, exactFiber]

theorem carrier_payload (q : Nat → Nat) (post : Key → Nat) (fiber : Fiber) :
    (carrier q post fiber).key.sources = fiber.key.sources ∧
    (carrier q post fiber).key.transformer = fiber.key.transformer ∧
    (carrier q post fiber).key.context =
      if renameBound q fiber.bound = fiber.bound then fiber.key.context else post fiber.key := by
  by_cases same : renameBound q fiber.bound = fiber.bound <;>
    simp [carrier, same, transport, exactFiber]

theorem allowance_carrier_exact (q : Nat → Nat) (events : List Discharge)
    (owner view : Nat) (sources : Option Nat) (transformer : Nat) :
    carrier q (postCheck (publications events [])) (allowanceFiber owner view sources transformer) =
      allowanceFiber (q owner) view sources transformer := by
  have identity := identity_postCheck events
    (allowanceFiber owner view sources transformer).key rfl
  by_cases same : q owner = owner <;>
    simp [carrier, allowanceFiber, renameBound, renameEndpoint, transport,
      exactFiber, Bound.pair, same] at identity ⊢
  exact identity

def copiedMoves (copyInputs : List Bound) (target parentIndex : Nat) (post : Key → Nat)
    (prior : List Fiber) : List Move :=
  (prior.filter (fun fiber => fiber.bound ∈ copyInputs)).map fun fiber =>
    ⟨fiber, transport post fiber { fiber.bound with owner := target }, .parentCopy parentIndex⟩

def copyFibers (copyInputs : List Bound) (target parentIndex : Nat) (post : Key → Nat)
    (prior : List Fiber) : List Fiber :=
  attachAll ((copiedMoves copyInputs target parentIndex post prior).map Move.after) prior

theorem copy_retains (copyInputs : List Bound) (target parentIndex : Nat) (post : Key → Nat)
    (prior : List Fiber) (fiber : Fiber) (present : fiber ∈ prior) :
    fiber ∈ copyFibers copyInputs target parentIndex post prior :=
  (mem_attachAll _ _ _).mpr (Or.inl present)

theorem copied_origin_has_transport (copyInputs : List Bound) (target parentIndex : Nat) (post : Key → Nat)
    (prior : List Fiber) (fiber : Fiber) (present : fiber ∈ prior)
    (owned : fiber.bound ∈ copyInputs) :
    Move.mk fiber (transport post fiber { fiber.bound with owner := target })
      (.parentCopy parentIndex) ∈ copiedMoves copyInputs target parentIndex post prior := by
  exact List.mem_map.mpr ⟨fiber, List.mem_filter.mpr ⟨present, by simpa using owned⟩, rfl⟩

def merge (copyInputs : List Bound) (target parentIndex : Nat) (q : Nat → Nat) (post : Key → Nat)
    (prior : List Fiber) : List Fiber :=
  canonicalize q post (copyFibers copyInputs target parentIndex post prior)

def installExpansion (owner : Nat) (views : List Nat) (sources : Option Nat)
    (transformer : Nat) (residual : Option Fiber) (prior : List Fiber) : List Fiber :=
  attachAll ((views.map (fun view => allowanceFiber owner view sources transformer)) ++
    residual.toList) prior

/-- The filter carrier is constructed after an arbitrary generation change;
neither a current-completion law nor semantic Allowance preservation is input. -/
theorem merged_expansion_filters (copyInputs : List Bound) (target parentIndex owner : Nat) (q : Nat → Nat)
    (events : List Discharge) (views : List Nat) (sources : Option Nat)
    (transformer : Nat) (residual : Option Fiber) (prior : List Fiber)
    (view : Nat) (selected : view ∈ views) :
    allowanceFiber (q owner) view sources transformer ∈
      merge copyInputs target parentIndex q (postCheck (publications events []))
        (installExpansion owner views sources transformer residual prior) := by
  rw [← allowance_carrier_exact q events owner view sources transformer]
  apply canonical_carrier
  apply copy_retains
  apply (mem_attachAll _ _ _).mpr
  right
  exact List.mem_append_left _ (List.mem_map.mpr ⟨view, selected, rfl⟩)

/-- A residual at any third owner is retained or transported by the same pass.
Its precise post-check context is kept; equality with its old context is absent. -/
theorem merged_expansion_residual (copyInputs : List Bound) (target parentIndex owner : Nat) (q : Nat → Nat)
    (post : Key → Nat) (views : List Nat) (sources : Option Nat)
    (transformer : Nat) (residual : Fiber) (prior : List Fiber) :
    carrier q post residual ∈ merge copyInputs target parentIndex q post
      (installExpansion owner views sources transformer (some residual) prior) := by
  apply canonical_carrier
  apply copy_retains
  apply (mem_attachAll _ _ _).mpr
  right
  exact List.mem_append_right _ (by simp)

/-- Erased dependency paths retain the original parent. They do not assert
that a transported child was re-dispatched or that a path is semantic evidence. -/
inductive DependencyPath (edges : List (Key × Key)) : Key → Key → Prop
  | refl (key : Key) : DependencyPath edges key key
  | step {first next last : Key} (edge : (first, next) ∈ edges)
      (rest : DependencyPath edges next last) : DependencyPath edges first last

theorem DependencyPath.weaken {edges larger : List (Key × Key)} {first last : Key}
    (path : DependencyPath edges first last)
    (included : ∀ edge, edge ∈ edges → edge ∈ larger) : DependencyPath larger first last := by
  induction path with
  | refl key => exact .refl key
  | step edge rest ih => exact .step (included _ edge) ih

def moveEdges (moves : List Move) : List (Key × Key) :=
  moves.map (fun move => (move.before.key, move.after.key))

theorem canonical_carrier_path (q : Nat → Nat) (post : Key → Nat)
    (prior : List Fiber) (fiber : Fiber) (present : fiber ∈ prior) :
    DependencyPath (moveEdges (canonicalMoves q post prior))
      fiber.key (carrier q post fiber).key := by
  by_cases same : renameBound q fiber.bound = fiber.bound
  · simpa [carrier, same] using
      (DependencyPath.refl (edges := moveEdges (canonicalMoves q post prior)) fiber.key)
  · apply DependencyPath.step
    · exact List.mem_map.mpr ⟨_, changed_carrier_has_transport q post prior fiber present same, rfl⟩
    · exact .refl _

def installationEdges (parent : Key) (owner : Nat) (views : List Nat)
    (residual : Option Fiber) : List (Key × Key) :=
  (views.map (fun view => (parent, (allowanceFiber owner view parent.sources parent.transformer).key))) ++
    residual.toList.map (fun fiber => (parent, fiber.key))

def mergeEdges (copyInputs : List Bound) (target parentIndex : Nat) (q : Nat → Nat)
    (post : Key → Nat) (prior : List Fiber) : List (Key × Key) :=
  moveEdges (copiedMoves copyInputs target parentIndex post prior) ++
    moveEdges (canonicalMoves q post (copyFibers copyInputs target parentIndex post prior))

/-- The old full-context parent connects to each exact current filter carrier
by its installed Derived edge followed by zero or one equality transport.
No replacement direct Replay or FunctionPort edge is manufactured. -/
theorem merged_filter_parent_path (copyInputs : List Bound) (target parentIndex owner : Nat)
    (q : Nat → Nat) (events : List Discharge) (parent : Key) (views : List Nat)
    (residual : Option Fiber) (prior : List Fiber) (view : Nat) (selected : view ∈ views) :
    DependencyPath
      (installationEdges parent owner views residual ++
        mergeEdges copyInputs target parentIndex q (postCheck (publications events []))
          (installExpansion owner views parent.sources parent.transformer residual prior))
      parent (allowanceFiber (q owner) view parent.sources parent.transformer).key := by
  let fiber := allowanceFiber owner view parent.sources parent.transformer
  have installed : fiber ∈ installExpansion owner views parent.sources parent.transformer residual prior :=
    (mem_attachAll _ _ _).mpr (Or.inr
      (List.mem_append_left _ (List.mem_map.mpr ⟨view, selected, rfl⟩)))
  have retained := copy_retains copyInputs target parentIndex
    (postCheck (publications events [])) _ fiber installed
  have route := canonical_carrier_path q (postCheck (publications events [])) _ fiber retained
  rw [allowance_carrier_exact] at route
  apply DependencyPath.step
  · apply List.mem_append_left
    exact List.mem_append_left _ (List.mem_map.mpr ⟨view, selected, rfl⟩)
  · apply route.weaken
    intro edge member
    exact List.mem_append_right _ (List.mem_append_right _ member)

theorem merged_residual_parent_path (copyInputs : List Bound) (target parentIndex owner : Nat)
    (q : Nat → Nat) (post : Key → Nat) (parent : Key) (views : List Nat)
    (residual : Fiber) (prior : List Fiber) :
    DependencyPath
      (installationEdges parent owner views (some residual) ++
        mergeEdges copyInputs target parentIndex q post
          (installExpansion owner views parent.sources parent.transformer (some residual) prior))
      parent (carrier q post residual).key := by
  have installed : residual ∈ installExpansion owner views parent.sources parent.transformer (some residual) prior :=
    (mem_attachAll _ _ _).mpr (Or.inr (List.mem_append_right _ (by simp)))
  have retained := copy_retains copyInputs target parentIndex post _ residual installed
  have route := canonical_carrier_path q post _ residual retained
  apply DependencyPath.step (next := residual.key)
  · apply List.mem_append_left
    exact List.mem_append_right _ (by simp)
  · apply route.weaken
    intro edge member
    exact List.mem_append_right _ (List.mem_append_right _ member)

/-- Native row-lower residual placement, after canonicalization and Context.
The opposite level branch reverses the storage polarity, not the comparison. -/
def residualBound (levels : Nat → Nat) (owner : Nat) (upper : Endpoint) : Option Bound :=
  if upper = .row owner then none
  else match upper with
    | .row target =>
        if levels target ≤ levels owner then some ⟨owner, .negative, upper⟩
        else some ⟨target, .positive, .row owner⟩
    | _ => some ⟨owner, .negative, upper⟩

theorem residual_bound_constructed (levels : Nat → Nat) (owner : Nat) (upper : Endpoint)
    (different : upper ≠ .row owner) :
    ∃ bound, residualBound levels owner upper = some bound ∧ bound.pair = (.row owner, upper) := by
  cases upper with
  | row target =>
      by_cases order : levels target ≤ levels owner
      · exact ⟨⟨owner, .negative, .row target⟩, by simp [residualBound, different, order], rfl⟩
      · exact ⟨⟨target, .positive, .row owner⟩, by simp [residualBound, different, order], rfl⟩
  | allowance id => exact ⟨⟨owner, .negative, .allowance id⟩, rfl, rfl⟩
  | support id => exact ⟨⟨owner, .negative, .support id⟩, rfl, rfl⟩
  | contribution id => exact ⟨⟨owner, .negative, .contribution id⟩, rfl, rfl⟩
  | annotationMember view member => exact ⟨⟨owner, .negative, .annotationMember view member⟩, rfl, rfl⟩
  | bottom => exact ⟨⟨owner, .negative, .bottom⟩, rfl, rfl⟩
  | emptyNegative => exact ⟨⟨owner, .negative, .emptyNegative⟩, rfl, rfl⟩

/-- The residual's owner is computed by the native level branch. Application
is to the unconsumed Context branch; this theorem does not infer that branch
from a discharge marker or require a later merge to choose the same owner. -/
theorem merged_computed_residual (copyInputs : List Bound) (target parentIndex owner : Nat)
    (levels q : Nat → Nat) (post : Key → Nat) (upper : Endpoint)
    (different : upper ≠ .row owner) (views : List Nat) (residualContext : Nat)
    (sources : Option Nat) (transformer : Nat) (prior : List Fiber) :
    ∃ bound, residualBound levels owner upper = some bound ∧
      bound.pair = (.row owner, upper) ∧
      carrier q post (exactFiber bound residualContext sources transformer) ∈
        merge copyInputs target parentIndex q post
          (installExpansion owner views sources transformer
            ((residualBound levels owner upper).map
              (fun result => exactFiber result residualContext sources transformer)) prior) := by
  obtain ⟨bound, constructed, pair⟩ := residual_bound_constructed levels owner upper different
  refine ⟨bound, constructed, pair, ?_⟩
  rw [constructed]
  exact merged_expansion_residual copyInputs target parentIndex owner q post views sources transformer
    (exactFiber bound residualContext sources transformer) prior

/-! The local Effect consumer, including every Support member and both kinds
of tail, is a second concrete part of the generation-change construction.
Tables retain the actual view/contribution IDs. `localReturn` is only the
constructor's return; it asserts no drain, diagnostic or semantic completion. -/
namespace Effect

structure View where
  allowed : List Nat
  tail : Option Nat
  closedAllowed : Option (List Nat)

structure Tables where
  views : Nat → Option View
  contributions : Nat → Option Nat

def memberEffect (tables : Tables) : Endpoint → Option Nat
  | .contribution id => tables.contributions id
  | .annotationMember view member => (tables.views view).bind (fun entry => entry.allowed[member]?)
  | _ => none

inductive Outcome where
  | localReturn
  | children (pairs : List (Endpoint × Endpoint))
  | conflict (lower upper : Endpoint)
  | unavailable
  deriving DecidableEq, Repr

def renamePair (q : Nat → Nat) (pair : Endpoint × Endpoint) : Endpoint × Endpoint :=
  (renameEndpoint q pair.1, renameEndpoint q pair.2)

def renameOutcome (q : Nat → Nat) : Outcome → Outcome
  | .localReturn => .localReturn
  | .children pairs => .children (pairs.map (renamePair q))
  | .conflict lower upper => .conflict (renameEndpoint q lower) (renameEndpoint q upper)
  | .unavailable => .unavailable

def checkMember (q : Nat → Nat) (tables : Tables) (lower upper : Endpoint) : Outcome :=
  match upper with
  | .emptyNegative => .conflict lower upper
  | .allowance id =>
      match memberEffect tables lower, tables.views id with
      | some effect, some view =>
          if effect ∈ view.closedAllowed.getD view.allowed then .localReturn
          else match view.tail with
            | some tail => .children [(lower, .row (q tail))]
            | none => .conflict lower upper
      | _, _ => .unavailable
  | _ => .unavailable

/-- Exact `candidate_check_effect_operand` child order: all original member
indices, then the optional canonical tail. Mismatch remains a conflict. -/
def checkOperand (q : Nat → Nat) (tables : Tables) (lower upper : Endpoint) : Outcome :=
  match lower with
  | .bottom => .localReturn
  | .support id =>
      match tables.views id with
      | none => .unavailable
      | some view => .children
          ((List.range view.allowed.length).map (fun member => (.annotationMember id member, upper)) ++
            view.tail.toList.map (fun tail => (.row (q tail), upper)))
  | .contribution _ | .annotationMember _ _ => checkMember q tables lower upper
  | _ => .unavailable

theorem memberEffect_rename (q : Nat → Nat) (tables : Tables) (lower : Endpoint) :
    memberEffect tables (renameEndpoint q lower) = memberEffect tables lower := by
  cases lower <;> rfl

theorem member_transport (old current : Nat → Nat)
    (absorbs : ∀ row, current (old row) = current row)
    (tables : Tables) (lower upper : Endpoint) :
    checkMember current tables (renameEndpoint current lower) (renameEndpoint current upper) =
      renameOutcome current (checkMember old tables lower upper) := by
  cases upper with
  | allowance id =>
      change checkMember current tables (renameEndpoint current lower) (.allowance id) =
        renameOutcome current (checkMember old tables lower (.allowance id))
      simp only [checkMember, memberEffect_rename]
      cases found : memberEffect tables lower with
      | none => rfl
      | some effect =>
          cases available : tables.views id with
          | none => rfl
          | some view =>
              by_cases allowed : effect ∈ view.closedAllowed.getD view.allowed
              · simp [allowed, renameOutcome]
              · cases tail : view.tail <;>
                  simp [allowed, tail, renameOutcome, renamePair, renameEndpoint, absorbs]
  | row id => rfl
  | support id => rfl
  | contribution id => rfl
  | annotationMember view member => rfl
  | bottom => rfl
  | emptyNegative => rfl

/-- A representative merge changes only row endpoints. The entire one-step
Effect expansion, including member positions, tail requests and conflicts,
is the computed image of the earlier expansion. No closed-child predicate is
assumed, and this equation does not claim those children have returned. -/
theorem operand_expansion_transport (old current : Nat → Nat)
    (absorbs : ∀ row, current (old row) = current row)
    (tables : Tables) (lower upper : Endpoint) :
    checkOperand current tables (renameEndpoint current lower) (renameEndpoint current upper) =
      renameOutcome current (checkOperand old tables lower upper) := by
  cases lower with
  | row id => rfl
  | allowance id => rfl
  | support id =>
      cases available : tables.views id with
      | none => simp [checkOperand, renameEndpoint, available, renameOutcome]
      | some view =>
          cases tail : view.tail <;>
            simp [checkOperand, renameEndpoint, available, renameOutcome, renamePair,
              List.map_map, Function.comp_def, tail, absorbs]
  | contribution id => exact member_transport old current absorbs tables (.contribution id) upper
  | annotationMember view member =>
      exact member_transport old current absorbs tables (.annotationMember view member) upper
  | bottom => rfl
  | emptyNegative => rfl

theorem support_member_exact (q : Nat → Nat) (tables : Tables) (id : Nat)
    (view : View) (found : tables.views id = some view) (upper : Endpoint)
    (member : Nat) (inBounds : member < view.allowed.length) :
    ∃ pairs, checkOperand q tables (.support id) upper = .children pairs ∧
      (.annotationMember id member, upper) ∈ pairs := by
  let pairs := (List.range view.allowed.length).map
    (fun index => (Endpoint.annotationMember id index, upper)) ++
      view.tail.toList.map (fun tail => (Endpoint.row (q tail), upper))
  refine ⟨pairs, ?_, ?_⟩
  · simp [checkOperand, found, pairs]
  · change _ ∈ (List.range view.allowed.length).map _ ++ _
    exact List.mem_append_left _ (List.mem_map.mpr ⟨member, List.mem_range.mpr inBounds, rfl⟩)

theorem support_tail_exact (q : Nat → Nat) (tables : Tables) (id : Nat)
    (view : View) (found : tables.views id = some view) (upper : Endpoint)
    (tail : Nat) (hasTail : view.tail = some tail) :
    ∃ pairs, checkOperand q tables (.support id) upper = .children pairs ∧
      (.row (q tail), upper) ∈ pairs := by
  let pairs := (List.range view.allowed.length).map
    (fun index => (Endpoint.annotationMember id index, upper)) ++
      view.tail.toList.map (fun tail => (Endpoint.row (q tail), upper))
  refine ⟨pairs, ?_, ?_⟩
  · simp [checkOperand, found, pairs]
  · change _ ∈ (List.range view.allowed.length).map _ ++ _
    exact List.mem_append_right _ (by simp [hasTail])

end Effect

/-! The Replay generator is per EXACT ordered pair of physical BoundKeys.
The element type retains the two attached relation identities; dependency
keys retain this input pair and the fixed root-key constructor. The native
authentication of these identities is not inferred from list membership. -/
namespace Replay

structure State (α : Type) where
  oldLower : List α := []
  newLower : List α := []
  oldUpper : List α := []
  newUpper : List α := []
  dependencies : List (α × α) := []
  operations : List (List (α × α)) := []

def State.lower (state : State α) := state.newLower ++ state.oldLower
def State.upper (state : State α) := state.newUpper ++ state.oldUpper

def candidates (state : State α) (incoming : Bool) : List (α × α) :=
  if incoming then product state.lower state.upper
  else replayDelta state.oldLower state.newLower state.oldUpper state.newUpper

def children [DecidableEq α] (state : State α) (incoming : Bool) : List (α × α) :=
  if incoming then candidates state incoming
  else (candidates state incoming).filter (fun pair => pair ∉ state.dependencies)

inductive Event (α : Type) where
  | lower (fiber : α)
  | upper (fiber : α)
  | replay (incoming : Bool)

def step [DecidableEq α] (state : State α) : Event α → State α
  | .lower fiber => if fiber ∈ state.lower then state
      else { state with newLower := fiber :: state.newLower }
  | .upper fiber => if fiber ∈ state.upper then state
      else { state with newUpper := fiber :: state.newUpper }
  | .replay incoming =>
      { oldLower := state.lower, oldUpper := state.upper,
        dependencies := children state incoming ++ state.dependencies,
        operations := state.operations ++ [children state incoming] }

def run [DecidableEq α] : List (Event α) → State α → State α
  | [], state => state
  | event :: rest, state => run rest (step state event)

structure OriginInvariant (state : State α) : Prop where
  oldProduct : ∀ pair, pair ∈ product state.oldLower state.oldUpper →
    pair ∈ state.dependencies
  dependencyOrigin : ∀ pair, pair ∈ state.dependencies ↔
    ∃ batch, batch ∈ state.operations ∧ pair ∈ batch

theorem initial_origins : OriginInvariant ({} : State α) := by
  constructor <;> simp [product]

theorem replay_retains_all_products [DecidableEq α] {state : State α}
    (origins : OriginInvariant state) (incoming : Bool) (lower upper : α)
    (present : (lower, upper) ∈ product state.lower state.upper) :
    (lower, upper) ∈ children state incoming ++ state.dependencies := by
  cases incoming with
  | true => exact List.mem_append_left _ (by simpa [children, candidates] using present)
  | false =>
      rcases (replay_quadrants_cover _ _ _ _ lower upper).mp present with fresh | old
      · by_cases seen : (lower, upper) ∈ state.dependencies
        · exact List.mem_append_right _ seen
        · apply List.mem_append_left
          exact List.mem_filter.mpr ⟨fresh, by simpa using seen⟩
      · exact List.mem_append_right _ (origins.oldProduct _ old)

theorem step_origins [DecidableEq α] {state : State α}
    (origins : OriginInvariant state) (event : Event α) :
    OriginInvariant (step state event) := by
  cases event with
  | lower fiber =>
      simp only [step]
      split
      · exact origins
      · exact ⟨origins.oldProduct, origins.dependencyOrigin⟩
  | upper fiber =>
      simp only [step]
      split
      · exact origins
      · exact ⟨origins.oldProduct, origins.dependencyOrigin⟩
  | replay incoming =>
      constructor
      · rintro ⟨lower, upper⟩ present
        exact replay_retains_all_products origins incoming lower upper present
      · intro pair
        change pair ∈ children state incoming ++ state.dependencies ↔
          ∃ batch, batch ∈ state.operations ++ [children state incoming] ∧ pair ∈ batch
        constructor
        · intro present
          rcases List.mem_append.mp present with fresh | old
          · exact ⟨children state incoming, List.mem_append_right _ (by simp), fresh⟩
          · obtain ⟨batch, prior, member⟩ := (origins.dependencyOrigin pair).mp old
            exact ⟨batch, List.mem_append_left _ prior, member⟩
        · rintro ⟨batch, present, member⟩
          rcases List.mem_append.mp present with old | fresh
          · exact List.mem_append_right _ ((origins.dependencyOrigin pair).mpr ⟨batch, old, member⟩)
          · have same : batch = children state incoming := List.mem_singleton.mp fresh
            exact List.mem_append_left _ (same ▸ member)

theorem run_origins [DecidableEq α] (events : List (Event α)) {state : State α}
    (origins : OriginInvariant state) : OriginInvariant (run events state) := by
  induction events generalizing state with
  | nil => exact origins
  | cons event rest ih => exact ih (step_origins origins event)

/-- Both skip cases obtain an actual indexed earlier batch/child in the
computed transcript. This is historical creation, not a returned disposition. -/
theorem dependency_indexed_origin [DecidableEq α] (events : List (Event α))
    (pair : α × α) (present : pair ∈ (run events {}).dependencies) :
    ∃ (operation : Nat) (batch : List (α × α)) (index : Nat),
      (run events {}).operations[operation]? = some batch ∧ batch[index]? = some pair := by
  obtain ⟨batch, batchMember, member⟩ :=
    ((run_origins events initial_origins).dependencyOrigin pair).mp present
  obtain ⟨operation, inBounds, found⟩ := List.mem_iff_getElem.mp batchMember
  obtain ⟨index, childBounds, childFound⟩ := List.mem_iff_getElem.mp member
  exact ⟨operation, batch, index, by simp [inBounds, found], by simp [childBounds, childFound]⟩

theorem old_old_indexed_origin [DecidableEq α] (events : List (Event α))
    (lower upper : α) (present : (lower, upper) ∈
      product (run events {}).oldLower (run events {}).oldUpper) :
    ∃ (operation : Nat) (batch : List (α × α)) (index : Nat),
      (run events {}).operations[operation]? = some batch ∧
        batch[index]? = some (lower, upper) :=
  dependency_indexed_origin events (lower, upper)
    ((run_origins events initial_origins).oldProduct _ present)

theorem dependency_skip_has_origin [DecidableEq α] (events : List (Event α))
    (pair : α × α) (seen : pair ∈ (run events {}).dependencies) :
    pair ∉ children (run events {}) false ∧
      ∃ (operation : Nat) (batch : List (α × α)) (index : Nat),
        (run events {}).operations[operation]? = some batch ∧ batch[index]? = some pair := by
  refine ⟨?_, dependency_indexed_origin events pair seen⟩
  simp [children, seen]

theorem fired_product_indexed_origin [DecidableEq α] (events : List (Event α))
    (incoming : Bool) (lower upper : α)
    (present : (lower, upper) ∈ product (run events {}).lower (run events {}).upper) :
    ∃ (operation : Nat) (batch : List (α × α)) (index : Nat),
      (step (run events {}) (.replay incoming)).operations[operation]? = some batch ∧
        batch[index]? = some (lower, upper) := by
  have retained := replay_retains_all_products (run_origins events initial_origins)
    incoming lower upper present
  have origin := (step_origins (run_origins events initial_origins) (.replay incoming)).dependencyOrigin
  obtain ⟨batch, batchMember, member⟩ := (origin (lower, upper)).mp retained
  obtain ⟨operation, inBounds, found⟩ := List.mem_iff_getElem.mp batchMember
  obtain ⟨index, childBounds, childFound⟩ := List.mem_iff_getElem.mp member
  exact ⟨operation, batch, index, by simp [inBounds, found], by simp [childBounds, childFound]⟩

end Replay
end YulangClosure.NativeMergeExpansion
