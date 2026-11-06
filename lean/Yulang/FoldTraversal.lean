import Yulang.LoopEffects
import Yulang.RoleDictionaries
import Yulang.CheckedRoles

/-!
# Finite observations of a resolved Fold traversal protocol

A cursor is an arbitrary machine state, not necessarily a finite collection.
One observation may finish, take an internal step, yield an item, or expose an
operation-specific signed request with its original resumption. Internal and
yielding cycles are permitted. Finite prefixes make no termination claim and
need no numerical fuel or artificial language error.

The local safety contract checks every response continuation and every yielded
item. Prefix safety follows from this contract without assuming that a whole
traversal succeeds. The rigid role resolver selects a declaration plan before
an explicitly supplied implementation table supplies its protocol.

This protocol is an interface for already elaborated dictionary execution.
It is NOT a derivation of this interface from arbitrary source `Fold.fold`:
that method is higher order and polymorphic in its accumulator. Compilation
of its method body, callback behaviour and effects into this interface, and
their semantic correspondence, remain separate obligations. A pure cursor
adapter agrees with the traversal observations of the existing `LoopEffects`
kernel; that kernel alone does not implement arbitrary source Fold either.
-/

namespace Yulang.FoldTraversal

open Directed SignatureRequests

inductive View (n : Nat) (signature : Signature Key) (Item Cursor : Type) where
  | done
  | tick : Cursor → View n signature Item Cursor
  | yield : Item → Cursor → View n signature Item Cursor
  | request (occurrence : Occurrence n Key) (payload : signature.Payload occurrence.key)
      (resume : signature.Response occurrence.key → Cursor)

abbrev Protocol (n : Nat) (signature : Signature Key) (Item Cursor : Type) :=
  Cursor → View n signature Item Cursor

structure Driver (n : Nat) (signature : Signature Key) (Container Item Cursor : Type) where
  start : Container → Cursor
  observe : Protocol n signature Item Cursor

variable {Key Item Cursor Container : Type} {n : Nat} {signature : Signature Key}

/-- Responses are supplied by the surrounding computation. An unanswered
request is a pending observation, not an internal transition or a fake value. -/
inductive Step (protocol : Protocol n signature Item Cursor) :
    Cursor → List Item → Row n Key → Cursor → Prop where
  | tick : protocol cursor = .tick next → Step protocol cursor [] [] next
  | yield : protocol cursor = .yield item next → Step protocol cursor [item] [] next
  | answer (observed : protocol cursor = .request occurrence payload resume)
      (response : signature.Response occurrence.key) :
      Step protocol cursor [] [occurrence] (resume response)

/-- Independent finite execution prefixes. Order and duplicate items/requests
are retained, including signed weights. The final cursor need not be done. -/
inductive Prefix (protocol : Protocol n signature Item Cursor) :
    Cursor → List Item → Row n Key → Cursor → Prop where
  | refl : Prefix protocol cursor [] [] cursor
  | cons : Step protocol first items requests next →
      Prefix protocol next later laterRequests last →
      Prefix protocol first (items ++ later) (requests ++ laterRequests) last

theorem Prefix.trans (first : Prefix protocol a xs es b)
    (last : Prefix protocol b ys fs c) : Prefix protocol a (xs ++ ys) (es ++ fs) c := by
  induction first with
  | refl => simpa using last
  | cons step tail ih =>
      simpa only [List.append_assoc] using Prefix.cons step (ih last)

/-- A local inductive invariant, quantified over every response. No field
assumes a successful run or a finite source container. -/
structure Safe (protocol : Protocol n signature Item Cursor)
    (valid : Cursor → Prop) (itemType : Item → Prop) (row : Occurrence n Key → Prop) : Prop where
  tick : ∀ cursor next, valid cursor → protocol cursor = .tick next → valid next
  yield : ∀ cursor item next, valid cursor → protocol cursor = .yield item next →
    itemType item ∧ valid next
  request : ∀ cursor occurrence payload resume, valid cursor →
    protocol cursor = .request occurrence payload resume →
    row occurrence ∧ ∀ response, valid (resume response)

theorem step_safe (safe : Safe protocol valid itemType row)
    (initial : valid first) (step : Step protocol first items requests last) :
    valid last ∧ (∀ item ∈ items, itemType item) ∧ (∀ occurrence ∈ requests, row occurrence) := by
  cases step with
  | tick observed => exact ⟨safe.tick _ _ initial observed, by simp, by simp⟩
  | yield observed =>
      obtain ⟨itemValid, nextValid⟩ := safe.yield _ _ _ initial observed
      exact ⟨nextValid, by simpa using itemValid, by simp⟩
  | answer observed response =>
      obtain ⟨allowed, continues⟩ := safe.request _ _ _ _ initial observed
      exact ⟨continues response, by simp, by simpa using allowed⟩

theorem prefix_safe (safe : Safe protocol valid itemType row) (initial : valid first)
    (observedPrefix : Prefix protocol first items requests last) :
    valid last ∧ (∀ item ∈ items, itemType item) ∧ (∀ occurrence ∈ requests, row occurrence) := by
  induction observedPrefix with
  | refl => exact ⟨initial, by simp, by simp⟩
  | cons step tail ih =>
      obtain ⟨nextValid, firstItems, firstRequests⟩ := step_safe safe initial step
      obtain ⟨lastValid, lastItems, lastRequests⟩ := ih nextValid
      exact ⟨lastValid, fun item member => (List.mem_append.mp member).elim
        (firstItems item) (lastItems item), fun occurrence member =>
          (List.mem_append.mp member).elim (firstRequests occurrence) (lastRequests occurrence)⟩

/-- Progress includes a well-typed suspended request; it does not promise an
answer to an abortive or externally unhandled operation. -/
theorem progress (safe : Safe protocol valid itemType row) (initial : valid cursor) :
    protocol cursor = .done ∨
    (∃ next, protocol cursor = .tick next ∧ valid next) ∨
    (∃ item next, protocol cursor = .yield item next ∧ itemType item ∧ valid next) ∨
    (∃ occurrence payload resume, protocol cursor = .request occurrence payload resume ∧
      row occurrence ∧ ∀ response, valid (resume response)) := by
  cases observed : protocol cursor with
  | done => exact Or.inl rfl
  | tick next => exact Or.inr (Or.inl ⟨next, rfl, safe.tick _ _ initial observed⟩)
  | yield item next =>
      exact Or.inr (Or.inr (Or.inl ⟨item, next, rfl, safe.yield _ _ _ initial observed⟩))
  | request occurrence payload resume =>
      exact Or.inr (Or.inr (Or.inr ⟨occurrence, payload, resume, rfl,
        safe.request _ _ _ _ initial observed⟩))

theorem pending_after_prefix (safe : Safe protocol valid itemType row) (initial : valid first)
    (observedPrefix : Prefix protocol first items requests last)
    (pending : protocol last = .request occurrence payload resume) :
    row occurrence ∧ ∀ response, valid (resume response) :=
  safe.request _ _ _ _ (prefix_safe safe initial observedPrefix).1 pending

/-! ## Pure-cursor special case and existing unlabelled for traversal -/

def ofNext (nextItem : Cursor → Option (Item × Cursor)) : Protocol n signature Item Cursor :=
  fun cursor => match nextItem cursor with
    | none => .done
    | some (item, next) => .yield item next

theorem ofNext_done (nextItem : Cursor → Option (Item × Cursor)) (cursor : Cursor) :
    ofNext (n := n) (signature := signature) nextItem cursor = .done ↔ nextItem cursor = none := by
  cases observed : nextItem cursor <;> simp [ofNext, observed]

theorem ofNext_yield (nextItem : Cursor → Option (Item × Cursor))
    (cursor next : Cursor) (item : Item) :
    ofNext (n := n) (signature := signature) nextItem cursor = .yield item next ↔
      nextItem cursor = some (item, next) := by
  cases observed : nextItem cursor with
  | none => simp [ofNext, observed]
  | some pair => cases pair; simp [ofNext, observed]

theorem existing_for_enters [DecidableEq Key]
    (machine : LoopEffects.Machine n signature Item Cursor State Event Value)
    (observed : ofNext (n := n) (signature := signature) machine.nextItem cursor = .yield item next) :
    LoopEffects.Step machine ⟨state, .pull cursor⟩ none
      ⟨state, .body item next (machine.body item)⟩ :=
  .enter ((ofNext_yield machine.nextItem cursor next item).mp observed)

theorem existing_for_finishes [DecidableEq Key]
    (machine : LoopEffects.Machine n signature Item Cursor State Event Value)
    (observed : ofNext (n := n) (signature := signature) machine.nextItem cursor = .done) :
    LoopEffects.Step machine ⟨state, .pull cursor⟩ none ⟨state, .done⟩ :=
  .exhausted ((ofNext_done machine.nextItem cursor).mp observed)

/-- Infinite yielding is admitted by the same safe protocol. -/
def repeatItems (item : Item) : Protocol n signature Item Unit := fun _ => .yield item ()

theorem repeat_safe (item : Item) (itemType : Item → Prop) (typed : itemType item)
    (row : Occurrence n Key → Prop) :
    Safe (repeatItems (signature := signature) item) (fun _ => True) itemType row := by
  constructor
  · intro cursor next _ observed; cases observed
  · intro cursor found next _ observed
    cases observed
    exact ⟨typed, trivial⟩
  · intro cursor occurrence payload resume _ observed; cases observed

theorem repeat_prefix (item : Item) (count : Nat) :
    Prefix (repeatItems (n := n) (signature := signature) item) () (List.replicate count item) [] () := by
  induction count with
  | zero => exact .refl
  | succ count ih =>
      simpa [List.replicate_succ] using
        Prefix.cons (Step.yield (protocol := repeatItems item) rfl) ih

theorem repeat_never_done (item : Item) (cursor : Unit) :
    repeatItems (n := n) (signature := signature) item cursor ≠ .done := by
  intro impossible
  cases impossible

/-! ## An accepted rigid role slot selects exactly its dictionary plan -/

def acceptedDictionary (visible : List Roles.Impl) (goal : Roles.Goal)
    (accepted : CheckedRoles.resolve visible goal = .answer .resolved) :
    RoleDictionaries.Dictionary visible goal :=
  let checked := (CheckedRoles.resolve_exact visible goal).mp accepted
  RoleDictionaries.buildResolved visible checked.1 goal
    ((RoleConstraints.resolve_exact visible checked.1 goal).mpr checked.2)

theorem accepted_plan_unique (visible : List Roles.Impl) (goal : Roles.Goal)
    (accepted : CheckedRoles.resolve visible goal = .answer .resolved)
    (dictionary : RoleDictionaries.Dictionary visible goal) :
    (acceptedDictionary visible goal accepted).erase = dictionary.erase :=
  RoleDictionaries.Dictionary.erase_unique _ _

/-- The table is a supplied method-body elaboration interface, not a claim
that role resolution has already compiled source method bodies. -/
def selectedDriver
    (table : RoleDictionaries.Plan → Driver n signature Container Item Cursor)
    (visible : List Roles.Impl) (goal : Roles.Goal)
    (accepted : CheckedRoles.resolve visible goal = .answer .resolved) :
    Driver n signature Container Item Cursor :=
  table (acceptedDictionary visible goal accepted).erase

theorem selected_driver_exact
    (table : RoleDictionaries.Plan → Driver n signature Container Item Cursor)
    (visible : List Roles.Impl) (goal : Roles.Goal)
    (accepted : CheckedRoles.resolve visible goal = .answer .resolved)
    (dictionary : RoleDictionaries.Dictionary visible goal) :
    selectedDriver table visible goal accepted = table dictionary.erase := by
  unfold selectedDriver
  rw [accepted_plan_unique visible goal accepted dictionary]

end Yulang.FoldTraversal
