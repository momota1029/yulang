import Yulang.FoldTraversal

/-!
# Ordered list construction from resolved Fold protocols

Source evaluation and dictionary traversal both admit internal divergence and
signed requests. A source occurrence is started once, then its Fold is drained
before the following source occurrence starts. Items are appended in traversal
order. There is no finiteness premise, run budget, or synthetic budget error.

The typing judgment records each contribution's item type, the source effect
row, and the traversal effect row. The result item type and effect row are
their unions. Safety is derived from local source/dictionary invariants, not
from a premise that evaluation succeeds. Only ordinary element sites carry an
explicit pure conversion; no fresh cast boundary for spread items is chosen.

As in `FoldTraversal`, the dictionary protocol and its local typing contract
are supplied after elaboration. Source `Fold.fold` method compilation and
whole-source inference are not proved by this resolved composition layer.
-/

namespace Yulang.FoldListSpread

open Directed SignatureRequests

/-- A source or compound expression can return, take an internal step, or
expose an unanswered request. The resumption is preserved for every response. -/
inductive View (n : Nat) (signature : Signature Key) (Value State : Type) where
  | value : Value → View n signature Value State
  | tick : State → View n signature Value State
  | request (occurrence : Occurrence n Key) (payload : signature.Payload occurrence.key)
      (resume : signature.Response occurrence.key → State)

abbrev Process (n : Nat) (signature : Signature Key) (Value State : Type) :=
  State → View n signature Value State

variable {Key Value State : Type} {n : Nat} {signature : Signature Key}

structure Safe (process : Process n signature Value State) (valid : State → Prop)
    (result : Value → Prop) (row : Occurrence n Key → Prop) : Prop where
  value : ∀ state value, valid state → process state = .value value → result value
  tick : ∀ state next, valid state → process state = .tick next → valid next
  request : ∀ state occurrence payload resume, valid state →
    process state = .request occurrence payload resume →
    row occurrence ∧ ∀ response, valid (resume response)

inductive Step (process : Process n signature Value State) : State → Row n Key → State → Prop where
  | tick : process state = .tick next → Step process state [] next
  | answer : process state = .request occurrence payload resume →
      (response : signature.Response occurrence.key) → Step process state [occurrence] (resume response)

inductive Prefix (process : Process n signature Value State) : State → Row n Key → State → Prop where
  | refl : Prefix process state [] state
  | cons : Step process first requests next → Prefix process next later last →
      Prefix process first (requests ++ later) last

theorem Prefix.trans (first : Prefix process a es b) (last : Prefix process b fs c) :
    Prefix process a (es ++ fs) c := by
  induction first with
  | refl => simpa using last
  | cons step tail ih => simpa only [List.append_assoc] using Prefix.cons step (ih last)

theorem step_safe (safe : Safe process valid result row) (initial : valid first)
    (step : Step process first requests last) : valid last ∧ ∀ request ∈ requests, row request := by
  cases step with
  | tick observed => exact ⟨safe.tick _ _ initial observed, by simp⟩
  | answer observed response =>
      obtain ⟨allowed, resumes⟩ := safe.request _ _ _ _ initial observed
      exact ⟨resumes response, by simpa using allowed⟩

theorem prefix_safe (safe : Safe process valid result row) (initial : valid first)
    (observedPrefix : Prefix process first requests last) :
    valid last ∧ ∀ request ∈ requests, row request := by
  induction observedPrefix with
  | refl => exact ⟨initial, by simp⟩
  | cons step tail ih =>
      obtain ⟨nextValid, firstAllowed⟩ := step_safe safe initial step
      obtain ⟨lastValid, lastAllowed⟩ := ih nextValid
      exact ⟨lastValid, fun request member =>
        (List.mem_append.mp member).elim (firstAllowed request) (lastAllowed request)⟩

theorem progress (safe : Safe process valid result row) (initial : valid state) :
    (∃ value, process state = .value value ∧ result value) ∨
    (∃ next, process state = .tick next ∧ valid next) ∨
    (∃ occurrence payload resume, process state = .request occurrence payload resume ∧
      row occurrence ∧ ∀ response, valid (resume response)) := by
  cases observed : process state with
  | value value => exact Or.inl ⟨value, rfl, safe.value _ _ initial observed⟩
  | tick next => exact Or.inr (Or.inl ⟨next, rfl, safe.tick _ _ initial observed⟩)
  | request occurrence payload resume =>
      exact Or.inr (Or.inr ⟨occurrence, payload, resume, rfl, safe.request _ _ _ _ initial observed⟩)

inductive Part (Source Conversion Dictionary : Type) where
  | element : Source → Conversion → Part Source Conversion Dictionary
  | spread : Source → Dictionary → Part Source Conversion Dictionary

def Part.source : Part Source Conversion Dictionary → Source
  | .element code _ | .spread code _ => code

structure Engine (n : Nat) (signature : Signature Key)
    (Source Conversion Dictionary Value SourceState FoldState : Type) where
  startSource : Source → SourceState
  source : Process n signature Value SourceState
  convert : Conversion → Value → Value
  fold : Dictionary → FoldTraversal.Driver n signature Value Value FoldState

inductive Control (Source Conversion Dictionary SourceState FoldState : Type) where
  | ready : List (Part Source Conversion Dictionary) → Control Source Conversion Dictionary SourceState FoldState
  | evaluating : Part Source Conversion Dictionary → List (Part Source Conversion Dictionary) → SourceState →
      Control Source Conversion Dictionary SourceState FoldState
  | traversing : Dictionary → List (Part Source Conversion Dictionary) → FoldState →
      Control Source Conversion Dictionary SourceState FoldState

structure Configuration (Source Conversion Dictionary Value SourceState FoldState : Type) where
  values : List Value
  control : Control Source Conversion Dictionary SourceState FoldState

variable {Source Conversion Dictionary SourceState FoldState : Type}

def Engine.observe (engine : Engine n signature Source Conversion Dictionary Value SourceState FoldState) :
    Process n signature (List Value) (Configuration Source Conversion Dictionary Value SourceState FoldState)
  | ⟨values, .ready []⟩ => .value values
  | ⟨values, .ready (part :: rest)⟩ =>
      .tick ⟨values, .evaluating part rest (engine.startSource part.source)⟩
  | ⟨values, .evaluating part rest state⟩ =>
      match engine.source state with
      | .value value =>
          match part with
          | .element _ conversion => .tick ⟨values ++ [engine.convert conversion value], .ready rest⟩
          | .spread _ dictionary => .tick ⟨values, .traversing dictionary rest ((engine.fold dictionary).start value)⟩
      | .tick next => .tick ⟨values, .evaluating part rest next⟩
      | .request occurrence payload resume =>
          .request occurrence payload (fun response => ⟨values, .evaluating part rest (resume response)⟩)
  | ⟨values, .traversing dictionary rest cursor⟩ =>
      match (engine.fold dictionary).observe cursor with
      | .done => .tick ⟨values, .ready rest⟩
      | .tick next => .tick ⟨values, .traversing dictionary rest next⟩
      | .yield item next => .tick ⟨values ++ [item], .traversing dictionary rest next⟩
      | .request occurrence payload resume =>
          .request occurrence payload (fun response => ⟨values, .traversing dictionary rest (resume response)⟩)

def start (parts : List (Part Source Conversion Dictionary)) :
    Configuration Source Conversion Dictionary Value SourceState FoldState := ⟨[], .ready parts⟩

/-- Static judgments and their local operational invariants are separate.
In particular, none of these fields asserts a successful whole computation. -/
structure Contracts (engine : Engine n signature Source Conversion Dictionary Value SourceState FoldState) where
  SourceTyped : Source → (Value → Prop) → (Occurrence n Key → Prop) → Prop
  ConversionTyped : Conversion → (Value → Prop) → (Value → Prop) → Prop
  FoldTyped : Dictionary → (Value → Prop) → (Value → Prop) → (Occurrence n Key → Prop) → Prop
  SourceValid : SourceState → (Value → Prop) → (Occurrence n Key → Prop) → Prop
  FoldValid : Dictionary → FoldState → (Value → Prop) → (Occurrence n Key → Prop) → Prop
  source_start : ∀ code input row, SourceTyped code input row → SourceValid (engine.startSource code) input row
  source_safe : ∀ input row, Safe engine.source (fun state => SourceValid state input row) input row
  conversion_safe : ∀ conversion input output, ConversionTyped conversion input output →
    ∀ value, input value → output (engine.convert conversion value)
  fold_start : ∀ dictionary input item row, FoldTyped dictionary input item row →
    ∀ value, input value → FoldValid dictionary ((engine.fold dictionary).start value) item row
  fold_safe : ∀ dictionary item row, FoldTraversal.Safe (engine.fold dictionary).observe
    (fun state => FoldValid dictionary state item row) item row

variable {engine : Engine n signature Source Conversion Dictionary Value SourceState FoldState}

inductive PartTyping (contracts : Contracts engine) :
    Part Source Conversion Dictionary → (Value → Prop) → (Occurrence n Key → Prop) → Prop where
  | element : contracts.SourceTyped code input row → contracts.ConversionTyped conversion input output →
      PartTyping contracts (.element code conversion) output row
  | spread : contracts.SourceTyped code container sourceRow →
      contracts.FoldTyped dictionary container item traversalRow →
      PartTyping contracts (.spread code dictionary) item (fun request => sourceRow request ∨ traversalRow request)

/-- All local types are retained: contributions need not share one type. -/
inductive Typing (contracts : Contracts engine) : List (Part Source Conversion Dictionary) →
    List (Value → Prop) → List (Occurrence n Key → Prop) → Prop where
  | nil : Typing contracts [] [] []
  | cons : PartTyping contracts part item row → Typing contracts rest items rows →
      Typing contracts (part :: rest) (item :: items) (row :: rows)

def union {A : Type} (predicates : List (A → Prop)) : A → Prop := fun value => ∃ predicate ∈ predicates, predicate value

@[simp] theorem union_nil {A : Type} (value : A) : union [] value ↔ False := by simp [union]
@[simp] theorem union_cons {A : Type} (first : A → Prop) (rest : List (A → Prop)) (value : A) :
    union (first :: rest) value ↔ first value ∨ union rest value := by simp [union]

inductive PartsTyped (contracts : Contracts engine) (target : Value → Prop)
    (row : Occurrence n Key → Prop) : List (Part Source Conversion Dictionary) → Prop where
  | nil : PartsTyped contracts target row []
  | cons : PartTyping contracts part item effects → (∀ value, item value → target value) →
      (∀ request, effects request → row request) → PartsTyped contracts target row rest →
      PartsTyped contracts target row (part :: rest)

theorem PartsTyped.mono (typed : PartsTyped contracts first before parts)
    (values : ∀ value, first value → last value) (effects : ∀ request, before request → after request) :
    PartsTyped contracts last after parts := by
  induction typed with
  | nil => exact .nil
  | cons head itemBound rowBound tail ih =>
      exact .cons head (fun value held => values value (itemBound value held))
        (fun request held => effects request (rowBound request held)) ih

theorem typing_union (typed : Typing contracts parts items rows) :
    PartsTyped contracts (union items) (union rows) parts := by
  induction typed with
  | nil => exact .nil
  | cons head tail ih =>
      exact .cons head (fun value held => (union_cons _ _ value).mpr (Or.inl held))
        (fun request held => (union_cons _ _ request).mpr (Or.inl held))
        (ih.mono (fun value held => (union_cons _ _ value).mpr (Or.inr held))
          (fun request held => (union_cons _ _ request).mpr (Or.inr held)))

inductive ControlTyped (contracts : Contracts engine) (target : Value → Prop)
    (row : Occurrence n Key → Prop) : Control Source Conversion Dictionary SourceState FoldState → Prop where
  | ready : PartsTyped contracts target row parts → ControlTyped contracts target row (.ready parts)
  | element : contracts.SourceValid state input sourceRow → contracts.ConversionTyped conversion input item →
      (∀ value, item value → target value) → (∀ request, sourceRow request → row request) →
      PartsTyped contracts target row rest →
      ControlTyped contracts target row (.evaluating (.element code conversion) rest state)
  | spread : contracts.SourceValid state container sourceRow →
      contracts.FoldTyped dictionary container item traversalRow →
      (∀ value, item value → target value) → (∀ request, sourceRow request → row request) →
      (∀ request, traversalRow request → row request) → PartsTyped contracts target row rest →
      ControlTyped contracts target row (.evaluating (.spread code dictionary) rest state)
  | traversing : contracts.FoldValid dictionary cursor item traversalRow →
      (∀ value, item value → target value) → (∀ request, traversalRow request → row request) →
      PartsTyped contracts target row rest → ControlTyped contracts target row (.traversing dictionary rest cursor)

def ConfigurationTyped (contracts : Contracts engine) (target : Value → Prop)
    (row : Occurrence n Key → Prop)
    (configuration : Configuration Source Conversion Dictionary Value SourceState FoldState) : Prop :=
  (∀ value ∈ configuration.values, target value) ∧ ControlTyped contracts target row configuration.control

theorem start_typed (typed : Typing contracts parts items rows) :
    ConfigurationTyped contracts (union items) (union rows) (start parts) :=
  ⟨by simp [start], .ready (typing_union typed)⟩

private theorem append_typed {values : List Value} {target : Value → Prop} {item : Value}
    (before : ∀ value ∈ values, target value) (last : target item) :
    ∀ value ∈ values ++ [item], target value := by
  intro value member
  rcases List.mem_append.mp member with earlier | final
  · exact before value earlier
  · exact (List.mem_singleton.mp final) ▸ last

theorem observe_typed (contracts : Contracts engine) (target : Value → Prop) (row : Occurrence n Key → Prop)
    (configuration : Configuration Source Conversion Dictionary Value SourceState FoldState)
    (typed : ConfigurationTyped contracts target row configuration) :
    match engine.observe configuration with
    | .value values => ∀ value ∈ values, target value
    | .tick next => ConfigurationTyped contracts target row next
    | .request occurrence _ resume => row occurrence ∧
        ∀ response, ConfigurationTyped contracts target row (resume response) := by
  rcases configuration with ⟨values, control⟩
  rcases typed with ⟨valuesTyped, controlTyped⟩
  cases controlTyped with
  | ready partsTyped =>
      cases partsTyped with
      | nil => exact valuesTyped
      | cons head itemBound rowBound tail =>
          cases head with
          | element sourceTyped conversionTyped =>
              exact ⟨valuesTyped, .element (contracts.source_start _ _ _ sourceTyped)
                conversionTyped itemBound rowBound tail⟩
          | spread sourceTyped foldTyped =>
              exact ⟨valuesTyped, .spread (contracts.source_start _ _ _ sourceTyped)
                foldTyped itemBound (fun request held => rowBound request (Or.inl held))
                (fun request held => rowBound request (Or.inr held)) tail⟩
  | @element state input sourceRow conversion item code rest sourceValid conversionTyped itemBound rowBound tail =>
      cases observed : engine.source state with
      | value value =>
          simp only [Engine.observe, observed]
          exact ⟨append_typed valuesTyped (itemBound _
            (contracts.conversion_safe _ _ _ conversionTyped _
              ((contracts.source_safe input sourceRow).value _ _ sourceValid observed))), .ready tail⟩
      | tick next =>
          simp only [Engine.observe, observed]
          exact ⟨valuesTyped, .element ((contracts.source_safe input sourceRow).tick _ _ sourceValid observed)
            conversionTyped itemBound rowBound tail⟩
      | request occurrence payload resume =>
          simp only [Engine.observe, observed]
          obtain ⟨allowed, resumes⟩ := (contracts.source_safe input sourceRow).request _ _ _ _ sourceValid observed
          exact ⟨rowBound _ allowed, fun response =>
            ⟨valuesTyped, .element (resumes response) conversionTyped itemBound rowBound tail⟩⟩
  | @spread state container sourceRow dictionary item traversalRow code rest
      sourceValid foldTyped itemBound sourceBound traversalBound tail =>
      cases observed : engine.source state with
      | value value =>
          simp only [Engine.observe, observed]
          exact ⟨valuesTyped, .traversing (contracts.fold_start _ _ _ _ foldTyped _
            ((contracts.source_safe container sourceRow).value _ _ sourceValid observed))
            itemBound traversalBound tail⟩
      | tick next =>
          simp only [Engine.observe, observed]
          exact ⟨valuesTyped, .spread ((contracts.source_safe container sourceRow).tick _ _ sourceValid observed)
            foldTyped itemBound sourceBound traversalBound tail⟩
      | request occurrence payload resume =>
          simp only [Engine.observe, observed]
          obtain ⟨allowed, resumes⟩ := (contracts.source_safe container sourceRow).request _ _ _ _ sourceValid observed
          exact ⟨sourceBound _ allowed, fun response =>
            ⟨valuesTyped, .spread (resumes response) foldTyped itemBound sourceBound traversalBound tail⟩⟩
  | @traversing dictionary cursor item traversalRow rest cursorValid itemBound rowBound tail =>
      cases observed : (engine.fold dictionary).observe cursor with
      | done =>
          simp only [Engine.observe, observed]
          exact ⟨valuesTyped, .ready tail⟩
      | tick next =>
          simp only [Engine.observe, observed]
          exact ⟨valuesTyped, .traversing ((contracts.fold_safe dictionary item traversalRow).tick _ _ cursorValid observed)
            itemBound rowBound tail⟩
      | yield value next =>
          simp only [Engine.observe, observed]
          obtain ⟨valueTyped, nextValid⟩ := (contracts.fold_safe dictionary item traversalRow).yield _ _ _ cursorValid observed
          exact ⟨append_typed valuesTyped (itemBound _ valueTyped), .traversing nextValid itemBound rowBound tail⟩
      | request occurrence payload resume =>
          simp only [Engine.observe, observed]
          obtain ⟨allowed, resumes⟩ := (contracts.fold_safe dictionary item traversalRow).request _ _ _ _ cursorValid observed
          exact ⟨rowBound _ allowed, fun response =>
            ⟨valuesTyped, .traversing (resumes response) itemBound rowBound tail⟩⟩

theorem engine_safe (contracts : Contracts engine) (target : Value → Prop) (row : Occurrence n Key → Prop) :
    Safe engine.observe (ConfigurationTyped contracts target row)
      (fun values => ∀ value ∈ values, target value) row := by
  constructor
  · intro configuration values typed observed
    have holds := observe_typed contracts target row configuration typed
    simpa only [observed] using holds
  · intro configuration next typed observed
    have holds := observe_typed contracts target row configuration typed
    simpa only [observed] using holds
  · intro configuration occurrence payload resume typed observed
    have holds := observe_typed contracts target row configuration typed
    simpa only [observed] using holds

theorem typed_prefix (contracts : Contracts engine) (typed : Typing contracts parts items rows)
    (observedPrefix : Prefix engine.observe (start parts) requests configuration) :
    ConfigurationTyped contracts (union items) (union rows) configuration ∧
      ∀ request ∈ requests, union rows request :=
  prefix_safe (engine_safe contracts _ _) (start_typed typed) observedPrefix

/-- Termination is a conclusion only when the observed configuration returns.
The safety theorem above applies just as well to nonterminating prefixes. -/
theorem returned_items_typed (contracts : Contracts engine) (typed : Typing contracts parts items rows)
    (observedPrefix : Prefix engine.observe (start parts) requests configuration)
    (returned : engine.observe configuration = .value values) :
    (∀ value ∈ values, union items value) ∧ ∀ request ∈ requests, union rows request := by
  obtain ⟨configurationTyped, requestsTyped⟩ := typed_prefix contracts typed observedPrefix
  exact ⟨(engine_safe contracts _ _).value _ _ configurationTyped returned, requestsTyped⟩

theorem typed_prefix_progress (contracts : Contracts engine) (typed : Typing contracts parts items rows)
    (observedPrefix : Prefix engine.observe (start parts) requests configuration) :
    (∃ values, engine.observe configuration = .value values ∧ ∀ value ∈ values, union items value) ∨
    (∃ next, engine.observe configuration = .tick next ∧
      ConfigurationTyped contracts (union items) (union rows) next) ∨
    (∃ occurrence payload resume, engine.observe configuration = .request occurrence payload resume ∧
      union rows occurrence ∧ ∀ response, ConfigurationTyped contracts (union items) (union rows) (resume response)) :=
  progress (engine_safe contracts _ _) (typed_prefix contracts typed observedPrefix).1

/-! ## Exact ordered composition of finite source and traversal prefixes -/

theorem source_prefix (engine : Engine n signature Source Conversion Dictionary Value SourceState FoldState)
    (part : Part Source Conversion Dictionary) (rest : List (Part Source Conversion Dictionary))
    (values : List Value) (observedPrefix : Prefix engine.source first requests last) :
    Prefix engine.observe ⟨values, .evaluating part rest first⟩ requests ⟨values, .evaluating part rest last⟩ := by
  induction observedPrefix with
  | refl => exact .refl
  | cons step tail ih =>
      cases step with
      | tick observed =>
          exact .cons (.tick (by simp only [Engine.observe, observed])) ih
      | @answer occurrence payload resume observed response =>
          exact .cons (.answer (payload := payload)
            (resume := fun response => ⟨values, .evaluating part rest (resume response)⟩)
            (by simp only [Engine.observe, observed]) response) ih

/-- During an arbitrary traversal prefix the remaining source syntax is
unchanged. Exactly its yielded items are appended, with no conversion map. -/
theorem traversal_prefix (engine : Engine n signature Source Conversion Dictionary Value SourceState FoldState)
    (dictionary : Dictionary) (rest : List (Part Source Conversion Dictionary)) (values : List Value)
    (observedPrefix : FoldTraversal.Prefix (engine.fold dictionary).observe first items requests last) :
    Prefix engine.observe ⟨values, .traversing dictionary rest first⟩ requests
      ⟨values ++ items, .traversing dictionary rest last⟩ := by
  induction observedPrefix generalizing values with
  | refl => simpa using (Prefix.refl (process := engine.observe)
      (state := ⟨values, .traversing dictionary rest _⟩))
  | @cons first items requests next later laterRequests last step tail ih =>
      cases step with
      | tick observed =>
          exact .cons (.tick (by simp only [Engine.observe, observed])) (ih values)
      | @yield item next observed =>
          have advanced : Step engine.observe ⟨values, .traversing dictionary rest first⟩ []
              ⟨values ++ [item], .traversing dictionary rest next⟩ :=
            .tick (by simp only [Engine.observe, observed])
          simpa only [List.append_assoc] using
            Prefix.cons advanced (ih (values ++ [item]))
      | @answer occurrence payload resume observed response =>
          exact .cons (.answer (payload := payload)
            (resume := fun response => ⟨values, .traversing dictionary rest (resume response)⟩)
            (by simp only [Engine.observe, observed]) response) (ih values)

inductive PartMeaning (engine : Engine n signature Source Conversion Dictionary Value SourceState FoldState) :
    Part Source Conversion Dictionary → List Value → Row n Key → Prop where
  | element : Prefix engine.source (engine.startSource code) requests state →
      engine.source state = .value value →
      PartMeaning engine (.element code conversion) [engine.convert conversion value] requests
  | spread : Prefix engine.source (engine.startSource code) sourceRequests state →
      engine.source state = .value container →
      FoldTraversal.Prefix (engine.fold dictionary).observe ((engine.fold dictionary).start container)
        items traversalRequests last → (engine.fold dictionary).observe last = .done →
      PartMeaning engine (.spread code dictionary) items (sourceRequests ++ traversalRequests)

inductive Meaning (engine : Engine n signature Source Conversion Dictionary Value SourceState FoldState) :
    List (Part Source Conversion Dictionary) → List Value → Row n Key → Prop where
  | nil : Meaning engine [] [] []
  | cons : PartMeaning engine part items requests → Meaning engine rest later laterRequests →
      Meaning engine (part :: rest) (items ++ later) (requests ++ laterRequests)

theorem part_meaning_prefix (engine : Engine n signature Source Conversion Dictionary Value SourceState FoldState)
    (rest : List (Part Source Conversion Dictionary)) (values : List Value)
    (meaning : PartMeaning engine part items requests) :
    Prefix engine.observe ⟨values, .ready (part :: rest)⟩ requests ⟨values ++ items, .ready rest⟩ := by
  cases meaning with
  | @element code requests state value conversion source returned =>
      have begins : Step engine.observe ⟨values, .ready (.element code conversion :: rest)⟩ []
          ⟨values, .evaluating (.element code conversion) rest (engine.startSource code)⟩ := .tick rfl
      have finishes : Prefix engine.observe ⟨values, .evaluating (.element code conversion) rest state⟩ []
          ⟨values ++ [engine.convert conversion value], .ready rest⟩ :=
        .cons (.tick (by simp only [Engine.observe, returned])) .refl
      simpa using Prefix.cons begins ((source_prefix engine (.element code conversion) rest values source).trans finishes)
  | @spread code sourceRequests state container dictionary items traversalRequests last source returned traversed done =>
      have begins : Step engine.observe ⟨values, .ready (.spread code dictionary :: rest)⟩ []
          ⟨values, .evaluating (.spread code dictionary) rest (engine.startSource code)⟩ := .tick rfl
      have traverse := traversal_prefix engine dictionary rest values traversed
      have finished : Prefix engine.observe ⟨values ++ items, .traversing dictionary rest last⟩ []
          ⟨values ++ items, .ready rest⟩ :=
        .cons (.tick (by simp only [Engine.observe, done])) .refl
      have startsFold : Step engine.observe ⟨values, .evaluating (.spread code dictionary) rest state⟩ []
          ⟨values, .traversing dictionary rest ((engine.fold dictionary).start container)⟩ :=
        .tick (by simp only [Engine.observe, returned])
      have enters : Prefix engine.observe ⟨values, .evaluating (.spread code dictionary) rest state⟩ traversalRequests
          ⟨values ++ items, .ready rest⟩ := by
        simpa using Prefix.cons startsFold (traverse.trans finished)
      simpa using Prefix.cons begins ((source_prefix engine _ rest values source).trans enters)

theorem meaning_prefix (engine : Engine n signature Source Conversion Dictionary Value SourceState FoldState)
    (values : List Value) (meaning : Meaning engine parts items requests) :
    Prefix engine.observe ⟨values, .ready parts⟩ requests ⟨values ++ items, .ready []⟩ := by
  induction meaning generalizing values with
  | nil => simpa using (Prefix.refl (process := engine.observe) (state := ⟨values, .ready []⟩))
  | cons head tail ih =>
      simpa only [List.append_assoc] using (part_meaning_prefix engine _ values head).trans (ih _)

theorem meaning_returns (meaning : Meaning engine parts items requests) :
    Prefix engine.observe (start parts) requests ⟨items, .ready []⟩ ∧
      engine.observe ⟨items, .ready []⟩ = .value items := by
  exact ⟨by simpa [start] using meaning_prefix engine [] meaning, rfl⟩

end Yulang.FoldListSpread
