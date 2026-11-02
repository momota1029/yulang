import YulangClosure.SourceDeclarationNoninterferenceR296
import YulangClosure.OriginalScopedClosure

/-!
R297: actual source-occurrence preallocation and its existing owner consumer.

This is the source-occurrence portion of IF construction §6's first pass,
not its complete provider/schema allocation or a semantic Graph supplier.
Every scoped Program node is retained, including its complete premises, body,
scope and frame. Original event-owner rows are attached at their actual binder
occurrences. The second pass still needs authentic complete contract schemas,
Call regions/all arms and resolved whole substitutions. No arbitrary catalogue,
successful target lookup, ClosedPrefix or source typing is an input below.
-/
namespace YulangClosure.SourceGraphRegistrationR297

open OriginalSource OriginalScopedClosure

/-- A preallocated occurrence retains its entire original source subtree;
owner rows never replace the source or its independent local premises. -/
structure Row where
  program : Program
  owners : List OriginalSourceEvents.Owner

mutual
def inventory (scope : List OriginalSourceEvents.ScopeEntry) : Program → List Row
  | p@(.rule _ _ _ _ _ children) =>
      ⟨p, []⟩ :: forestInventory scope children
  | p@(.existsE occurrence body) | p@(.forallE occurrence body)
  | p@(.executionE occurrence body) | p@(.sharedE occurrence body) =>
      ⟨p, OriginalSourceEvents.binderOwner occurrence.position.route scope occurrence.binder⟩ ::
        inventory (OriginalSourceEvents.extendScope scope occurrence.position.route occurrence.binder) body
  | p@(.initializerE _ _ body) | p@(.publishGroup _ _ body)
  | p@(.atPublication _ _ body) | p@(.aliasPublication _ _ _ body) =>
      ⟨p, []⟩ :: inventory scope body
  | p@(.choice _ _ left right) =>
      ⟨p, []⟩ :: (inventory scope left ++ inventory scope right)
def forestInventory (scope : List OriginalSourceEvents.ScopeEntry) : Programs → List Row
  | .nil => []
  | .cons head tail => inventory scope head ++ forestInventory scope tail
end

def sourceInventory (origin : Declaration) (context : Context) (raw : Source category) : List Row :=
  inventory [] (source origin context raw)

/-- Allocation does not use labels as row identities. Every constructor,
including a repeated source site or an empty owner list, gets its own row. -/
theorem inventory_root (scope : List OriginalSourceEvents.ScopeEntry) (program : Program) :
    ∃ row, (inventory scope program)[0]? = some row ∧ row.program = program := by
  cases program <;> exact ⟨_, rfl, rfl⟩

mutual
theorem inventory_owners_allocate (position : Position) (scope : List OriginalSourceEvents.ScopeEntry)
    (tree : RuleTree) :
    (inventory scope (allocate position tree)).flatMap Row.owners =
      OriginalSourceEvents.owners position.route scope tree := by
  cases tree <;>
    simp [allocate, inventory, OriginalSourceEvents.owners, inventory_owners_allocate,
      forest_inventory_owners_allocate, Position.child, Position.under, atBinder]
  all_goals split <;> rfl
theorem forest_inventory_owners_allocate (position : Position) (scope : List OriginalSourceEvents.ScopeEntry)
    (trees : RuleForest) :
    (forestInventory scope (allocateForest position trees)).flatMap Row.owners =
      OriginalSourceEvents.forestOwners position.route scope trees := by
  cases trees <;>
    simp [allocateForest, forestInventory, OriginalSourceEvents.forestOwners,
      inventory_owners_allocate, forest_inventory_owners_allocate, Position.child]
end

/-- All original Source categories and constructors, with no admission premise. -/
theorem source_owner_rows (origin : Declaration) (context : Context) (raw : Source category) :
    (sourceInventory origin context raw).flatMap Row.owners = OriginalSourceEvents.sourceOwners context raw :=
  inventory_owners_allocate ⟨origin, [], [], []⟩ [] (sourceRules context raw)

/-- The binder that actually emitted an owner. Non-binder nodes never pass
this test, even when their numeric source labels happen to coincide. -/
def AtBinder (program : Program) (owner : OriginalSourceEvents.Owner) : Prop :=
  match program with
  | .existsE occurrence _ | .forallE occurrence _
  | .executionE occurrence _ | .sharedE occurrence _ =>
      occurrence.position.route = owner.route ∧ occurrence.binder = owner.binder
  | _ => False

private theorem binder_owner_fields (route : OriginalSourceEvents.Route)
    (scope : List OriginalSourceEvents.ScopeEntry) (binder : Binder)
    (owner : OriginalSourceEvents.Owner)
    (member : owner ∈ OriginalSourceEvents.binderOwner route scope binder) :
    route = owner.route ∧ binder = owner.binder := by
  unfold OriginalSourceEvents.binderOwner at member
  split at member
  · simp only [List.mem_singleton] at member
    subst owner
    exact ⟨rfl, rfl⟩
  · split at member
    · simp only [List.mem_singleton] at member
      subst owner
      exact ⟨rfl, rfl⟩
    · split at member
      · simp only [List.mem_singleton] at member
        subst owner
        exact ⟨rfl, rfl⟩
      · contradiction

mutual
theorem inventory_owner_at_binder (scope : List OriginalSourceEvents.ScopeEntry)
    (program : Program) (row : Row) (present : row ∈ inventory scope program)
    (owner : OriginalSourceEvents.Owner) (member : owner ∈ row.owners) :
    AtBinder row.program owner := by
  cases program <;> simp only [inventory, List.mem_cons, List.mem_append] at present
  all_goals first
    | obtain rfl | present := present
      · first | contradiction | exact binder_owner_fields _ _ _ _ member
      · first
        | exact forest_inventory_owner_at_binder _ _ _ present _ member
        | exact inventory_owner_at_binder _ _ _ present _ member
        | rcases present with present | present
          · exact inventory_owner_at_binder _ _ _ present _ member
          · exact inventory_owner_at_binder _ _ _ present _ member
theorem forest_inventory_owner_at_binder (scope : List OriginalSourceEvents.ScopeEntry)
    (programs : Programs) (row : Row) (present : row ∈ forestInventory scope programs)
    (owner : OriginalSourceEvents.Owner) (member : owner ∈ row.owners) :
    AtBinder row.program owner := by
  cases programs with
  | nil => contradiction
  | cons head tail =>
      rcases List.mem_append.mp present with present | present
      · exact inventory_owner_at_binder _ _ _ present _ member
      · exact forest_inventory_owner_at_binder _ _ _ present _ member
end

/-- A source-owned declaration is now located at an actual allocated row,
without asking for its desired row lookup as an input. -/
theorem source_owner_registered (origin : Declaration) (context : Context)
    (raw : Source category) (owner : OriginalSourceEvents.Owner)
    (emitted : owner ∈ OriginalSourceEvents.sourceOwners context raw) :
    ∃ (index : Nat) (row : Row), (sourceInventory origin context raw)[index]? = some row ∧
      owner ∈ row.owners ∧ AtBinder row.program owner := by
  rw [← source_owner_rows origin context raw] at emitted
  obtain ⟨row, present, owns⟩ := List.mem_flatMap.mp emitted
  obtain ⟨index, bound, equal⟩ := List.getElem_of_mem present
  exact ⟨index, row, List.getElem?_eq_some_iff.mpr ⟨bound, equal⟩, owns,
    inventory_owner_at_binder _ _ row present owner owns⟩

open OriginalSourceInterpretation OriginalSourceEnvironment

/-- Static Call ownership is extracted from the retained original local
premises, not reconstructed from a type, owner label or semantic endpoint. -/
def Row.callOwner (row : Row) : Option CallOwner :=
  match row.program with
  | .rule _ rule site context premises _ => localCallOwner rule site context premises
  | _ => none

mutual
theorem inventory_call_rows (scope : List OriginalSourceEvents.ScopeEntry) (program : Program) :
    (inventory scope program).flatMap (fun row => row.callOwner.toList) =
      callOwners program.erase := by
  cases program <;>
    simp only [inventory, List.flatMap_cons, List.flatMap_append,
      inventory_call_rows, forest_inventory_call_rows] <;>
    simp [Row.callOwner, Program.erase, callOwners]
theorem forest_inventory_call_rows (scope : List OriginalSourceEvents.ScopeEntry) (programs : Programs) :
    (forestInventory scope programs).flatMap (fun row => row.callOwner.toList) =
      forestCallOwners programs.erase := by
  cases programs <;>
    simp [forestInventory, Programs.erase, forestCallOwners,
      inventory_call_rows, forest_inventory_call_rows]
end

theorem source_call_rows (origin : Declaration) (context : Context) (raw : Source category) :
    (sourceInventory origin context raw).flatMap (fun row => row.callOwner.toList) =
      sourceCallOwners context raw := by
  rw [sourceInventory, inventory_call_rows]
  simp only [source, erase_allocate, sourceCallOwners]

/-- Every actual static Call owner resolves to the preallocated occurrence.
This still does not supply that owner's six semantic regions or arm schemas. -/
theorem source_call_registered (origin : Declaration) (context : Context) (raw : Source category)
    (owner : CallOwner) (emitted : owner ∈ sourceCallOwners context raw) :
    ∃ (index : Nat) (row : Row), (sourceInventory origin context raw)[index]? = some row ∧
      row.callOwner = some owner := by
  rw [← source_call_rows origin context raw] at emitted
  obtain ⟨row, present, owns⟩ := List.mem_flatMap.mp emitted
  obtain ⟨index, bound, equal⟩ := List.getElem_of_mem present
  exact ⟨index, row, List.getElem?_eq_some_iff.mpr ⟨bound, equal⟩,
    Option.mem_toList.mp owns⟩

/-- Applied raw-App case has no assumed registration or lookup. Both arbitrary
source operands remain in the retained scoped program with their full rules. -/
theorem source_application_registered (origin : Declaration) (context : Context) (site : Site)
    (callee argument : Source .expression) :
    ∃ (index : Nat) (row : Row),
      (sourceInventory origin context (.app ⟨site, none⟩ callee argument))[index]? = some row ∧
        row.callOwner = some (.application site context callee.site argument.site) := by
  apply source_call_registered
  rw [source_app_call_owner]
  exact List.mem_cons_self

/-- The existing source-record consumer, reading only the constructed table.
Its original sort test and complete history/assignment input are unchanged. -/
def registeredRecord {s : Sorts} {View : Type}
    (assignment : OriginalSourceEvents.RecordAssignment s View) (origin : Declaration)
    (context : Context) (source : Source category) (index : Nat)
    (parents : List (OriginalSourceEvents.HistoryStep s View)) (occurrence : Nat)
    (raw : OriginalSourceEvents.RawRecord s View) : Option (OriginalSourceEvents.HistoryRecord s View) := do
  let introduction ← (((sourceInventory origin context source).flatMap Row.owners).filter
    (fun introduced => introduced.lifetime == .actualEvent))[index]?
  if introduction.binder.kind = raw.runtime.kind then
    pure (OriginalSourceEvents.instantiateRecord assignment introduction origin parents occurrence raw)
  else none

/-- Applied edge: the new actual source table feeds the unchanged original
consumer for every index, scope, history and raw record, including failure. -/
theorem registered_record_eq_source_record {s : Sorts} {View : Type}
    (assignment : OriginalSourceEvents.RecordAssignment s View) (origin : Declaration)
    (context : Context) (source : Source category) (index : Nat)
    (parents : List (OriginalSourceEvents.HistoryStep s View)) (occurrence : Nat)
    (raw : OriginalSourceEvents.RawRecord s View) :
    registeredRecord assignment origin context source index parents occurrence raw =
      OriginalSourceEvents.sourceRecord assignment context source index origin parents occurrence raw := by
  simp only [registeredRecord, source_owner_rows, OriginalSourceEvents.sourceRecord]

/-- The known computed-App hole survives the real first pass. It cannot be
filled by calling an occurrence/owner inventory a complete Call schema table. -/
theorem computed_record_still_absent {s : Sorts} {View : Type}
    (assignment : OriginalSourceEvents.RecordAssignment s View) (origin : Declaration)
    (context : Context) (f x y : Name) (index : Nat)
    (parents : List (OriginalSourceEvents.HistoryStep s View)) (occurrence : Nat)
    (raw : OriginalSourceEvents.RawRecord s View) :
    registeredRecord assignment origin context
      (ComputedCallSourceSupplierR294.computedSource f x y) index parents occurrence raw = none := by
  rw [registered_record_eq_source_record]
  exact ComputedCallSourceSupplierR294.computed_record_absent
    assignment context f x y index origin parents occurrence raw

end YulangClosure.SourceGraphRegistrationR297
