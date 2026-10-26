import YulangClosure.OriginalRecursivePair
import YulangClosure.OriginalSourceEnvironment

/-!
Computed native immutable-cell/view and saved-environment readout for the
actual parameter bind. This is a partial constructor supplier, not a full
source-owned PhiW result: the existing formal Return telescope does not yet
supply its SG §3.3 retained Shared/EventField evidence output.

Every native cell is read, including every Some outside an arbitrary Store's
count. Finite support is separately derived from the actual list/Vec
projection. No view tag is used as semantic validity evidence.
-/
namespace YulangClosure.OriginalWorldReadout

open NativeClosureEnvironment SourceIdentityWorld OriginalSourceInterpretation
open OriginalRecursivePair OriginalSourceEnvironment

/-- Exact projection of an actual native vector of optional cell contents. -/
def vectorCell : List (Option V) → Nat → Option V
  | [], _ => none
  | cell :: _, 0 => cell
  | _ :: rest, index + 1 => vectorCell rest index

def vectorStore (cells : List (Option V)) : Store V :=
  ⟨cells.length, vectorCell cells⟩

theorem vector_cell_beyond (cells : List (Option V)) (index : Nat)
    (outside : cells.length ≤ index) : vectorCell cells index = none := by
  induction cells generalizing index with
  | nil => rfl
  | cons head tail ih =>
      cases index with
      | zero => exact False.elim ((Nat.not_succ_le_zero _) outside)
      | succ index => exact ih index (Nat.le_of_succ_le_succ outside)

theorem vector_some_bound (cells : List (Option V)) (index : Nat) (value : V)
    (present : (vectorStore cells).cell index = some value) : index < (vectorStore cells).size := by
  by_cases bounded : index < (vectorStore cells).size
  · exact bounded
  · have empty := vector_cell_beyond cells index (Nat.le_of_not_gt bounded)
    change vectorCell cells index = some value at present
    rw [empty] at present
    cases present

theorem vector_cell_append (cells : List (Option V)) (value : V) (index : Nat) :
    vectorCell (cells ++ [some value]) index =
      if index = cells.length then some value else vectorCell cells index := by
  induction cells generalizing index with
  | nil => cases index <;> simp [vectorCell]
  | cons head tail ih => cases index <;> simp [vectorCell, ih]

theorem vector_store_push (cells : List (Option V)) (value : V) :
    vectorStore (cells ++ [some value]) = (vectorStore cells).push value := by
  unfold vectorStore Store.push
  simp only [List.length_append, List.length_cons, List.length_nil]
  congr 1
  funext index
  exact vector_cell_append cells value index

/-- One original joint logical assignment, indexed by actual cell address
and view, plus raw payload/root projections. Equal native view tokens do not
force equal installed descriptions at different binding positions. These are
data interpretations, not certificates attached to native tags. -/
structure ViewAssignment (s : Sorts) (V : Type) where
  descriptor : Nat → Nat → s.Descriptor
  interface : Nat → Nat → s.Interface
  value : V → s.Value
  carrier : V → s.Carrier
  root : V → s.Root

def ViewAssignment.received (assignment : ViewAssignment s V) (index : Nat) (raw : Received V) : Installed s :=
  match raw.interface with
  | .value => .value (assignment.descriptor index raw.view) (assignment.value raw.value) (assignment.root raw.value)
  | .computation => .carrier (assignment.interface index raw.view) (assignment.carrier raw.value) (assignment.root raw.value)

def bindingReadout (assignment : ViewAssignment s V) (store : Store (Received V)) :
    Nat → Option (Installed s) :=
  fun index => (store.cell index).map (assignment.received index)

/-- All Some cells are interpreted; no scan bounded by count defines meaning. -/
theorem every_cell_readout (assignment : ViewAssignment s V) (store : Store (Received V))
    (index : Nat) (raw : Received V) (present : store.cell index = some raw) :
    bindingReadout assignment store index = some (assignment.received index raw) := by
  simp only [bindingReadout, present, Option.map_some]

theorem interpreted_some_has_native_bound (assignment : ViewAssignment s V)
    (cells : List (Option (Received V))) (index : Nat) (object : Installed s)
    (present : bindingReadout assignment (vectorStore cells) index = some object) :
    index < cells.length := by
  cases stored : (vectorStore cells).cell index with
  | none => simp only [bindingReadout, stored, Option.map_none, reduceCtorEq] at present
  | some raw => exact vector_some_bound cells index raw stored

def returnRow (assignment : ViewAssignment s V) (event : Event s)
    (descriptor : s.Descriptor) (raw : Received V) : ValueRow s :=
  ⟨descriptor, assignment.value raw.value, assignment.root raw.value, event⟩

theorem as_value_is_actual_return (assignment : ViewAssignment s V) (index : Nat) (raw : Received V) :
    assignment.received index raw.asValue =
      .value (assignment.descriptor index raw.view) (assignment.value raw.value) (assignment.root raw.value) := rfl

/-- Exact bind/readout commutation for installed fields, constructed from
Store.push and the one original view assignment. No registry equality premise. -/
theorem push_binding_readout (assignment : ViewAssignment s V) (store : Store (Received V))
    (raw : Received V) :
    bindingReadout assignment (store.push raw) =
      extendBindings (bindingReadout assignment store) store.size (assignment.received store.size raw) := by
  funext index
  by_cases same : index = store.size
  · subst index
    simp only [bindingReadout, Store.push, extendBindings, ite_true, Option.map_some]
  · simp only [bindingReadout, Store.push, extendBindings, ite_eq_right same]

theorem parameter_bind_readout (assignment : ViewAssignment s V)
    (world : World K D V ViewData Site Rest) (parent : Nat) (formal : K)
    (raw : Received V) (node : Node K D)
    (found : nodeAt world.environments parent = some node) :
    bindingReadout assignment (bindValue world parent formal raw node found).cells =
      extendBindings (bindingReadout assignment world.cells) world.cells.size
        (.value (assignment.descriptor world.cells.size raw.view) (assignment.value raw.value) (assignment.root raw.value)) :=
  push_binding_readout assignment world.cells raw.asValue

theorem parameter_bind_actual_return (assignment : ViewAssignment s V)
    (world : World K D V ViewData Site Rest) (parent : Nat) (formal : K)
    (raw : Received V) (node : Node K D)
    (found : nodeAt world.environments parent = some node) :
    bindingReadout assignment (bindValue world parent formal raw node found).cells world.cells.size =
      some (.value (assignment.descriptor world.cells.size raw.view) (assignment.value raw.value) (assignment.root raw.value)) := by
  rw [parameter_bind_readout]
  exact extend_bindings_new _ _ _

/-- Preservation covers every old populated native cell, without asking the
semantic consumer to restrict its original all-Some world quantifier. -/
theorem parameter_bind_every_old (assignment : ViewAssignment s V)
    (world : World K D V ViewData Site Rest) (cells : List (Option (Received V)))
    (actualCells : world.cells = vectorStore cells) (parent : Nat) (formal : K)
    (raw : Received V) (node : Node K D)
    (found : nodeAt world.environments parent = some node)
    (index : Nat) (previous : Installed s)
    (present : bindingReadout assignment world.cells index = some previous) :
    bindingReadout assignment (bindValue world parent formal raw node found).cells index = some previous := by
  rw [parameter_bind_readout]
  apply extend_bindings_old _ present
  rw [actualCells]
  simp only [bindingReadout, vectorStore]
  rw [vector_cell_beyond cells cells.length (Nat.le_refl _)]
  rfl

theorem parameter_bind_native_vector (world : World K D V ViewData Site Rest)
    (cells : List (Option (Received V))) (actualCells : world.cells = vectorStore cells)
    (parent : Nat) (formal : K) (raw : Received V) (node : Node K D)
    (found : nodeAt world.environments parent = some node) :
    (bindValue world parent formal raw node found).cells = vectorStore (cells ++ [some raw.asValue]) := by
  change world.cells.push raw.asValue = _
  rw [actualCells, vector_store_push]

/-- The computed installed fields can now consume the actual typed Return
row and old binding certificates. This supplies only PhiW's recursive binding
conjunct; no Shared/EventField or complete-world premise is smuggled into it. -/
theorem parameter_bind_recursive_fields (assignment : ViewAssignment s V)
    (world : World K D V ViewData Site Rest) (parent : Nat) (formal : K)
    (raw : Received V) (node : Node K D) (found : nodeAt world.environments parent = some node)
    (candidate : Family s) (event : Event s)
    (old : ∀ index previous, bindingReadout assignment world.cells index = some previous →
      previous.Valid candidate event)
    (returned : candidate (.value (returnRow assignment event (assignment.descriptor world.cells.size raw.view) raw))) :
    ∀ index object, bindingReadout assignment (bindValue world parent formal raw node found).cells index =
      some object → object.Valid candidate event := by
  intro index object present
  rw [parameter_bind_readout] at present
  unfold extendBindings at present
  split at present
  · cases Option.some.inj present
    exact returned
  · exact old index object present

/-- Applied at the accepted pair's actual post-Force entry step, with its
current returned world and the closure's original captured environment. -/
theorem pair_parameter_step_readout [DecidableEq K] [DecidableEq V]
    (assignment : ViewAssignment s V) (world : World K D V ViewData Site Rest)
    (suffix : Suffix K Site) (raw : Received V) (node : Node K D)
    (found : nodeAt world.environments suffix.capturedEnvironment = some node) :
    OriginalRecursivePair.suffixStep suffix (.entry world raw) = some (.body
      (bindValue world suffix.capturedEnvironment suffix.formal raw node found) world.environments.size) ∧
    bindingReadout assignment
      (bindValue world suffix.capturedEnvironment suffix.formal raw node found).cells =
      extendBindings (bindingReadout assignment world.cells) world.cells.size
        (.value (assignment.descriptor world.cells.size raw.view) (assignment.value raw.value) (assignment.root raw.value)) := by
  refine ⟨?_, parameter_bind_readout assignment world suffix.capturedEnvironment suffix.formal raw node found⟩
  simp only [OriginalRecursivePair.suffixStep]
  split
  · rename_i absent
    cases absent.symm.trans found
  · rename_i other present
    have same : other = node := Option.some.inj (present.symm.trans found)
    subst other
    rfl

/-- Dispatch at the chosen parent may be unrelated to the latest node.
The rest includes the dictionary machine; bind itself does not mutate it. -/
theorem parameter_bind_preserves_other_fields (world : World K D V ViewData Site Rest)
    (parent : Nat) (formal : K) (raw : Received V) (node : Node K D)
    (found : nodeAt world.environments parent = some node) :
    (bindValue world parent formal raw node found).receiving = world.receiving ∧
    (bindValue world parent formal raw node found).control = world.control ∧
    (bindValue world parent formal raw node found).rest = world.rest ∧
    nodeAt (bindValue world parent formal raw node found).environments world.environments.size =
      some ⟨some parent, some (formal, world.cells.size), node.dispatch⟩ := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  simp only [bindValue, extendNode, nodeAt, ite_true]

theorem parameter_bind_preserves_old_environments (world : World K D V ViewData Site Rest)
    (parent : Nat) (formal : K) (raw : Received V) (node : Node K D)
    (found : nodeAt world.environments parent = some node) (index : Nat)
    (old : index < world.environments.size) :
    nodeAt (bindValue world parent formal raw node found).environments index =
      nodeAt world.environments index :=
  nodeAt_old world.environments parent index (some (formal, world.cells.size)) node.dispatch old

/-- Physical native arena invariant: every binder contains an allocated cell
address. It has no type, witness, provider-safety, or world-validity premise. -/
def AddressesWithin : Arena K D → Nat → Prop
  | .root _, _ => True
  | .append old _ binder _, count =>
      AddressesWithin old count ∧ ∀ key address, binder = some (key, address) → address < count

theorem addresses_root (dispatch : D) (count : Nat) :
    AddressesWithin (.root dispatch : Arena K D) count := True.intro

/-- Native extend can refer to any allocated existing cell. Together with
root and parameter allocation, this establishes the address invariant from
its actual construction operations. It asserts nothing about overwrites. -/
theorem addresses_extend_existing {arena : Arena K D} {count : Nat}
    (within : AddressesWithin arena count) (parent : Nat) (key : K) (cell : Nat)
    (allocated : cell < count) (dispatch : D) :
    AddressesWithin (.append arena parent (some (key, cell)) dispatch) count := by
  refine ⟨within, ?_⟩
  intro other address same
  have equal := Option.some.inj same
  rw [← (Prod.mk.inj equal).2]
  exact allocated

theorem addresses_monotone {arena : Arena K D} {first second : Nat}
    (within : AddressesWithin arena first) (larger : first ≤ second) : AddressesWithin arena second := by
  induction arena with
  | root _ => trivial
  | append old parent binder dispatch ih =>
      exact ⟨ih within.1, fun key address present => Nat.lt_of_lt_of_le (within.2 key address present) larger⟩

theorem addresses_parameter_bind (world : World K D V ViewData Site Rest)
    (within : AddressesWithin world.environments world.cells.size) (parent : Nat) (formal : K)
    (raw : Received V) (node : Node K D) (found : nodeAt world.environments parent = some node) :
    AddressesWithin (bindValue world parent formal raw node found).environments
      (bindValue world parent formal raw node found).cells.size := by
  refine ⟨addresses_monotone within (Nat.le_succ _), ?_⟩
  intro key address same
  have equal : (formal, world.cells.size) = (key, address) := Option.some.inj same
  rw [← (Prod.mk.inj equal).2]
  exact Nat.lt_succ_self _

theorem lookup_address_bound [DecidableEq K] (arena : Arena K D) (count : Nat)
    (within : AddressesWithin arena count) (key : K) (environment address : Nat)
    (found : lookupKey key arena environment = some address) : address < count := by
  induction arena generalizing environment with
  | root dispatch => simp only [lookupKey, lookup, reduceCtorEq] at found
  | append old parent binder dispatch ih =>
      simp only [lookupKey, lookup] at found
      by_cases atNew : environment = old.size
      · rw [ite_eq_left atNew] at found
        cases binder with
        | none => exact ih within.1 parent found
        | some pair =>
            rcases pair with ⟨other, cell⟩
            by_cases sameKey : other = key
            · simp only [sameKey, decide_true, ite_true, Option.some.injEq] at found
              subst address
              exact within.2 other cell rfl
            · simp only [sameKey, decide_false, Bool.false_eq_true, ite_false] at found
              exact ih within.1 parent found
      · rw [ite_eq_right atNew] at found
        exact ih within.1 environment found

/-- Raw capture resolution uses the actual closure's saved environment and
its resolved body references. It never replaces savedEnvironment by latest. -/
def captureAddress [DecidableEq K] (arena : Arena K D) (closure : Closure Body)
    (references : Body → Nat → Option K) (name : Nat) : Option Nat :=
  (references closure.body name).bind (fun key => lookupKey key arena closure.savedEnvironment)

theorem capture_address_bound [DecidableEq K] (arena : Arena K D) (count : Nat)
    (within : AddressesWithin arena count) (closure : Closure Body)
    (references : Body → Nat → Option K) (name address : Nat)
    (found : captureAddress arena closure references name = some address) : address < count := by
  unfold captureAddress at found
  cases reference : references closure.body name with
  | none => simp only [reference, Option.bind_none, reduceCtorEq] at found
  | some key =>
      simp only [reference, Option.bind_some] at found
      exact lookup_address_bound arena count within key closure.savedEnvironment address found

/-- The exact Pair CaptureData record is constructed from actual raw saved
lookup and cell contents. Its object and bound are proved, not supplied as
semantic readout equations or typing evidence. -/
def resolvedCaptureData [DecidableEq K] (assignment : ViewAssignment s V)
    (world : World K D V ViewData Site Rest)
    (within : AddressesWithin world.environments world.cells.size) (closure : Closure Body)
    (references : Body → Nat → Option K) (name address : Nat)
    (resolved : captureAddress world.environments closure references name = some address)
    (raw : Received V) (stored : world.cells.cell address = some raw) :
    CaptureData (bindingReadout assignment world.cells) world.cells.size :=
  ⟨address, capture_address_bound world.environments world.cells.size within closure references name address resolved,
    assignment.received address raw, every_cell_readout assignment world.cells address raw stored⟩

theorem resolved_capture_data_fields [DecidableEq K] (assignment : ViewAssignment s V)
    (world : World K D V ViewData Site Rest)
    (within : AddressesWithin world.environments world.cells.size) (closure : Closure Body)
    (references : Body → Nat → Option K) (name address : Nat)
    (resolved : captureAddress world.environments closure references name = some address)
    (raw : Received V) (stored : world.cells.cell address = some raw) :
    (resolvedCaptureData assignment world within closure references name address resolved raw stored).address = address ∧
    (resolvedCaptureData assignment world within closure references name address resolved raw stored).object =
      assignment.received address raw := ⟨rfl, rfl⟩

def captureReadout [DecidableEq K] (assignment : ViewAssignment s V)
    (world : World K D V ViewData Site Rest) (closure : Closure Body)
    (references : Body → Nat → Option K) (name : Nat) : Option (Installed s) :=
  (captureAddress world.environments closure references name).bind (bindingReadout assignment world.cells)

theorem capture_address_parameter_bind [DecidableEq K]
    (world : World K D V ViewData Site Rest) (closure : Closure Body)
    (saved : closure.savedEnvironment < world.environments.size)
    (references : Body → Nat → Option K) (name : Nat)
    (parent : Nat) (formal : K) (raw : Received V) (node : Node K D)
    (found : nodeAt world.environments parent = some node) :
    captureAddress (bindValue world parent formal raw node found).environments closure references name =
      captureAddress world.environments closure references name := by
  unfold captureAddress
  cases present : references closure.body name with
  | none => rfl
  | some key =>
      exact lookup_old (fun candidate => decide (candidate = key)) world.environments parent
        closure.savedEnvironment (some (formal, world.cells.size)) node.dispatch saved

/-- All saved captures retain their actual address and complete decorated
cell, even when the new formal shadows that name in the current environment. -/
theorem capture_readout_parameter_bind [DecidableEq K]
    (assignment : ViewAssignment s V) (world : World K D V ViewData Site Rest)
    (within : AddressesWithin world.environments world.cells.size)
    (closure : Closure Body) (saved : closure.savedEnvironment < world.environments.size)
    (references : Body → Nat → Option K) (name : Nat)
    (parent : Nat) (formal : K) (raw : Received V) (node : Node K D)
    (found : nodeAt world.environments parent = some node) :
    captureReadout assignment (bindValue world parent formal raw node found) closure references name =
      captureReadout assignment world closure references name := by
  unfold captureReadout
  rw [capture_address_parameter_bind world closure saved references name parent formal raw node found]
  cases reference : references closure.body name with
  | none => simp only [captureAddress, reference, Option.bind_none]
  | some key =>
      simp only [captureAddress, reference, Option.bind_some]
      cases address : lookupKey key world.environments closure.savedEnvironment with
      | none => rfl
      | some cell =>
          simp only [Option.bind_some, bindingReadout]
          change ((world.cells.push raw.asValue).cell cell).map (assignment.received cell) = _
          rw [push_old _ _ _ (lookup_address_bound world.environments world.cells.size within
            key closure.savedEnvironment cell address)]

theorem parameter_formal_shadows [DecidableEq K]
    (world : World K D V ViewData Site Rest) (parent : Nat) (formal : K)
    (raw : Received V) (node : Node K D) (found : nodeAt world.environments parent = some node) :
    lookupKey formal (bindValue world parent formal raw node found).environments world.environments.size =
      some world.cells.size := parameter_shadows _ _ _ _ _

/-- Registered provider tables may contain arbitrary older saved environments.
No allocator-freshness or site-freshness claim is inferred from provider IDs. -/
theorem every_registered_capture_preserved [DecidableEq K]
    (assignment : ViewAssignment s V) (world : World K D V ViewData Site Rest)
    (within : AddressesWithin world.environments world.cells.size)
    (closures : Provider → Option (Closure Body))
    (saved : ∀ provider closure, closures provider = some closure →
      closure.savedEnvironment < world.environments.size)
    (references : Body → Nat → Option K)
    (parent : Nat) (formal : K) (raw : Received V) (node : Node K D)
    (found : nodeAt world.environments parent = some node) :
    ∀ provider closure, closures provider = some closure → ∀ name,
      captureReadout assignment (bindValue world parent formal raw node found) closure references name =
        captureReadout assignment world closure references name := by
  intro provider closure registered name
  exact capture_readout_parameter_bind assignment world within closure (saved provider closure registered)
    references name parent formal raw node found

/-- Different checked result descriptors retain the same raw return, actual
value/root/event, and source receipt. No view tag certifies either row. -/
theorem checked_return_descriptors (assignment : ViewAssignment s V) (event : Event s)
    (raw : Received V) (first second : s.Descriptor) (different : first ≠ second) :
    (returnRow assignment event first raw).value = (returnRow assignment event second raw).value ∧
    (returnRow assignment event first raw).root = (returnRow assignment event second raw).root ∧
    (returnRow assignment event first raw).event = (returnRow assignment event second raw).event ∧
    returnRow assignment event first raw ≠ returnRow assignment event second raw := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro same
  exact different (congrArg ValueRow.descriptor same)

/-! Existing Shared frames can be projected exactly. These equations preserve
older evidence; they do not invent the missing formal-rebind Shared output. -/
/-- Full original Shared records, retaining binder, entry path, actual event,
bindings, installed records and witness. No field is reconstructed from IDs. -/
def sharedFrames (frames : List (OriginalSource.Frame (Payload s ViewToken))) :
    List (OriginalSource.Frame (Payload s ViewToken)) :=
  frames.filter fun frame => match frame.value.data with
    | .shared _ => true
    | _ => false

theorem actual_return_preserves_older_shared_frames (readout : RuntimeReadout s ViewToken)
    (state : Decoded s ViewToken) (binder : OriginalSource.Binder) (data : Outcome s)
    (event : OriginalSource.ActualEvent (Payload s ViewToken))
    (entryPath : List (OriginalSource.EventStep (Payload s ViewToken))) :
    sharedFrames (decodeFrame readout state
      ⟨binder, ⟨.runtime (.returnRebind data), event⟩, entryPath⟩).fixedFrames =
      sharedFrames state.fixedFrames := by
  simp only [decodeFrame, Decoded.retain, runtime_preserves_prior_fixed_prefix,
    sharedFrames, List.filter_append, List.filter_cons, List.filter_nil,
    Bool.false_eq_true, ite_false, List.append_nil]

def sharedWitnesses (frames : List (OriginalSource.Frame (Payload s ViewToken))) : List s.WitnessValue :=
  frames.filterMap fun frame => match frame.value.data with
    | .shared data => some data.witness
    | _ => none

theorem actual_return_preserves_older_shared (readout : RuntimeReadout s ViewToken)
    (state : Decoded s ViewToken) (binder : OriginalSource.Binder) (data : Outcome s)
    (event : OriginalSource.ActualEvent (Payload s ViewToken))
    (entryPath : List (OriginalSource.EventStep (Payload s ViewToken))) :
    sharedWitnesses (decodeFrame readout state
      ⟨binder, ⟨.runtime (.returnRebind data), event⟩, entryPath⟩).fixedFrames =
      sharedWitnesses state.fixedFrames := by
  simp only [decodeFrame, Decoded.retain, runtime_preserves_prior_fixed_prefix,
    sharedWitnesses, List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
    List.append_nil]

theorem existing_shared_witness_readback (binder : OriginalSource.Binder) (data : Shared s)
    (event : OriginalSource.ActualEvent (Payload s ViewToken))
    (entryPath : List (OriginalSource.EventStep (Payload s ViewToken))) :
    sharedWitnesses [⟨binder, ⟨.shared data, event⟩, entryPath⟩] = [data.witness] := rfl

theorem distinct_shared_assignments_are_observable (binder : OriginalSource.Binder)
    (first second : Shared s) (different : first.witness ≠ second.witness)
    (event : OriginalSource.ActualEvent (Payload s ViewToken))
    (entryPath : List (OriginalSource.EventStep (Payload s ViewToken))) :
    sharedWitnesses [⟨binder, ⟨.shared first, event⟩, entryPath⟩] ≠
      sharedWitnesses [⟨binder, ⟨.shared second, event⟩, entryPath⟩] := by
  intro same
  exact different (List.cons.inj same).1

/-- Current Event witness readout remains independent of the older Shared
projection. Its complete source EventField ownership remains the named gap. -/
theorem actual_return_current_witness (readout : RuntimeReadout s ViewToken)
    (state : Decoded s ViewToken) (binder : OriginalSource.Binder) (data : Outcome s) :
    (state.runtime readout binder (.returnRebind data)).assignment.event.witness =
      readout.witness state.fixedFrames state.assignment.event binder (.returnRebind data) := rfl


/-! Small actual-operation probes. These assert raw data equations, not that
views or native cells carry semantic typing certificates. -/
namespace Discriminator

def first : Received Nat := ⟨10, .value, 0, none⟩
def unrelated : Received Nat := ⟨99, .value, 1, some 6⟩
def incoming : Received Nat := ⟨20, .value, 2, some 9⟩

def arena : Arena Nat Nat :=
  .append (.append (.root 3) 0 (some (7, 0)) 11) 0 (some (8, 1)) 22

def world : World Nat Nat Nat Unit Nat Nat where
  environments := arena
  cells := vectorStore [some first, some unrelated]
  receiving :=
    {views := vectorStore [some ⟨10, ()⟩, some ⟨99, ()⟩, some ⟨20, ()⟩]
     receipts := vectorStore []
     index := fun _ => none}
  control := {invocations := vectorStore [], active := [], current := .moduleRun}
  rest := 47

def closure : Closure Unit := capture 1 ()
def references (_ : Unit) (name : Nat) : Option Nat := if name = 0 then some 7 else none

def bound : World Nat Nat Nat Unit Nat Nat :=
  bindValue world 1 7 incoming ⟨some 0, some (7, 0), 11⟩ (by rfl)

theorem physical_address_invariant : AddressesWithin world.environments world.cells.size := by
  apply addresses_extend_existing
  · apply addresses_extend_existing (addresses_root 3 2) 0 7 0 (by decide) 11
  · decide

theorem nonlatest_capture_and_formal_shadow :
    closure.savedEnvironment < world.environments.size - 1 ∧
    captureAddress bound.environments closure references 0 = some 0 ∧
    lookupKey (7 : Nat) bound.environments world.environments.size = some 2 ∧
    bound.cells.cell 0 = some first ∧ bound.cells.cell 2 = some incoming :=
  ⟨by decide, rfl, rfl, rfl, rfl⟩

theorem saved_capture_full_readout (assignment : ViewAssignment s Nat) :
    captureReadout assignment bound closure references 0 = some (assignment.received 0 first) ∧
    captureReadout assignment world closure references 0 = some (assignment.received 0 first) := ⟨rfl, rfl⟩

theorem selected_parent_dispatch_and_rest :
    (nodeAt bound.environments world.environments.size).map Node.dispatch = some 11 ∧
    bound.receiving = world.receiving ∧ bound.rest = 47 := ⟨rfl, rfl, rfl⟩

/-- Identical native cells and views do not determine the logical checked
assignment. Neither decorated result is asserted valid merely by reading it. -/
theorem same_cells_distinct_logical_assignments (firstAssignment secondAssignment : ViewAssignment s Nat)
    (different : firstAssignment.descriptor 0 0 ≠ secondAssignment.descriptor 0 0) :
    bindingReadout firstAssignment world.cells 0 ≠ bindingReadout secondAssignment world.cells 0 := by
  intro same
  have objects := Option.some.inj same
  exact different (Installed.value.inj objects).1

/-- One joint assignment may give different retained contracts to two actual
cells with the identical raw received value and view. Capture resolution must
therefore preserve the address, not merely the native view token. -/
theorem same_view_separate_cell_contracts (assignment : ViewAssignment s Nat)
    (different : assignment.descriptor 0 first.view ≠ assignment.descriptor 1 first.view) :
    bindingReadout assignment (vectorStore [some first, some first]) 0 ≠
      bindingReadout assignment (vectorStore [some first, some first]) 1 := by
  intro same
  have objects := Option.some.inj same
  exact different (Installed.value.inj objects).1

def sameViewWorld : World Nat Nat Nat Unit Nat Nat :=
  {world with
    environments := .append (.append (.root 3) 0 (some (7, 0)) 11) 1 (some (8, 1)) 22
    cells := vectorStore [some first, some first]}

def twoReferences (_ : Unit) (name : Nat) : Option Nat := if name = 0 then some 7 else some 8

theorem capture_same_view_keeps_exact_cell (assignment : ViewAssignment s Nat)
    (different : assignment.descriptor 0 first.view ≠ assignment.descriptor 1 first.view) :
    captureAddress sameViewWorld.environments (capture 2 ()) twoReferences 0 = some 0 ∧
    captureAddress sameViewWorld.environments (capture 2 ()) twoReferences 1 = some 1 ∧
    captureReadout assignment sameViewWorld (capture 2 ()) twoReferences 0 ≠
      captureReadout assignment sameViewWorld (capture 2 ()) twoReferences 1 := by
  refine ⟨rfl, rfl, ?_⟩
  intro same
  have objects := Option.some.inj same
  exact different (Installed.value.inj objects).1

end Discriminator

end YulangClosure.OriginalWorldReadout
