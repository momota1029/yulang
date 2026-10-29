import YulangClosure.FormalPermissionAuthenticatedSiteExport

/-! R4: the fixed R3 atomic tuple/formal observation, interpreted as mathematical
constructor instructions. Atom numbers encode source constructors, never native
Term identities. `initial` changes only the model's allocation coordinate; it
asserts no equality with an unobserved native State. Native extraction remains
external, as does the original whole-language preservation obligation. -/
namespace YulangClosure.FormalPermissionAuthenticatedNativeDecode
open FormalPermissionSourceOrigin FormalPermissionCaptureConstruction
open FormalPermissionExportWitness FormalPermissionSiteTraversal
open FormalPermissionAuthenticatedSiteExport
open FormalPermissionLiveCapture (prependPath atPort shift shiftPath)
noncomputable section

inductive AtomicSource where
  | int | unit
  deriving DecidableEq

def sourceConstructorCode : AtomicSource → Nat
  | .int => 0
  | .unit => 1

theorem source_constructor_injective : Function.Injective sourceConstructorCode := by
  intro a b h
  cases a <;> cases b <;> simp_all [sourceConstructorCode]

def context : Context := ⟨0, 4, 0, 0⟩
def rootRow : SourceRow := ⟨1, [0], []⟩
def firstRow : SourceRow := ⟨2, [1], []⟩
def secondRow : SourceRow := ⟨3, [2], []⟩
def firstPath : List Step := [.element 0, .result]
def secondPath : List Step := [.element 1, .element 1, .result]
def intLeaf : Annotation := .leaf none .int
def resultLeaf (row : SourceRow) : Annotation := .leaf (some row) .unit
def firstFunction : Annotation := .function none intLeaf (resultLeaf firstRow)
def secondFunction : Annotation := .function none intLeaf (resultLeaf secondRow)
def tree : Annotation := .tuple (some rootRow)
  (.cons firstFunction (.cons (.tuple none
    (.cons intLeaf (.cons secondFunction .nil))) .nil))

/- Full source inventory retains all nine nodes, including the root row and
all six omitted rows. This is separate from the four actual Effect-port calls. -/
mutual
  def sourceNodes : Annotation → List (List Step × Option SourceRow)
    | .leaf e _ => [([], e)]
    | .function e a r => [([], e)] ++
        (sourceNodes a).map (fun x => (.argument :: x.1, x.2)) ++
        (sourceNodes r).map (fun x => (.result :: x.1, x.2))
    | .tuple e xs => [([], e)] ++ sourceElements 0 xs
  def sourceElements (index : Nat) : Annotations → List (List Step × Option SourceRow)
    | .nil => []
    | .cons x xs =>
        (sourceNodes x).map (fun v => (.element index :: v.1, v.2)) ++
        sourceElements (index + 1) xs
end

theorem complete_source_inventory : sourceNodes tree =
    [([], some rootRow), ([.element 0], none),
     ([.element 0, .argument], none), (firstPath, some firstRow),
     ([.element 1], none), ([.element 1, .element 0], none),
     ([.element 1, .element 1], none),
     ([.element 1, .element 1, .argument], none), (secondPath, some secondRow)] := rfl

/- Complete chronological Effect-port traversal, including omitted ports.
The recursive order is value argument, value result, argument port, result
port; Tuple follows every ordered child. Root/bare Tuple rows allocate nothing. -/
mutual
  def orderedPorts (p : Bool) : Annotation → List (List Step × Bool × Option SourceRow)
    | .leaf _ _ => []
    | .function _ a r =>
        (orderedPorts (!p) a).map (fun x => (.argument :: x.1, x.2)) ++
        (orderedPorts p r).map (fun x => (.result :: x.1, x.2)) ++
        [([.argument], !p, a.effects), ([.result], p, r.effects)]
    | .tuple _ xs => orderedElements p 0 xs
  def orderedElements (p : Bool) (index : Nat) : Annotations → List (List Step × Bool × Option SourceRow)
    | .nil => []
    | .cons x xs =>
        (orderedPorts p x).map (fun v => (.element index :: v.1, v.2)) ++
        orderedElements p (index + 1) xs
end

theorem complete_ordered_ports : orderedPorts false tree =
    [([.element 0, .argument], true, none),
     (firstPath, false, some firstRow),
     ([.element 1, .element 1, .argument], true, none),
     (secondPath, false, some secondRow)] := rfl

def code (intCode unitCode : Nat) : ValueCode :=
  .tuple (.cons
    (.function (.scalar intCode) (.scalar unitCode) .omitted (.explicit 2 [1] none))
    (.cons (.tuple (.cons (.scalar intCode) (.cons
      (.function (.scalar intCode) (.scalar unitCode) .omitted (.explicit 3 [2] none))
      .nil))) .nil))

/-- Partial source projection for this atomic slice. Unsupported constructors
are explicit failures, not a restriction on the original parent language.
Root and bare Tuple rows remain in `sourceNodes`; Function uses precisely its
argument/result rows, as the pinned native constructor does. -/
def encodePort : Option SourceRow → Option SourcePort
  | none => some .omitted
  | some row => if row.variables = [] then
      some (.explicit row.position row.concrete none) else none

mutual
  def encodeSource (intCode unitCode : Nat) : Annotation → Option ValueCode
    | .leaf _ .int => some (.scalar intCode)
    | .leaf _ .unit => some (.scalar unitCode)
    | .leaf _ _ => none
    | .function _ a r => do
        let ac ← encodeSource intCode unitCode a
        let rc ← encodeSource intCode unitCode r
        let ae ← encodePort a.effects
        let re ← encodePort r.effects
        pure (.function ac rc ae re)
    | .tuple _ xs => do
        let cs ← encodeElements intCode unitCode xs
        pure (.tuple cs)
  def encodeElements (intCode unitCode : Nat) : Annotations → Option TupleCode
    | .nil => some .nil
    | .cons x xs => do
        let c ← encodeSource intCode unitCode x
        let cs ← encodeElements intCode unitCode xs
        pure (.cons c cs)
end

theorem code_from_exact_source (intCode unitCode : Nat) :
    encodeSource intCode unitCode tree = some (code intCode unitCode) := rfl

def retained (n : Nat) : List Retained :=
  [⟨context.metadata 2 [1], firstPath, n + 1⟩,
   ⟨context.metadata 3 [2], secondPath, n + 3⟩]

/-- All State fields and both atomic tags are universally quantified. This
computes the four births and preserves every unread field by record update. -/
theorem allocation_and_decode (s : State) (intCode unitCode : Nat) :
    ∃ out : ValueDecoded context false s,
      decodeValue context false s (code intCode unitCode) = some out ∧
      out.entries = retained s.nextEffect ∧
      out.births = [s.nextEffect, s.nextEffect + 1, s.nextEffect + 2, s.nextEffect + 3] ∧
      out.state = {s with nextEffect := s.nextEffect + 4} := by
  simp [code, decodeValue, decodeTuple, decodePort, retained, firstPath,
    secondPath, prependPath, atPort, shift, shiftPath, Nat.add_assoc]

def output (s : State) (intCode unitCode : Nat) : ValueDecoded context false s :=
  Classical.choose (allocation_and_decode s intCode unitCode)

theorem output_equations (s : State) (intCode unitCode : Nat) :
    decodeValue context false s (code intCode unitCode) = some (output s intCode unitCode) ∧
    (output s intCode unitCode).entries = retained s.nextEffect ∧
    (output s intCode unitCode).births =
      [s.nextEffect, s.nextEffect + 1, s.nextEffect + 2, s.nextEffect + 3] ∧
    (output s intCode unitCode).state = {s with nextEffect := s.nextEffect + 4} :=
  Classical.choose_spec (allocation_and_decode s intCode unitCode)

/-- Forward recurrence: the first retained result follows the omitted argument.
The complete traversal and allocation theorem establish that this is n+1;
this arithmetic lemma alone is not a native initial-state observation. -/
theorem base_from_forward_allocation (n : Nat) (firstOrigin : n + 1 = 22) :
    n = 21 ∧ [n, n + 1, n + 2, n + 3] = [21, 22, 23, 24] := by
  have h : n = 21 := Nat.add_right_cancel (show n + 1 = 21 + 1 from firstOrigin)
  subst n
  exact ⟨rfl, rfl⟩

def initial (unread : State) : State := {unread with nextEffect := 21}
def snapshot : CaptureSnapshot :=
  ⟨4, 0, [(22, 22), (24, 24)], [((22, false), 17), ((24, false), 14)]⟩
def observations : List Observation :=
  [⟨0, .definition 0, context.metadata 2 [1], firstPath, 22, 22, false, 4, 0, 17, 17⟩,
   ⟨1, .definition 0, context.metadata 3 [2], secondPath, 24, 24, false, 4, 0, 14, 14⟩]

theorem expected_observations :
    expectedAll context snapshot 0 (retained 21) = some observations := by decide

/-- Atomic tags and the seven unread State coordinates cannot alter retained
entries or the full expected observation list. Shapes may still contain tags. -/
theorem tags_and_unread_state_irrelevant (a b : State) (i u j v : Nat) :
    (output (initial a) i u).entries = (output (initial b) j v).entries ∧
    expectedAll context snapshot 0 (output (initial a) i u).entries = some observations ∧
    expectedAll context snapshot 0 (output (initial b) j v).entries = some observations := by
  rw [(output_equations (initial a) i u).2.1,
    (output_equations (initial b) j v).2.1]
  exact ⟨rfl, expected_observations, expected_observations⟩

theorem first_source_port : SourceTreeVisit tree firstPath (some firstRow) ∧ PortPath firstPath := by
  constructor
  · exact .inElement (some rootRow) rfl (.inResult none intLeaf (.root (resultLeaf firstRow)))
  · exact .prepend (.element 0) .result

theorem second_source_port : SourceTreeVisit tree secondPath (some secondRow) ∧ PortPath secondPath := by
  constructor
  · exact .inElement (some rootRow) rfl (.inElement none rfl
      (.inResult none intLeaf (.root (resultLeaf secondRow))))
  · exact .prepend (.element 1) (.prepend (.element 1) .result)

/-- Direct application of the unchanged parent-facing theorem to BOTH retained
ports and the SAME computed output. Every tag choice and unread State is covered;
no native State identity is asserted or assumed. -/
theorem extracted_instance (unread : State) (intCode unitCode : Nat) :
    EffectVisit tree firstPath (some firstRow) ∧
    EffectVisit tree secondPath (some secondRow) ∧
    decodeObserved context (initial unread) (code intCode unitCode) snapshot observations =
      some (output (initial unread) intCode unitCode) := by
  have decoded := (output_equations (initial unread) intCode unitCode).1
  have allEntries : expectedAll context snapshot 0
      (output (initial unread) intCode unitCode).entries = some observations := by
    rw [(output_equations (initial unread) intCode unitCode).2.1]
    exact expected_observations
  have first := extracted_port_and_export context tree firstPath (some firstRow)
    first_source_port.1 first_source_port.2 (initial unread) (code intCode unitCode)
    (output (initial unread) intCode unitCode) snapshot observations decoded allEntries
  have second := extracted_port_and_export context tree secondPath (some secondRow)
    second_source_port.1 second_source_port.2 (initial unread) (code intCode unitCode)
    (output (initial unread) intCode unitCode) snapshot observations decoded allEntries
  exact ⟨first.1, second.1, first.2⟩

/-- The concrete Int/Unit encoding is only a source-constructor encoding. -/
theorem source_coded_instance (unread : State) :
    decodeObserved context (initial unread)
      (code (sourceConstructorCode .int) (sourceConstructorCode .unit)) snapshot observations =
      some (output (initial unread) 0 1) :=
  (extracted_instance unread 0 1).2.2

end
end YulangClosure.FormalPermissionAuthenticatedNativeDecode
