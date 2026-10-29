import YulangClosure.FormalPermissionSourceAllocation

/-! R10 exact-tree conditional supplier. Every nonallocating source helper has
an explicit, local frame premise. No default/empty frame, target SourcePair,
native successful-return witness, or native initial coordinate is assumed.
Allocator permissions contain the arbitrary full prefix; PortResult entries
contain only the local delta. Their execution correspondence remains OPEN. -/
namespace YulangClosure.FormalPermissionSourceInstance
open FormalPermissionSourceOrigin FormalPermissionCaptureConstruction
open FormalPermissionConstructorRealization FormalPermissionExportWitness
open FormalPermissionSiteTraversal FormalPermissionSourceAllocation
open FormalPermissionLiveCapture (prependPath atPort shift shiftPath)
noncomputable section

def Aligned (a : Allocator) : Prop :=
  a.levels.length = a.bounds.length ∧
  a.metadata.length = a.bounds.length ∧ a.marks.length = a.bounds.length

def appendPermission (a : Allocator) (e : Retained) : Allocator :=
  {a with permissions := a.permissions ++ [e]}

def firstEntry (n : Nat) : Retained :=
  ⟨FormalPermissionAuthenticatedNativeDecode.context.metadata 2 [1], FormalPermissionAuthenticatedNativeDecode.firstPath, n + 1⟩
def secondEntry (n : Nat) : Retained :=
  ⟨FormalPermissionAuthenticatedNativeDecode.context.metadata 3 [2], FormalPermissionAuthenticatedNativeDecode.secondPath, n + 3⟩

def afterOne (a : Allocator) (level : Nat) : Allocator := a.push level
def afterTwo (a : Allocator) (level : Nat) : Allocator :=
  appendPermission ((afterOne a level).push level) (firstEntry a.bounds.length)
def afterThree (a : Allocator) (level : Nat) : Allocator := (afterTwo a level).push level
def afterFour (a : Allocator) (level : Nat) : Allocator :=
  appendPermission ((afterThree a level).push level) (secondEntry a.bounds.length)

/-- Four separate successful reservations, at the actual successive vectors.
Owner: lib.rs fresh_effect_at_level/reserve_typed_route_lane!/reserve_f5b.
The fields do not assert that these reservations succeed in a Rust execution. -/
structure Reservations (a : Allocator) (level : Nat) where
  first : FreshReady a.bounds.length
  second : FreshReady (afterOne a level).bounds.length
  third : FreshReady (afterTwo a level).bounds.length
  fourth : FreshReady (afterThree a level).bounds.length

theorem push_aligned (a : Allocator) (level : Nat) (h : Aligned a) :
    Aligned (a.push level) := by
  rcases h with ⟨hl, hm, hz⟩
  simp [Aligned, Allocator.push, hl, hm, hz]

theorem four_allocations_and_prefix (a : Allocator) (level : Nat) (h : Aligned a) :
    Aligned (afterOne a level) ∧ Aligned (afterTwo a level) ∧
    Aligned (afterThree a level) ∧ Aligned (afterFour a level) ∧
    (afterOne a level).bounds.length = a.bounds.length + 1 ∧
    (afterTwo a level).bounds.length = a.bounds.length + 2 ∧
    (afterThree a level).bounds.length = a.bounds.length + 3 ∧
    (afterFour a level).bounds.length = a.bounds.length + 4 ∧
    (afterFour a level).permissions = a.permissions ++ FormalPermissionAuthenticatedNativeDecode.retained a.bounds.length := by
  have h1 := push_aligned a level h
  have h2 := push_aligned (afterOne a level) level h1
  have h2' : Aligned (afterTwo a level) := h2
  have h3 := push_aligned (afterTwo a level) level h2'
  have h4 := push_aligned (afterThree a level) level h3
  refine ⟨h1, h2', h3, h4, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [afterOne, afterTwo, afterThree, afterFour, appendPermission,
      Allocator.push, FormalPermissionAuthenticatedNativeDecode.retained, firstEntry, secondEntry, List.append_assoc,
      Nat.add_assoc]

private def freshStep (a : Allocator) (level : Nat) (h : Aligned a)
    (ready : FreshReady a.bounds.length) : FreshStep a.bounds.length :=
  ⟨a, level, rfl, h.1, h.2.1, h.2.2, ready⟩

/-- No source helper is replaced by the empty HelperFrames constructor. -/
def Frame (n : Nat) (entries : List Retained) : Prop :=
  HelperFrames ⟨n, entries⟩ ⟨n, entries⟩

def localEntry (row : SourceRow) (path : List Step) (n : Nat) : Retained :=
  ⟨FormalPermissionAuthenticatedNativeDecode.context.metadata row.position row.concrete, path, n⟩

/-- Exact per-Function helper obligations. Atomic fields own int/unit term
construction; ports own live_effect_term after the allocation and, for the
result, retained-path/concrete copy and byte-accounting; function owns the
positive_function_term/negative_function_term calls via with_term_events.
A Frame is only the R9 projection obligation, not Rust success authentication. -/
structure FunctionFrames (s : State) (row : SourceRow) where
  argument : Frame s.nextEffect []
  result : Frame s.nextEffect []
  argumentPort : Frame (s.nextEffect + 1) []
  resultPort : Frame (s.nextEffect + 1 + 1)
    [localEntry row [] (s.nextEffect + 1)]
  terms : Frame (s.nextEffect + 1 + 1)
    [localEntry row [.result] (s.nextEffect + 1)]

private theorem omitted_supplier (s : State) (allocation : FreshStep s.nextEffect)
    (helpers : Frame (s.nextEffect + 1) []) :
    SourcePortSuccess FormalPermissionAuthenticatedNativeDecode.context true none s .omitted
      ⟨sharedPorts s.nextEffect, [], [], {s with nextEffect := s.nextEffect + 1}⟩
      [s.nextEffect] := by
  have eqs := fresh_step_equations allocation
  have frames : HelperFrames ⟨allocation.next, []⟩ ⟨s.nextEffect + 1, []⟩ := by
    simpa only [Frame, eqs.2.1] using helpers
  simpa only [eqs.1, List.map_nil] using
    (SourcePortSuccess.omitted (c := FormalPermissionAuthenticatedNativeDecode.context) true s allocation
      ⟨s.nextEffect + 1, []⟩ frames)

private theorem concrete_supplier (s : State) (row : SourceRow)
    (allocation : FreshStep s.nextEffect) (nonempty : row.concrete ≠ [])
    (noVariables : row.variables = [])
    (helpers : Frame (s.nextEffect + 1) [localEntry row [] s.nextEffect]) :
    SourcePortSuccess FormalPermissionAuthenticatedNativeDecode.context false (some row) s
      (.explicit row.position row.concrete none)
      ⟨sharedPorts s.nextEffect (some (FormalPermissionAuthenticatedNativeDecode.context.metadata row.position row.concrete)),
        [⟨FormalPermissionAuthenticatedNativeDecode.context.metadata row.position row.concrete, s.nextEffect⟩], [],
        {s with nextEffect := s.nextEffect + 1}⟩ [s.nextEffect] := by
  have eqs := fresh_step_equations allocation
  have frames : HelperFrames
      ⟨allocation.next, [⟨FormalPermissionAuthenticatedNativeDecode.context.metadata row.position row.concrete, [], allocation.ordinal⟩]⟩
      ⟨s.nextEffect + 1, [localEntry row [] s.nextEffect]⟩ := by
    simpa only [Frame, eqs.1, eqs.2.1, localEntry] using helpers
  simpa only [eqs.1, localEntry, List.map_cons, List.map_nil] using
    (SourcePortSuccess.concrete (c := FormalPermissionAuthenticatedNativeDecode.context) s row allocation nonempty noVariables
      ⟨s.nextEffect + 1, [localEntry row [] s.nextEffect]⟩ frames)

private theorem function_supplier (s : State) (row : SourceRow)
    (allocation1 : FreshStep s.nextEffect)
    (allocation2 : FreshStep (s.nextEffect + 1))
    (nonempty : row.concrete ≠ []) (noVariables : row.variables = [])
    (helpers : FunctionFrames s row) :
    ∃ out : ValueDecoded FormalPermissionAuthenticatedNativeDecode.context false s,
      SourcePair FormalPermissionAuthenticatedNativeDecode.context false
        (.function none FormalPermissionAuthenticatedNativeDecode.intLeaf (FormalPermissionAuthenticatedNativeDecode.resultLeaf row))
        (.function (.scalar 0) (.scalar 1) .omitted
          (.explicit row.position row.concrete none)) s out ∧
      out.entries = [localEntry row [.result] (s.nextEffect + 1)] ∧
      out.state = {s with nextEffect := s.nextEffect + 2} := by
  have argument := SourcePair.int (c := FormalPermissionAuthenticatedNativeDecode.context) true s none helpers.argument
  have result := SourcePair.unit (c := FormalPermissionAuthenticatedNativeDecode.context) false s (some row) helpers.result
  have ae := omitted_supplier s allocation1 helpers.argumentPort
  have re := concrete_supplier {s with nextEffect := s.nextEffect + 1} row
    allocation2 nonempty noVariables helpers.resultPort
  refine ⟨_, SourcePair.function none argument result ae re ?_, ?_, ?_⟩
  · simpa [Frame, localEntry, prependPath, atPort] using helpers.terms
  · rfl
  · simp [Nat.add_assoc]

/-- The remaining exact-tree helper obligations, each at its own call cut.
Tuple fields own tuple-term construction after the ordered children. -/
structure TreeFrames (s : State) where
  first : FunctionFrames s FormalPermissionAuthenticatedNativeDecode.firstRow
  innerInt : Frame (s.nextEffect + 2) []
  second : FunctionFrames {s with nextEffect := s.nextEffect + 2} FormalPermissionAuthenticatedNativeDecode.secondRow
  innerTuple : Frame (s.nextEffect + 4)
    [localEntry FormalPermissionAuthenticatedNativeDecode.secondRow [.element 1, .result] (s.nextEffect + 3)]
  rootTuple : Frame (s.nextEffect + 4) (FormalPermissionAuthenticatedNativeDecode.retained s.nextEffect)

/-- Construct the target SourcePair from connected allocation steps and only
local helper obligations. No SourcePair or whole-pair frame is an input. -/
theorem exact_tree_supplier (s : State) (a : Allocator) (level : Nat)
    (length : a.bounds.length = s.nextEffect) (aligned : Aligned a)
    (ready : Reservations a level) (helpers : TreeFrames s) :
    ∃ out : ValueDecoded FormalPermissionAuthenticatedNativeDecode.context false s,
      SourcePair FormalPermissionAuthenticatedNativeDecode.context false FormalPermissionAuthenticatedNativeDecode.tree (FormalPermissionAuthenticatedNativeDecode.code 0 1) s out := by
  have all := four_allocations_and_prefix a level aligned
  have a1 : FreshStep s.nextEffect := by
    simpa only [length] using freshStep a level aligned ready.first
  have a2 : FreshStep (s.nextEffect + 1) := by
    simpa only [all.2.2.2.2.1, length] using
      freshStep (afterOne a level) level all.1 ready.second
  have a3 : FreshStep (s.nextEffect + 2) := by
    simpa only [all.2.2.2.2.2.1, length] using
      freshStep (afterTwo a level) level all.2.1 ready.third
  have a4 : FreshStep (s.nextEffect + 2 + 1) := by
    simpa only [all.2.2.2.2.2.2.1, length, Nat.add_assoc] using
      freshStep (afterThree a level) level all.2.2.1 ready.fourth
  obtain ⟨first, firstRun, firstEntries, firstState⟩ :=
    function_supplier s FormalPermissionAuthenticatedNativeDecode.firstRow a1 a2 (by decide) rfl helpers.first
  have innerInt := SourcePair.int (c := FormalPermissionAuthenticatedNativeDecode.context) false first.state none
    (by simpa only [Frame, firstState] using helpers.innerInt)
  have secondFrames : FunctionFrames first.state FormalPermissionAuthenticatedNativeDecode.secondRow := by
    simpa only [firstState] using helpers.second
  have step3 : FreshStep first.state.nextEffect := by
    simpa only [firstState] using a3
  have step4 : FreshStep (first.state.nextEffect + 1) := by
    simpa only [firstState] using a4
  obtain ⟨second, secondRun, secondEntries, secondState⟩ :=
    function_supplier first.state FormalPermissionAuthenticatedNativeDecode.secondRow step3 step4 (by decide) rfl secondFrames
  have innerChildren := SourceTuples.cons innerInt
    (SourceTuples.cons secondRun (SourceTuples.nil false second.state))
  have innerRun := SourcePair.tuple (c := FormalPermissionAuthenticatedNativeDecode.context) none innerChildren
    (by simp [NoElementEffects, Annotation.effects, FormalPermissionAuthenticatedNativeDecode.intLeaf]) (by simp) (by
      simpa [Frame, firstState, secondState, secondEntries, prependPath,
        shift, shiftPath, localEntry, Nat.add_assoc] using helpers.innerTuple)
  have rootChildren := SourceTuples.cons firstRun
    (SourceTuples.cons innerRun (SourceTuples.nil false _))
  -- Name the actual child output before constructing the dependent root.
  -- Reassembling its fields keeps every sequential state and event witness.
  let children : TupleDecoded FormalPermissionAuthenticatedNativeDecode.context false s :=
    (fun {xs : Annotations} {cs : TupleCode}
      {out : TupleDecoded FormalPermissionAuthenticatedNativeDecode.context false s}
      (_ : SourceTuples FormalPermissionAuthenticatedNativeDecode.context false xs cs s out) =>
        { elements := out.elements, entries := out.entries, state := out.state,
          births := out.births, events := out.events }) rootChildren
  have nonempty : children.elements ≠ [] := by simp [children]
  let root : ValueDecoded FormalPermissionAuthenticatedNativeDecode.context false s :=
    { shape := .tuple children.elements, entries := children.entries,
      state := children.state, births := children.births,
      events := .tuple children.events nonempty }
  have rootRun : SourcePair FormalPermissionAuthenticatedNativeDecode.context false
      FormalPermissionAuthenticatedNativeDecode.tree
      (FormalPermissionAuthenticatedNativeDecode.code 0 1) s root := by
    exact SourcePair.tuple (out := children)
      (some FormalPermissionAuthenticatedNativeDecode.rootRow) rootChildren
      (by simp [NoElementEffects, Annotation.effects, FormalPermissionAuthenticatedNativeDecode.firstFunction])
      nonempty (by
        simpa [children, Frame, firstState, secondState, firstEntries, secondEntries,
          prependPath, shift, shiftPath, localEntry, FormalPermissionAuthenticatedNativeDecode.retained, FormalPermissionAuthenticatedNativeDecode.firstPath,
          FormalPermissionAuthenticatedNativeDecode.secondPath, FormalPermissionAuthenticatedNativeDecode.firstRow, FormalPermissionAuthenticatedNativeDecode.secondRow, Nat.add_assoc] using helpers.rootTuple)
  exact ⟨root, rootRun⟩

/-- The SAME constructed source derivation/output is passed to accepted R9.
Allocator permissions retain the arbitrary prefix; decoded entries are its
local suffix. Concrete helper execution/authentication remains external. -/
theorem exact_tree_r9_application (s : State) (a : Allocator) (level : Nat)
    (length : a.bounds.length = s.nextEffect) (aligned : Aligned a)
    (ready : Reservations a level) (helpers : TreeFrames s) :
    ∃ out : ValueDecoded FormalPermissionAuthenticatedNativeDecode.context false s,
      SourcePair FormalPermissionAuthenticatedNativeDecode.context false FormalPermissionAuthenticatedNativeDecode.tree (FormalPermissionAuthenticatedNativeDecode.code 0 1) s out ∧
      out = FormalPermissionAuthenticatedNativeDecode.output s 0 1 ∧ out.entries = FormalPermissionAuthenticatedNativeDecode.retained s.nextEffect ∧
      out.births = [s.nextEffect, s.nextEffect + 1, s.nextEffect + 2, s.nextEffect + 3] ∧
      out.state = {s with nextEffect := s.nextEffect + 4} ∧
      Aligned (afterFour a level) ∧
      (afterFour a level).permissions = a.permissions ++ out.entries := by
  obtain ⟨out, run⟩ := exact_tree_supplier s a level length aligned ready helpers
  obtain ⟨same, entries, births, state⟩ := r5_source_allocation_instance s out run
  have all := four_allocations_and_prefix a level aligned
  refine ⟨out, run, same, entries, births, state, all.2.2.2.1, ?_⟩
  rw [entries, ← length]
  exact all.2.2.2.2.2.2.2.2

end
end YulangClosure.FormalPermissionSourceInstance
