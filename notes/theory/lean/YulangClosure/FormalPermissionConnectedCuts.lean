import YulangClosure.FormalPermissionHelperFrames

/-! R13 connected operation model. This is a construction from one arbitrary
helper state, not a Rust execution/success certificate. Local views below are
read interpretations; they never mutate the connected full permission list. -/
namespace YulangClosure.FormalPermissionConnectedCuts
open FormalPermissionSourceOrigin FormalPermissionCaptureConstruction
open FormalPermissionConstructorRealization FormalPermissionExportWitness
open FormalPermissionSiteTraversal FormalPermissionSourceAllocation
open FormalPermissionSourceInstance FormalPermissionHelperFrames
noncomputable section

/-- Structural priorPath comparison rejects a different constructor/index. -/
def stripPath : List Step → List Step → Option (List Step)
  | [], full => some full
  | _ :: _, [] => none
  | p :: ps, q :: qs => if p = q then stripPath ps qs else none

theorem strip_recompose (priorPath relative : List Step) :
    stripPath priorPath (priorPath ++ relative) = some relative := by
  induction priorPath with
  | nil => rfl
  | cons p ps ih => simpa [stripPath] using ih

theorem recompose_strip (priorPath full relative : List Step)
    (h : stripPath priorPath full = some relative) : full = priorPath ++ relative := by
  induction priorPath generalizing full with
  | nil => simpa [stripPath] using h
  | cons p ps ih =>
    cases full with
    | nil => simp [stripPath] at h
    | cons q qs =>
      by_cases same : p = q
      · subst q
        simp only [stripPath, if_pos rfl] at h
        exact congrArg (List.cons p) (ih qs h)
      · simp [stripPath, same] at h

def extendEntry (priorPath : List Step) (entry : Retained) : Retained :=
  {entry with path := priorPath ++ entry.path}

def rebaseEntry (priorPath : List Step) (entry : Retained) : Option Retained := do
  let relative ← stripPath priorPath entry.path
  pure {entry with path := relative}

theorem rebase_extend (priorPath : List Step) (entry : Retained) :
    rebaseEntry priorPath (extendEntry priorPath entry) = some entry := by
  cases entry
  simp [rebaseEntry, extendEntry, strip_recompose]

theorem extend_rebase (priorPath : List Step) (full relative : Retained)
    (h : rebaseEntry priorPath full = some relative) :
    extendEntry priorPath relative = full := by
  cases full with
  | mk metadata path ordinal =>
    cases hs : stripPath priorPath path with
    | none => simp [rebaseEntry, hs] at h
    | some relativePath =>
      have he : (⟨metadata, relativePath, ordinal⟩ : Retained) = relative := by
        simpa [rebaseEntry, hs] using h
      subst relative
      simp [extendEntry, recompose_strip priorPath path relativePath hs]

/-- All source identity fields and the allocation witness survive rebasing. -/
theorem rebase_identity (priorPath : List Step) (entry : Retained) :
    (extendEntry priorPath entry).metadata = entry.metadata ∧
    (extendEntry priorPath entry).allocatedRow = entry.allocatedRow := ⟨rfl, rfl⟩

/-- Siblings remain different even when every concrete/metadata field and the
allocation identity coincide. No distinct-concrete-data premise is used. -/
theorem sibling_distinction (priorPath tail : List Step) (i j : Nat) (different : i ≠ j)
    (metadata : Metadata) (ordinal : Nat) :
    extendEntry priorPath ⟨metadata, .element i :: tail, ordinal⟩ ≠
      extendEntry priorPath ⟨metadata, .element j :: tail, ordinal⟩ := by
  intro same
  have paths := congrArg Retained.path same
  have heads : (.element i :: tail : List Step) = .element j :: tail :=
    List.append_cancel_left paths
  cases heads
  exact different rfl

/-- Total relativePath read view. The accompanying decomposition theorems establish
its meaning on the selected cuts; drop alone is not a path-validity test. -/
def localEntryView (priorPath : List Step) (entry : Retained) : Retained :=
  {entry with path := entry.path.drop priorPath.length}

theorem local_view_exact (priorPath : List Step) (entry : Retained) :
    localEntryView priorPath (extendEntry priorPath entry) = entry := by
  cases entry
  simp [localEntryView, extendEntry]

def viewState (priorCount : Nat) (priorPath : List Step) (s : HelperState) : HelperState :=
  {s with allocator := {s.allocator with permissions :=
    (s.allocator.permissions.drop priorCount).map (localEntryView priorPath)}}

structure Calls where
  firstArgument : Call .leaf
  firstResult : Call .leaf
  firstArgumentPort : Call .portCompletion
  firstResultPort : Call .portCompletion
  firstTerms : Call .functionCompletion
  innerInt : Call .leaf
  secondArgument : Call .leaf
  secondResult : Call .leaf
  secondArgumentPort : Call .portCompletion
  secondResultPort : Call .portCompletion
  secondTerms : Call .functionCompletion
  innerTuple : Call .tupleCompletion
  rootTuple : Call .tupleCompletion
  firstPathCapacity : Nat
  firstConcreteCapacity : Nat
  firstBacking : Nat
  secondPathCapacity : Nat
  secondConcreteCapacity : Nat
  secondBacking : Nat

/-- These fields are outputs of connect, never independently supplied cut
endpoints. c1..c13 are the states immediately before their Call transcript. -/
structure Trace where
  c1 : HelperState
  c2 : HelperState
  c3 : HelperState
  c4 : HelperState
  c5 : HelperState
  c6 : HelperState
  c7 : HelperState
  c8 : HelperState
  c9 : HelperState
  c10 : HelperState
  c11 : HelperState
  c12 : HelperState
  c13 : HelperState
  final : HelperState

def enter (path : List Step) (s : HelperState) : HelperState := applyOp (.setPath path) s

def finish {kind : CallKind} (call : Call kind) (s : HelperState) : HelperState :=
  runOps call.ops s

/-- One effect birth appends one row to EACH of four allocator vectors. -/
def birth (level : Nat) (s : HelperState) : HelperState :=
  {s with allocator := s.allocator.push level}

def prepareAppend (entry : Retained) (pc cc backing : Nat) (s : HelperState) : HelperState :=
  pushPermission (runOps (concretePreparation entry pc cc backing) s) entry

/-- One threaded construction. Both permission appends follow their allocation
and concrete preparation, and precede their port term completion. -/
def connect (calls : Calls) (initial : HelperState) (level : Nat) : Trace :=
  let n := initial.allocator.bounds.length
  let c1 := enter [.element 0, .argument] initial
  let c2 := enter FormalPermissionAuthenticatedNativeDecode.firstPath (finish calls.firstArgument c1)
  let c3 := birth level (enter [.element 0, .argument] (finish calls.firstResult c2))
  let c4 := prepareAppend (firstEntry n) calls.firstPathCapacity calls.firstConcreteCapacity calls.firstBacking
    (birth level (enter FormalPermissionAuthenticatedNativeDecode.firstPath (finish calls.firstArgumentPort c3)))
  let c5 := enter [.element 0] (finish calls.firstResultPort c4)
  let c6 := enter [.element 1, .element 0] (finish calls.firstTerms c5)
  let c7 := enter [.element 1, .element 1, .argument] (finish calls.innerInt c6)
  let c8 := enter FormalPermissionAuthenticatedNativeDecode.secondPath (finish calls.secondArgument c7)
  let c9 := birth level (enter [.element 1, .element 1, .argument] (finish calls.secondResult c8))
  let c10 := prepareAppend (secondEntry n) calls.secondPathCapacity calls.secondConcreteCapacity calls.secondBacking
    (birth level (enter FormalPermissionAuthenticatedNativeDecode.secondPath (finish calls.secondArgumentPort c9)))
  let c11 := enter [.element 1, .element 1] (finish calls.secondResultPort c10)
  let c12 := enter [.element 1] (finish calls.secondTerms c11)
  let c13 := enter [] (finish calls.innerTuple c12)
  ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, finish calls.rootTuple c13⟩

private theorem enter_allocator (path : List Step) (s : HelperState) :
    (enter path s).allocator = s.allocator := rfl
private theorem finish_allocator {kind : CallKind} (call : Call kind) (s : HelperState) :
    (finish call s).allocator = s.allocator := operations_preserve_allocator _ _
private theorem prepare_allocator (entry : Retained) (pc cc backing : Nat) (s : HelperState) :
    (prepareAppend entry pc cc backing s).allocator = appendPermission s.allocator entry := by
  simp only [prepareAppend, pushPermission, operations_preserve_allocator, appendPermission]

/-- All thirteen allocator observations derive from the same chain. -/
theorem connected_allocators (calls : Calls) (initial : HelperState) (level : Nat) :
    let t := connect calls initial level
    let a := initial.allocator
    t.c1.allocator = a ∧ t.c2.allocator = a ∧
    t.c3.allocator = afterOne a level ∧ t.c4.allocator = afterTwo a level ∧
    t.c5.allocator = afterTwo a level ∧ t.c6.allocator = afterTwo a level ∧
    t.c7.allocator = afterTwo a level ∧ t.c8.allocator = afterTwo a level ∧
    t.c9.allocator = afterThree a level ∧ t.c10.allocator = afterFour a level ∧
    t.c11.allocator = afterFour a level ∧ t.c12.allocator = afterFour a level ∧
    t.c13.allocator = afterFour a level ∧ t.final.allocator = afterFour a level := by
  simp only [connect, finish_allocator, enter_allocator, prepare_allocator, birth,
    afterOne, afterTwo, afterThree, afterFour] <;> simp

/-- The two full records factor at every nonempty R12 relativePath root. -/
theorem exact_path_factors (n : Nat) :
    firstEntry n = extendEntry FormalPermissionAuthenticatedNativeDecode.firstPath (localEntry FormalPermissionAuthenticatedNativeDecode.firstRow [] (n + 1)) ∧
    firstEntry n = extendEntry [.element 0] (localEntry FormalPermissionAuthenticatedNativeDecode.firstRow [.result] (n + 1)) ∧
    secondEntry n = extendEntry FormalPermissionAuthenticatedNativeDecode.secondPath (localEntry FormalPermissionAuthenticatedNativeDecode.secondRow [] (n + 3)) ∧
    secondEntry n = extendEntry [.element 1, .element 1] (localEntry FormalPermissionAuthenticatedNativeDecode.secondRow [.result] (n + 3)) ∧
    secondEntry n = extendEntry [.element 1] (localEntry FormalPermissionAuthenticatedNativeDecode.secondRow [.element 1, .result] (n + 3)) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

private def cut {kind : CallKind} (call : Call kind) (s : HelperState)
    (priorCount : Nat) (priorPath : List Step) (n : Nat) (entries : List Retained)
    (rows : s.allocator.bounds.length = n)
    (permissions : (s.allocator.permissions.drop priorCount).map (localEntryView priorPath) = entries) :
    Cut kind n entries :=
  ⟨viewState priorCount priorPath s, [], rows, by simpa [viewState] using permissions, call⟩

/-- Every R12 initial state is a deterministic view of a cut of connect. No
Cut.initial, endpoint equality, or TreeFrames is accepted as input. -/
def treeOperations (s : State) (initial : HelperState) (level : Nat)
    (length : initial.allocator.bounds.length = s.nextEffect) (calls : Calls) : TreeOperations s := by
  let t := connect calls initial level
  let k := initial.allocator.permissions.length
  have h := connected_allocators calls initial level
  dsimp only at h
  rcases h with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,hfinal⟩
  refine ⟨⟨cut calls.firstArgument t.c1 k [.element 0, .argument] _ _ ?_ ?_,
    cut calls.firstResult t.c2 k FormalPermissionAuthenticatedNativeDecode.firstPath _ _ ?_ ?_,
    cut calls.firstArgumentPort t.c3 k [.element 0, .argument] _ _ ?_ ?_,
    cut calls.firstResultPort t.c4 k FormalPermissionAuthenticatedNativeDecode.firstPath _ _ ?_ ?_,
    cut calls.firstTerms t.c5 k [.element 0] _ _ ?_ ?_⟩,
    cut calls.innerInt t.c6 (k + 1) [.element 1, .element 0] _ _ ?_ ?_,
    ⟨cut calls.secondArgument t.c7 (k + 1) [.element 1, .element 1, .argument] _ _ ?_ ?_,
    cut calls.secondResult t.c8 (k + 1) FormalPermissionAuthenticatedNativeDecode.secondPath _ _ ?_ ?_,
    cut calls.secondArgumentPort t.c9 (k + 1) [.element 1, .element 1, .argument] _ _ ?_ ?_,
    cut calls.secondResultPort t.c10 (k + 1) FormalPermissionAuthenticatedNativeDecode.secondPath _ _ ?_ ?_,
    cut calls.secondTerms t.c11 (k + 1) [.element 1, .element 1] _ _ ?_ ?_⟩,
    cut calls.innerTuple t.c12 (k + 1) [.element 1] _ _ ?_ ?_,
    cut calls.rootTuple t.c13 k [] _ _ ?_ ?_⟩ <;>
    simp [t, k, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
      afterOne, afterTwo, afterThree, afterFour, appendPermission, Allocator.push,
      firstEntry, secondEntry, localEntryView, localEntry, FormalPermissionAuthenticatedNativeDecode.firstPath,
      FormalPermissionAuthenticatedNativeDecode.secondPath, FormalPermissionAuthenticatedNativeDecode.firstRow, FormalPermissionAuthenticatedNativeDecode.secondRow, FormalPermissionAuthenticatedNativeDecode.retained,
      List.drop_left, List.drop_length_add_append, List.append_assoc, length, Nat.add_assoc]

/-- The SAME R12/R11 output and derivation, applied to the connected model.
Reservations remain explicit successful-path inputs, not availability claims. -/
theorem exact_tree_r9_from_connected (s : State) (initial : HelperState) (level : Nat)
    (length : initial.allocator.bounds.length = s.nextEffect)
    (aligned : Aligned initial.allocator) (ready : Reservations initial.allocator level)
    (calls : Calls) :
    ∃ out : ValueDecoded FormalPermissionAuthenticatedNativeDecode.context false s,
      SourcePair FormalPermissionAuthenticatedNativeDecode.context false FormalPermissionAuthenticatedNativeDecode.tree (FormalPermissionAuthenticatedNativeDecode.code 0 1) s out ∧
      out = FormalPermissionAuthenticatedNativeDecode.output s 0 1 ∧ out.entries = FormalPermissionAuthenticatedNativeDecode.retained s.nextEffect ∧
      out.births = [s.nextEffect, s.nextEffect + 1, s.nextEffect + 2, s.nextEffect + 3] ∧
      out.state = {s with nextEffect := s.nextEffect + 4} ∧
      Aligned (afterFour initial.allocator level) ∧
      (afterFour initial.allocator level).permissions = initial.allocator.permissions ++ out.entries :=
  exact_tree_r9_from_operations s initial.allocator level length aligned ready
    (treeOperations s initial level length calls)

end
end YulangClosure.FormalPermissionConnectedCuts
