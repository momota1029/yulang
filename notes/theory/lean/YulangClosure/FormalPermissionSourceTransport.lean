import YulangClosure.FormalPermissionExportWitnessNative

/-! Conditional source-transport obligations. The forest update matches the
copy-representative -> parent-representative write in candidate_intrusion.rs.
The source-tree interface below is parameterized: extraction from actual HIR,
its child recurrence, positions and occurrence identities remain OPEN. Neither
interface proves an ordinary source demand, qualification or native capture. -/
namespace YulangClosure.FormalPermissionSourceTransport
open FormalPermissionSourceOrigin FormalPermissionCaptureConstruction

def writeParent (forest : Nat → Nat) (copy parent : Nat) : Nat → Nat :=
  fun row => if row = copy then parent else forest row

def walk (forest : Nat → Nat) : Nat → Nat → Nat
  | 0, row => row
  | n + 1, row => forest (walk forest n row)

theorem copy_write (forest : Nat → Nat) (copy parent : Nat) :
    writeParent forest copy parent copy = parent := by simp [writeParent]

/-- A finite old chain avoiding the copy slot is unchanged by that write. -/
theorem walk_frame (forest : Nat → Nat) (copy parent row bound : Nat)
    (avoids : ∀ k, k < bound → walk forest k row ≠ copy) :
    walk (writeParent forest copy parent) bound row = walk forest bound row := by
  induction bound with
  | zero => rfl
  | succ n ih =>
      have earlier : ∀ k, k < n → walk forest k row ≠ copy :=
        fun k hk => avoids k (Nat.lt_trans hk (Nat.lt_succ_self n))
      simp only [walk, ih earlier, writeParent]
      exact if_neg (avoids n (Nat.lt_succ_self n))

/-- Necessary direction condition for a changed bounded representative read.
Native extraction must establish a common bound and the actual forest write. -/
theorem changed_walk_hits_copy (forest : Nat → Nat) (copy parent row bound : Nat)
    (changed : walk (writeParent forest copy parent) bound row ≠ walk forest bound row) :
    ∃ k, k < bound ∧ walk forest k row = copy := by
  classical
  by_contra absent
  have avoids : ∀ k, k < bound → walk forest k row ≠ copy := by
    intro k hk eq
    exact absent ⟨k, hk, eq⟩
  exact changed (walk_frame forest copy parent row bound avoids)

theorem parent_stays_root (forest : Nat → Nat) (copy parent bound : Nat)
    (distinct : parent ≠ copy) (root : forest parent = parent) :
    walk (writeParent forest copy parent) bound parent = parent := by
  induction bound with
  | zero => rfl
  | succ n ih => simp only [walk, ih, writeParent, if_neg distinct, root]

/-- Copy-side transport is sufficient once the parent is a distinct root.
An extrusion with allocated r on the PARENT side does not satisfy this claim. -/
theorem copy_reaches_parent (forest : Nat → Nat) (copy parent bound : Nat)
    (distinct : parent ≠ copy) (root : forest parent = parent) :
    walk (writeParent forest copy parent) (bound + 1) copy = parent := by
  induction bound with
  | zero => simp [walk, writeParent]
  | succ n ih => simp only [walk, ih, writeParent, if_neg distinct, root]

/-- Application to an allocated row r and independently read captured q. No
numeric r/q is chosen; old/new finite-read equations remain extraction premises. -/
theorem unequal_capture_requires_copy_hit (forest : Nat → Nat)
    (copy parent allocated captured bound : Nat)
    (oldRead : walk forest bound allocated = allocated)
    (newRead : walk (writeParent forest copy parent) bound allocated = captured)
    (unequal : captured ≠ allocated) :
    ∃ k, k < bound ∧ walk forest k allocated = copy := by
  apply changed_walk_hits_copy forest copy parent allocated bound
  rw [oldRead, newRead]
  exact unequal

/-- Generic navigation over an extracted ACTUAL source tree. `child` must
implement the Function argument/result and Tuple element recurrence. -/
def descend {Tree : Type} (child : Tree → Step → Option Tree) :
    Tree → List Step → Option Tree
  | node, [] => some node
  | node, step :: rest => (child node step).bind (fun next => descend child next rest)

def locate {Tree : Type} (child : Tree → Step → Option Tree)
    (effectPosition : Tree → Option Nat) (root : Tree) (path : List Step) : Option Nat :=
  (descend child root path).bind effectPosition

structure SiteKey where
  context : Context
  enclosingAnnotation : Nat
  path : List Step
  nestedEffectRow : Nat
  deriving DecidableEq, Repr

/-- Keeps both coordinates. Native events must preserve this same key across
the delegated tail and BOTH polarity-specific port allocations. -/
def Associated {Tree : Type} (child : Tree → Step → Option Tree)
    (effectPosition : Tree → Option Nat) (root : Tree) (context : Context)
    (annotationPosition : Nat) (site : SiteKey) : Prop :=
  site.context = context ∧ site.enclosingAnnotation = annotationPosition ∧
    locate child effectPosition root site.path = some site.nestedEffectRow

theorem site_row_unique {Tree : Type} (child : Tree → Step → Option Tree)
    (effectPosition : Tree → Option Nat) (root : Tree) (context : Context)
    (annotationPosition : Nat) (first second : SiteKey)
    (a : Associated child effectPosition root context annotationPosition first)
    (b : Associated child effectPosition root context annotationPosition second)
    (samePath : first.path = second.path) :
    first.nestedEffectRow = second.nestedEffectRow := by
  have one := a.2.2
  rw [samePath, b.2.2] at one
  exact (Option.some.inj one).symm

/-- Different source paths never collapse merely because enclosing positions
agree. This does not assume that different paths have distinct row positions. -/
theorem different_paths_distinct (first second : SiteKey)
    (different : first.path ≠ second.path) : first ≠ second := by
  intro same
  exact different (congrArg SiteKey.path same)

theorem associated_coordinates {Tree : Type} (child : Tree → Step → Option Tree)
    (effectPosition : Tree → Option Nat) (root : Tree) (context : Context)
    (annotationPosition : Nat) (site : SiteKey)
    (a : Associated child effectPosition root context annotationPosition site) :
    site.context = context ∧ site.enclosingAnnotation = annotationPosition ∧
      locate child effectPosition root site.path = some site.nestedEffectRow := a

/-- Association is compatible with unequal positions: equality of numeric
coordinates cannot replace tree/path extraction. -/
theorem associated_with_distinct_positions {Tree : Type}
    (child : Tree → Step → Option Tree) (effectPosition : Tree → Option Nat)
    (root : Tree) (context : Context) (annotationPosition nestedPosition : Nat)
    (path : List Step) (found : locate child effectPosition root path = some nestedPosition)
    (distinct : annotationPosition ≠ nestedPosition) :
    Associated child effectPosition root context annotationPosition
      ⟨context, annotationPosition, path, nestedPosition⟩ ∧
      annotationPosition ≠ nestedPosition := ⟨⟨rfl, rfl, found⟩, distinct⟩

end YulangClosure.FormalPermissionSourceTransport
