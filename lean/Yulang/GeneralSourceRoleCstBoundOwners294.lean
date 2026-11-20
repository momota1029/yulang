import Yulang.GeneralSourceRoleCstGroupAnchor294

/-! Validate that a separately attached owner path denotes a real mixed CST
child before using it to admit a diagnostic outside the selected corridor.
Path existence does not authenticate the attachment. -/
namespace Yulang.GeneralSourceRoleCstBoundOwners294
open GeneralSourceRoleCstTree293 (Path Tree)
open GeneralSourceRoleCstPath293 (follow)
open GeneralSourceRoleCstDiagnostics294 (Diagnostic Scan permitted IndependentPermission)
open GeneralSourceRoleCstMarkPolicy294 (Policy allows guarded)
open GeneralSourceRoleCstSnapshot293 (Snapshot Address)
open GeneralSourceRoleCstRustSnapshot293 (exportAt)
open GeneralSourceRoleTrack292 (Tracked)

def ownerExists (root : Tree) (d : Diagnostic) : Bool :=
  match d.owner with
  | none => false
  | some p => (follow p root).isSome

def grounded (policy : Policy) (root : Tree) (selected : Path) (d : Diagnostic) : Bool :=
  permitted policy selected d && ownerExists root d

theorem owner_exists_exact (root : Tree) (d : Diagnostic) : ownerExists root d = true ↔
    ∃ p node, d.owner = some p ∧ follow p root = some node := by
  cases h : d.owner with
  | none => simp [ownerExists,h]
  | some p =>
    cases f : follow p root <;> simp [ownerExists,h,f]

theorem grounded_exact (policy : Policy) (root : Tree) (selected : Path) (d : Diagnostic) :
    grounded policy root selected d = true ↔ IndependentPermission policy selected d ∧
    ∃ p node, d.owner = some p ∧ follow p root = some node := by
  simp [grounded,GeneralSourceRoleCstDiagnostics294.permitted_exact,owner_exists_exact]

def packetOK {Brand : Type} [DecidableEq Brand] (policy : Policy) (s : Snapshot Brand)
    (selected : Path) : Scan Brand → Bool
  | .reported brand items => decide (brand = s.brand) && items.all (grounded policy s.root selected)
  | _ => false

theorem packet_exact {Brand : Type} [DecidableEq Brand] (policy : Policy)
    (s : Snapshot Brand) (selected : Path) (scan : Scan Brand) :
    packetOK policy s selected scan = true ↔
      ∃ ds, scan = .reported s.brand ds ∧ ∀ d ∈ ds,
        IndependentPermission policy selected d ∧
        ∃ p node, d.owner = some p ∧ follow p s.root = some node := by
  cases scan with
  | absent => simp [packetOK]
  | failed => simp [packetOK]
  | reported sender ds =>
    simp only [packetOK,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,grounded_exact,
      Scan.reported.injEq]
    constructor
    · rintro ⟨rfl,h⟩; exact ⟨ds,⟨rfl,rfl⟩,h⟩
    · rintro ⟨_,⟨rfl,rfl⟩,h⟩; exact ⟨rfl,h⟩

def checkedBound {Scope Brand : Type} [DecidableEq Brand] (policy : Policy) (scope : Scope)
    (s : Snapshot Brand) (a : Address Brand) (scan : Scan Brand) :
    Option (Tracked Scope (Address Brand)) :=
  if packetOK policy s a.path scan then guarded policy scope s a else none

theorem checked_bound_exact {Scope Brand : Type} [DecidableEq Brand] (policy : Policy)
    (scope : Scope) (s : Snapshot Brand) (a : Address Brand) (scan : Scan Brand)
    (out : Tracked Scope (Address Brand)) :
    checkedBound policy scope s a scan = some out ↔
      packetOK policy s a.path scan = true ∧ allows policy s.root a.path = true ∧
      exportAt scope s a = some out := by
  by_cases h : packetOK policy s a.path scan = true
  · simp [checkedBound,h,GeneralSourceRoleCstMarkPolicy294.guarded_exact]
  · simp [checkedBound,h]

theorem implies_independent_packet {Brand : Type} [DecidableEq Brand] (policy : Policy)
    (s : Snapshot Brand) (wanted : Path) (scan : Scan Brand)
    (ok : packetOK policy s wanted scan = true) :
    GeneralSourceRoleCstDiagnostics294.permits policy s.brand wanted scan = true := by
  obtain ⟨items,reported,ok⟩ := (packet_exact ..).mp ok
  exact (GeneralSourceRoleCstDiagnostics294.permits_exact ..).mpr
    ⟨items,reported,fun d h => (ok d h).1⟩

end Yulang.GeneralSourceRoleCstBoundOwners294
