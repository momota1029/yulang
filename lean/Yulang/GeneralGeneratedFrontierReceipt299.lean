import Yulang.GeneralGeneratedDictionaryScope299

namespace Yulang.GeneralGeneratedFrontierReceipt299
open CommonRoleOutermostResolver (Frontier)
open GeneralGeneratedDictionaryRun299 (Entry Read)
open GeneralGeneratedDictionaryScope299 (Faithful)
open B4Target (Vocabulary)
open B4TargetV8

inductive Receipt where
  | absent
  | pending
  | rejected
  | ambiguous
  | unindexed
  | selected (row : Entry)

def indices (encode : α → Option Nat) : List α → Option (List Nat)
  | [] => some []
  | c::cs => do
    let i ← encode c
    let rest ← indices encode cs
    return i::rest

def compile (lookup : Nat → Option (Frontier α)) (encode : α → Option Nat) (x : Nat) : Receipt :=
  match lookup x with
  | none => .absent
  | some .pending => .pending
  | some .rejected => .rejected
  | some .ambiguous => .ambiguous
  | some (.selected k children) =>
    match indices encode children with
    | none => .unindexed
    | some keys => .selected ⟨k,keys⟩

def readRows (lookup : Nat → Option (Frontier α)) (encode : α → Option Nat) : Read := fun x =>
  match compile lookup encode x with
  | .selected row => some row
  | _ => none

def translate (denote : α → β) : Frontier α → Frontier β
  | .pending => .pending
  | .rejected => .rejected
  | .ambiguous => .ambiguous
  | .selected k children => .selected k (children.map denote)

theorem indices_exact (encode : α → Option Nat) (decode : Nat → β) (denote : α → β)
    (roundtrip : ∀ x i, encode x = some i → decode i = denote x)
    (children : List α) (row : List Nat) (hit : indices encode children = some row) :
    row.map decode = children.map denote := by
  induction children generalizing row with
  | nil => cases Option.some.inj hit; rfl
  | cons child rest ih =>
    cases first : encode child with
    | none => simp [indices,first] at hit
    | some i =>
      cases tail : indices encode rest with
      | none => simp [indices,first,tail] at hit
      | some is =>
        have eq : i::is = row := by simpa [indices,first,tail] using hit
        subst row
        simp only [List.map_cons,roundtrip _ _ first,ih _ tail]

theorem row_exact (lookup : Nat → Option (Frontier α)) (encode : α → Option Nat)
    (x : Nat) (row : Entry) (ok : readRows lookup encode x = some row) :
    ∃ children, lookup x = some (.selected row.key children) ∧
      indices encode children = some row.children := by
  cases ret : lookup x with
  | none => simp [readRows,compile,ret] at ok
  | some receipt =>
    cases receipt with
    | pending => simp [readRows,compile,ret] at ok
    | rejected => simp [readRows,compile,ret] at ok
    | ambiguous => simp [readRows,compile,ret] at ok
    | selected key children =>
      cases ids : indices encode children with
      | none => simp [readRows,compile,ret,ids] at ok
      | some chosen =>
        have eq : (⟨key,chosen⟩ : Entry) = row := by simpa [readRows,compile,ret,ids] using ok
        subst row
        exact ⟨children,rfl,ids⟩

theorem faithful {v : Vocabulary} {b : SourceBoundary v} {r : v.Registry} {s : v.State}
    (lookup : Nat → Option (Frontier α)) (encode : α → Option Nat)
    (decode : Nat → v.Demand) (denote : α → v.Demand)
    (observed : ∀ i f, lookup i = some f → Local b r s (decode i) (translate denote f))
    (roundtrip : ∀ x i, encode x = some i → decode i = denote x) :
    Faithful (b:=b) (r:=r) (s:=s) (readRows lookup encode) decode := by
  intro i row hit
  obtain ⟨children,old,ids⟩ := row_exact lookup encode i row hit
  have proof := observed i (.selected row.key children) old
  change Local b r s (decode i) (.selected row.key (children.map denote)) at proof
  rw [indices_exact encode decode denote roundtrip children row.children ids]
  exact proof

theorem unindexed_not_rejected (lookup : Nat → Option (Frontier α)) (encode : α → Option Nat)
    (x k : Nat) (children : List α) (seen : lookup x = some (.selected k children))
    (bad : indices encode children = none) :
    compile lookup encode x = .unindexed ∧ readRows lookup encode x = none := by
  simp [compile,readRows,seen,bad]

end Yulang.GeneralGeneratedFrontierReceipt299
