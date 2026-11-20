import Yulang.GeneralSourceRoleCstRangeReceipt294

/-! A narrow adapter for independently provided structural recovery ranges and
explicitly attached other diagnostic owners. A supplied list is not evidence
of its own completeness. This does not interpret Rust diagnostic IDs. -/
namespace Yulang.GeneralSourceRoleCstMixedReceipt294
open GeneralSourceRoleCstTree293 (Path Tree)
open GeneralSourceRoleCstWire293 (Wire decode Transfer decode_exact)
open GeneralSourceRoleCstSpan293 (Extent)
open GeneralSourceRoleCstRangeReceipt294 (check_exact)
open GeneralSourceRoleCstGroupAnchor294 (unique outside)
open GeneralSourceRoleCstMarkPolicy294 (Policy guarded allows guarded_exact)
open GeneralSourceRoleCstDiagnostics294 (Diagnostic IndependentPermission)
open GeneralSourceRoleCstBoundOwners294 (grounded grounded_exact)
open GeneralSourceRoleCstSnapshot293 (Snapshot Address)
open GeneralSourceRoleCstRustSnapshot293 (exportAt)
open GeneralSourceRoleTrack292 (Tracked)

inductive Evidence where
  | errorGroupRange (range : Extent)
  | otherDiagnostic (source : Diagnostic)

inductive Receipt (Brand : Type) where
  | absent
  | failed
  | reported (brand : Brand) (events : List Evidence)

def acceptable (policy : Policy) (wire : Wire) (root : Tree) (focus : Path) : Evidence → Bool
  | .errorGroupRange range =>
    (match policy with
      | .whole => false
      | .selectedBranch => ((unique wire root range).map (outside focus)).getD false)
  | .otherDiagnostic d => grounded policy root focus d

def Evidence.Scoped (policy : Policy) (wire : Wire) (root : Tree) (p : Path) :
    Evidence → Prop
  | .errorGroupRange range =>
    policy = .selectedBranch ∧ ∃ row, unique wire root range = some row ∧
      ∀ item ∈ row, ¬ p <+: item.occurrence.path ∧ ¬ item.occurrence.path <+: p
  | .otherDiagnostic d =>
    IndependentPermission policy p d ∧ ∃ atPath node,
      d.owner = some atPath ∧ GeneralSourceRoleCstPath293.follow atPath root = some node

theorem acceptable_exact (policy : Policy) (wire : Wire) (root : Tree) (focus : Path)
    (e : Evidence) : acceptable policy wire root focus e = true ↔ e.Scoped policy wire root focus := by
  cases e with
  | otherDiagnostic d => simpa only [acceptable,Evidence.Scoped] using grounded_exact policy root focus d
  | errorGroupRange range =>
    cases policy with
    | whole => simp [acceptable,Evidence.Scoped]
    | selectedBranch =>
      cases h : unique wire root range <;>
        simp [acceptable,Evidence.Scoped,h,GeneralSourceRoleCstGroupAnchor294.outside_exact]

def valid {Brand : Type} [DecidableEq Brand] (policy : Policy) (wire : Wire) (s : Snapshot Brand)
    (focus : Path) : Receipt Brand → Bool
  | .reported brand events =>
    decide (s.brand = brand) && events.all (acceptable policy wire s.root focus)
  | _ => false

theorem valid_exact {Brand : Type} [DecidableEq Brand] (policy : Policy) (wire : Wire)
    (s : Snapshot Brand) (focus : Path) (r : Receipt Brand) : valid policy wire s focus r = true ↔
      ∃ events, r = .reported s.brand events ∧ ∀ e ∈ events, e.Scoped policy wire s.root focus := by
  cases r with
  | absent => simp [valid]
  | failed => simp [valid]
  | reported brand events =>
    simp only [valid,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,acceptable_exact,
      Receipt.reported.injEq]
    constructor
    · rintro ⟨rfl,each⟩; exact ⟨events,⟨rfl,rfl⟩,each⟩
    · rintro ⟨_,⟨rfl,rfl⟩,each⟩; exact ⟨rfl,each⟩

theorem whole_valid_exact {Brand : Type} [DecidableEq Brand] (wire : Wire)
    (s : Snapshot Brand) (p : Path) (r : Receipt Brand) :
    valid .whole wire s p r = true ↔ r = .reported s.brand [] := by
  rw [valid_exact]
  constructor
  · rintro ⟨events,reported,each⟩
    cases events with
    | nil => exact reported
    | cons e es =>
      have proper := each e List.mem_cons_self
      cases e with
      | errorGroupRange _ => cases proper.1
      | otherDiagnostic _ => cases proper.1.1
  · rintro rfl; exact ⟨[],rfl,by simp⟩

def exportChecked {Scope Brand : Type} [DecidableEq Brand] (policy : Policy) (scope : Scope)
    (wire : Wire) (brand : Brand) (a : Address Brand) (r : Receipt Brand) :
    Option (Tracked Scope (Address Brand)) :=
  (decode wire).bind fun root =>
    let s : Snapshot Brand := ⟨brand,root⟩
    if valid policy wire s a.path r then guarded policy scope s a else none

theorem export_exact {Scope Brand : Type} [DecidableEq Brand] (policy : Policy) (scope : Scope)
    (wire : Wire) (brand : Brand) (a : Address Brand) (r : Receipt Brand)
    (out : Tracked Scope (Address Brand)) : exportChecked policy scope wire brand a r = some out ↔
      ∃ root events, Transfer wire root ∧ r = .reported brand events ∧
        (∀ e ∈ events, e.Scoped policy wire root a.path) ∧
        allows policy root a.path = true ∧ exportAt scope ⟨brand,root⟩ a = some out := by
  constructor
  · intro ok
    cases h : decode wire with
    | none => simp [exportChecked,h] at ok
    | some root =>
      let s : Snapshot Brand := ⟨brand,root⟩
      by_cases hv : valid policy wire s a.path r = true
      · obtain ⟨ev,report,each⟩ := (valid_exact ..).mp hv
        have g : guarded policy scope s a = some out := by simpa [exportChecked,h,hv,s] using ok
        have w := (guarded_exact ..).mp g
        exact ⟨root,ev,(decode_exact ..).mp h,report,each,w.1,w.2⟩
      · simp [exportChecked,h,hv,s] at ok
  · rintro ⟨root,ev,matchTree,report,each,clean,found⟩
    have hx : valid policy wire ⟨brand,root⟩ a.path r = true :=
      (valid_exact ..).mpr ⟨ev,report,each⟩
    have gx : guarded policy scope ⟨brand,root⟩ a = some out :=
      (guarded_exact ..).mpr ⟨clean,found⟩
    simp [exportChecked,(decode_exact ..).mpr matchTree,hx,gx]

end Yulang.GeneralSourceRoleCstMixedReceipt294
