import Yulang.GeneralSourceRoleCstVisibleRange294

/-! Keep portable receipts and the conservative plain-token receipt distinct.
The stronger gate still needs a genuine complete diagnostic input. -/
namespace Yulang.GeneralSourceRoleCstVisibleReceipt294
open GeneralSourceRoleCstTree293 (Path)
open GeneralSourceRoleCstWire293 (Wire)
open GeneralSourceRoleCstVisibleRange294 (checkVisible)
open GeneralSourceRoleCstMixedReceipt294 (Evidence Receipt exportChecked)
open GeneralSourceRoleCstMarkPolicy294 (Policy)
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceRoleTrack292 (Tracked)

def plainTokenEvidence (w : Wire) (path : Path) : Evidence → Bool
  | .errorGroupRange range => checkVisible w range path
  | .otherDiagnostic _ => true

def plainTokenPacket {Brand : Type} (w : Wire) (p : Path) : Receipt Brand → Bool
  | .reported _ events => events.all (plainTokenEvidence w p)
  | _ => false

def project {Scope Brand : Type} [DecidableEq Brand] (policy : Policy) (scope : Scope)
    (w : Wire) (brand : Brand) (a : Address Brand) (packet : Receipt Brand) :
    Option (Tracked Scope (Address Brand)) :=
  if plainTokenPacket w a.path packet then exportChecked policy scope w brand a packet else none

theorem project_exact {Scope Brand : Type} [DecidableEq Brand] (policy : Policy)
    (scope : Scope) (w : Wire) (brand : Brand) (a : Address Brand) (packet : Receipt Brand)
    (out : Tracked Scope (Address Brand)) :
    project policy scope w brand a packet = some out ↔
    exportChecked policy scope w brand a packet = some out ∧
      ∃ sender events, packet = .reported sender events ∧ ∀ range,
        .errorGroupRange range ∈ events → checkVisible w range a.path = true := by
  have handoff : plainTokenPacket w a.path packet = true ↔
      ∃ sender events, packet = .reported sender events ∧ ∀ range,
        .errorGroupRange range ∈ events → checkVisible w range a.path = true := by
    cases packet with
    | absent => simp [plainTokenPacket]
    | failed => simp [plainTokenPacket]
    | reported sender events =>
      simp only [plainTokenPacket,List.all_eq_true,Receipt.reported.injEq]
      constructor
      · intro all
        exact ⟨sender,events,⟨rfl,rfl⟩,fun r found => all _ found⟩
      · rintro ⟨_,_,⟨rfl,rfl⟩,h⟩ e found
        cases e with
        | errorGroupRange r => exact h r found
        | otherDiagnostic _ => rfl
  rw [← handoff]
  by_cases h : plainTokenPacket w a.path packet = true <;> simp [project,h]

end Yulang.GeneralSourceRoleCstVisibleReceipt294
