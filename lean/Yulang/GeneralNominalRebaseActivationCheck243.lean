import Yulang.GeneralNominalRebaseActivation243
/-! Finite no-read checking for inactive-cell activation. The check includes
nominal raw reads and every supplied live endpoint and actual center. -/
namespace Yulang.GeneralNominalRebaseActivationCheck243
open GeneralNominalFiniteEquationRealization236 (Entry)
open GeneralNominalRebaseActivation243
open GeneralNominalCenters (Site)
variable {roles : Roles.RoleDecls}

def check (entries : List Entry) (raw : GeneralNominalState.State)
 (atoms : List (PresenceNormalForm.Atom Nat)) (sites : List (Site roles)) : Bool :=
 entries.all (fun entry => !(reads raw atoms sites).contains entry.1)

theorem check_iff (entries : List Entry) (raw : GeneralNominalState.State)
 (atoms : List (PresenceNormalForm.Atom Nat)) (sites : List (Site roles)) :
 check entries raw atoms sites = true ↔ Checked entries raw atoms sites := by
 simp [check,Checked]

theorem reservations_invariant (entries : List Entry) (raw : GeneralNominalState.State)
 (atoms : List (PresenceNormalForm.Atom Nat)) (sites : List (Site roles)) (reserved : List Nat) :
 check entries {raw with reserved := reserved} atoms sites = check entries raw atoms sites := rfl

theorem allocations_invariant (entries : List Entry) (raw : GeneralNominalState.State)
 (atoms : List (PresenceNormalForm.Atom Nat)) (sites : List (Site roles))
 (allocated : List GeneralNominalIdentities.Origin) :
 check entries {raw with allocated := allocated} atoms sites = check entries raw atoms sites := rfl

theorem entry_rejected (entry : Entry) (present : entry ∈ entries)
 (read : entry.1 ∈ reads raw atoms sites) : check entries raw atoms sites = false := by
 cases equal : check entries raw atoms sites
 · rfl
 · exact False.elim (((check_iff entries raw atoms sites).mp equal) entry present read)
end Yulang.GeneralNominalRebaseActivationCheck243
