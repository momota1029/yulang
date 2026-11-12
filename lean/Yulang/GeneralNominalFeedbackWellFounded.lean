import Yulang.GeneralNominalFeedbackBoundary

/-! Installation descent may use any well-founded order. Administrative
updates may preserve the rank or decrease it; their already proved finite
support argument handles equal-rank updates. No installation rank is assumed
by source formation. -/
namespace Yulang.GeneralNominalFeedbackWellFounded

open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalFeedbackSteps GeneralNominalFeedbackDescent

universe u

variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

structure InstallationOrder (registry : Registry) (root : Occurrence roles) where
  Measure : Type u
  before : Measure → Measure → Prop
  wellFounded : WellFounded before
  rank : State roles → Measure
  administrative : ∀ first last, SourceFormed registry root first →
    GeneralNominalFeedbackAdministrative.Update registry first last →
      rank last = rank first ∨ before (rank last) (rank first)
  installation : ∀ state, SourceFormed registry root state → ∀ packet : Packet roles,
    Installable registry state packet → ¬ Committed state packet →
      before (rank (GeneralNominalFeedbackSites.install state packet
        (GeneralNominalFeedbackSites.emitted packet))) (rank state)

theorem accessible (order : InstallationOrder registry root)
    (state : State roles) (formed : SourceFormed registry root state) :
    Acc (fun next current => Step registry root current next) state := by
  have all : ∀ measure, ∀ current, order.rank current = measure →
      SourceFormed registry root current →
      Acc (fun next current => Step registry root current next) current := by
    intro measure
    induction order.wellFounded.apply measure with
    | intro measure below lower =>
      intro current
      induction GeneralNominalFeedbackAdministrative.accessible registry current with
      | intro current predecessors admin =>
        intro equal formed
        refine Acc.intro current ?_
        intro next step
        have nextFormed := SourceFormed.update formed step
        rcases formed_step_cases formed step with update | ⟨packet,enabled,novel,rfl⟩
        · rcases order.administrative current next formed update with same | smaller
          · exact admin next update (same.trans equal) nextFormed
          · exact lower _ (equal ▸ smaller) next rfl nextFormed
        · exact lower _ (equal ▸ order.installation current formed packet enabled novel) _ rfl nextFormed
  exact all (order.rank state) state rfl formed

def ofNat (descent : InstallationDescent registry root) : InstallationOrder registry root where
  Measure := Nat
  before := (· < ·)
  wellFounded := Nat.lt_wfRel.wf
  rank := descent.rank
  administrative := by
    intro first last formed update
    have bound := descent.administrative first last formed update
    by_cases equal : descent.rank last = descent.rank first
    · exact Or.inl equal
    · exact Or.inr (Nat.lt_of_le_of_ne bound equal)
  installation := descent.installation

theorem boundary_progress (roles : Roles.RoleDecls)
    (evidence : GeneralNominalFeedbackBoundary.Evidence roles)
    (registry : Registry) (root : Occurrence roles)
    (order : InstallationOrder registry root) (state : State roles)
    (formed : SourceFormed registry root state) :
    Acc (fun next current => (GeneralNominalFeedbackBoundary.boundary roles evidence).Step
      registry root current next) state := accessible order state formed

end Yulang.GeneralNominalFeedbackWellFounded
