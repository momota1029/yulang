import Yulang.GeneralNominalRawSeparation184
import Yulang.GeneralNominalPredicateExtension182

/-! Reachability supplies raw-journal preservation for high-namespace updates.
Only actual centered ledger overlap remains in the conservative-extension test. -/
namespace Yulang.GeneralNominalGroundLedgerExtension184
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalCenteredGroundBoundary (groundBoundary)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection (Observes)
open GeneralNominalCenteredModelExtension (assign originSource assign_preserves)
open GeneralNominalModeLedger181 (ledgerSources fullSources)
open CommonNominalFullCarrier
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}

def HighNames (state : State roles) (names : Fin count → Nat) : Prop :=
  ∀ index, ∃ invocation declaration purpose owner position, 7 ≤ purpose ∧
    names index = fresh state.erased.current.context.state.seed invocation declaration purpose owner position

theorem centered_assign_kept
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (names : Fin count → Nat) (values : Fin count → Ty) (high : HighNames state names)
    (model : Assignment) (valid : Models state model)
    (kept : ∀ index, names index ∈ ledgerSources state → values index = (model (names index)).1) :
    Models state (assign model names values) := by
  apply GeneralNominalModeLedger181.ledger_frame state _ valid
    (GeneralNominalRawSeparation184.raw_assign_preserves reachable names values high model valid.1)
  intro name member
  apply Eq.symm
  apply assign_preserves
  intro index equal
  simpa only [equal] using kept index (equal.symm ▸ member)

theorem centered_assign_disjoint
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (names : Fin count → Nat) (values : Fin count → Ty) (high : HighNames state names)
    (model : Assignment) (valid : Models state model)
    (outside : ∀ index, names index ∉ ledgerSources state) :
    Models state (assign model names values) :=
  centered_assign_kept reachable names values high model valid (fun index member => False.elim (outside index member))

theorem extension_iff_ledger
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (arguments : Fin count → NominalArgument)
    (high : HighNames state (fun index => (arguments index).argument.center))
    (previous : Assignment) (valid : Models state previous)
    (linked : ∀ i, (arguments i).argument.endpoints.1 ∈ fullSources state ∧
      (arguments i).argument.endpoints.2 ∈ fullSources state ∧ originSource (arguments i).origin ∈ fullSources state) :
    (∃ extended, Models state extended ∧
      (∀ name ∈ fullSources state, extended name = previous name) ∧ ∀ i, (arguments i).Holds extended) ↔
    (∀ i, ∃ actual, Observes previous (arguments i).origin actual) ∧
    (∀ i actual, Observes previous (arguments i).origin actual →
      GeneralNominalCaptureMerges.Fits previous (arguments i).argument.endpoints actual) ∧
    (∀ i j first last, (arguments i).argument.center = (arguments j).argument.center →
      Observes previous (arguments i).origin first → Observes previous (arguments j).origin last → Equivalent first last) ∧
    (∀ i actual, (arguments i).argument.center ∈ ledgerSources state →
      Observes previous (arguments i).origin actual → Equivalent actual (previous (arguments i).argument.center).1) := by
  rw [GeneralNominalPredicateExtension182.extension_iff (Models state) (fullSources state)
    (fun _ _ same => GeneralNominalModeLedger181.centered_models_frame state same)
    arguments previous valid linked]
  have overlap i : (arguments i).argument.center ∈ fullSources state ↔
      (arguments i).argument.center ∈ ledgerSources state := by
    obtain ⟨invocation,declaration,purpose,owner,position,large,equal⟩ := high i
    dsimp only at equal
    rw [equal]
    exact GeneralNominalRawSeparation184.overlap_iff_ledger reachable large
  simp only [overlap]

end Yulang.GeneralNominalGroundLedgerExtension184
