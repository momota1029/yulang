import Yulang.GeneralNominalCenteredTerminalObservations
import Yulang.GeneralNominalCenteredMergeAvailability

/-! Every reachable centered snapshot retains its unique source context.
Terminal Local agreement from that common ground source suffices for the exact
V5 order field. Requiring all primitive terminal observations is stronger and
fails on the concrete descriptor fork. -/
namespace Yulang.GeneralNominalCenteredTerminalAgreement
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenteredSteps
open GeneralNominalCenteredAdministrativeLocal
open GeneralNominalCenteredAdministrativeComposition

variable {roles : Roles.RoleDecls}

theorem source_at (action : At registry before focus after) : after.erased.source = before.erased.source := by
  cases action <;> rfl

theorem source_steps (path : B4Target.Steps (Step registry root) before after) : after.erased.source = before.erased.source := by
  induction path with
  | refl => rfl
  | tail path step ih => exact (source_at step.choose_spec.2).trans ih

theorem reachable_source
    (reachable : B4TargetV5.Reachable (boundary roles) registry root state) :
    ∃ labels, GeneralNominalSourceFormation.InitialSource registry state.erased.source root ∧
      (∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2) ∧
      GeneralNominalGroundAccessibility.GroundRoots state.erased.source root labels ∧
      B4Target.Steps (Step registry root) (initial state.erased.source root) state := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := reachable
  have same : state.erased.source = context := source_steps path
  exact ⟨labels,same ▸ source,point,same ▸ ground,same ▸ path⟩

private theorem append_steps (first : B4Target.Steps relation start middle)
    (last : B4Target.Steps relation middle finish) : B4Target.Steps relation start finish := by
  induction last with
  | refl => exact first
  | tail prior step ih => exact .tail ih step

def TerminalLocalConfluence (roles : Roles.RoleDecls) : Prop :=
  ∀ first last, (boundary roles).Checked first → (boundary roles).Checked last → (boundary roles).Reorders first last →
    ∀ context (root : Occurrence roles) labels, GeneralNominalSourceFormation.InitialSource first context root →
    (∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2) →
    GeneralNominalGroundAccessibility.GroundRoots context root labels → ∀ left right,
    B4Target.Steps (Step first root) (initial context root) left →
    B4Target.Steps (Step last root) (initial context root) right →
    (∀ next, ¬ Step first root left next) → (∀ next, ¬ Step last root right next) → ∀ demand frontier,
    Local last left demand frontier ↔ Local last right demand frontier

def TerminalObservationConfluence (roles : Roles.RoleDecls) : Prop :=
  ∀ first last, (boundary roles).Checked first → (boundary roles).Checked last → (boundary roles).Reorders first last →
    ∀ context (root : Occurrence roles) labels, GeneralNominalSourceFormation.InitialSource first context root →
    (∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2) →
    GeneralNominalGroundAccessibility.GroundRoots context root labels → ∀ left right,
    B4Target.Steps (Step first root) (initial context root) left →
    B4Target.Steps (Step last root) (initial context root) right →
    (∀ next, ¬ Step first root left next) → (∀ next, ¬ Step last root right next) →
    ObservationAgreement last left right

theorem final_local_of_terminal (confluent : TerminalLocalConfluence roles) : FinalLocalAgreement roles := by
  intro first last checked checkedLast order state root reached reachedLast demand frontier
  obtain ⟨labels,source,point,ground,leftPath⟩ := reachable_source reached
  obtain ⟨otherLabels,otherSource,otherPoint,otherGround,rightPath⟩ := reachable_source reachedLast
  exact confluent first last checked checkedLast order state.erased.source root labels source point ground _ _
    (append_steps leftPath (execution first checked state root reached))
    (append_steps rightPath (execution last checkedLast state root reachedLast))
    (halted first checked state root reached) (halted last checkedLast state root reachedLast) demand frontier

theorem canonicalLocalOrder_of_terminal (confluent : TerminalLocalConfluence roles) : CanonicalLocalOrder roles :=
  canonicalLocalOrder_iff_final_local_agreement.mpr (final_local_of_terminal confluent)

theorem observation_confluence_suffices (confluent : TerminalObservationConfluence roles) : TerminalLocalConfluence roles := by
  intro first last checked checkedLast order context root labels source point ground left right leftPath rightPath leftHalted rightHalted demand frontier
  exact observation_local (confluent first last checked checkedLast order context root labels source point ground
    left right leftPath rightPath leftHalted rightHalted) demand frontier

theorem terminal_observation_confluence_false : ¬ TerminalObservationConfluence GeneralDeclarationExamples.roles := by
  intro confluent
  open GeneralNominalCenteredTerminalForkSource in
    exact GeneralNominalCenteredTerminalObservations.observations_different
      (confluent registry registry ⟨rfl,registry_checked⟩ ⟨rfl,registry_checked⟩
        (GeneralRegistryReordering.reorders_refl registry) (context none) root [.app 2 []]
        (source none) (fun _ => rfl) ground (finish false) (finish true)
        (.tail .refl (step false)) (.tail .refl (step true)) (halted false) (halted true))

end Yulang.GeneralNominalCenteredTerminalAgreement
