import Yulang.GeneralRebasePreInstallReplay297

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseSourceMetadata297
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalCandidates (Context Metadata)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded)
open GeneralRebaseSourceWitnessProgram297 (Checks Observed Holds questions)
open GeneralRebaseSourceQuestions297 (entries)
open GeneralRebaseRawObserver297 (ExactSafety observe)
open GeneralRebaseFiniteWitnessTable297 (Covers)
open GeneralNominalCommonBridge (Assignment)
open GeneralSourceState (Output)

def current (s : State roles) : Context := s.core.erased.current.context

theorem context_equalities {r : Registry} {root : Occurrence roles}
    {before after : State roles} (action : Step (Encoded r) root before after) :
    (current after).state.constructors = (current before).state.constructors ∧
      (current after).interpretation = (current before).interpretation := by
  obtain ⟨f,_,next⟩ := action
  cases next with
  | administrative admin =>
    cases admin with
    | refresh ctx cert _ _ _ _ => exact ⟨cert.refines.constructors,cert.interpretation⟩
    | enqueue => exact ⟨rfl,rfl⟩
    | equate => exact ⟨rfl,rfl⟩
    | reobserve => exact ⟨rfl,rfl⟩
  | refresh _ ctx cert _ _ _ _ => exact ⟨cert.refines.constructors,cert.interpretation⟩
  | merge => exact ⟨rfl,rfl⟩
  | install e enabled _ =>
    have eq : e.plan.packet.context = current before :=
      e.frame.context_eq.trans (congrArg (fun c : GeneralNominalCenteredSteps.State roles => c.erased.current.context) enabled.snapshot_eq)
    have sameConstructors : (current (GeneralNominalVersionedInstall232.install before e)).state.constructors =
        e.plan.packet.context.state.constructors := rfl
    have sameInterpretation : (current (GeneralNominalVersionedInstall232.install before e)).interpretation =
        e.plan.packet.context.interpretation := rfl
    exact ⟨sameConstructors.trans (congrArg (fun c : Context => c.state.constructors) eq),
      sameInterpretation.trans (congrArg Context.interpretation eq)⟩

theorem fixed_metadata {r : Registry} {root : Occurrence roles}
    {before after : State roles} (action : Step (Encoded r) root before after) :
    Metadata (Encoded r) (current after) ↔ Metadata (Encoded r) (current before) := by
  obtain ⟨constructors,interpretation⟩ := context_equalities action
  unfold Metadata
  rw [constructors,interpretation]

theorem reachable_metadata {r : Registry} {root : Occurrence roles} {s : State roles}
    (path : B4TargetV8.Reachable (Boundary roles) r root s) :
    Metadata (Encoded r) (current s) := by
  obtain ⟨first,init,run⟩ := path
  have read : Metadata (Encoded r) (current first) := by
    obtain ⟨legacy,⟨ctx,_,source,_,_,_,legacyEq⟩,firstEq⟩ := init
    subst first
    subst legacy
    exact source.metadata
  induction run with
  | refl => exact read
  | tail _ step ih => exact (fixed_metadata step).mpr ih

theorem source_strict_exact {r : Registry} {s : State roles} {root : Occurrence roles}
    {checked : (Boundary roles).Checked r} {xs : List Assignment} {c : Checks roles}
    {safety : Occurrence roles → Bool}
    (reach : B4TargetV8.Reachable (Boundary roles) r root s)
    (safe : ExactSafety r s root safety)
    (cover : Covers (Holds s) (questions r s root checked) xs)
    (cert : Observed s xs (entries r s root checked) c)
    (owners : List Nat) (pool : List Output)
    (t : GeneralRebaseStep258.State (GeneralRebaseCompression266.Basis owners pool)) :
    GeneralRebaseStep258.Step (observe r s root checked xs c safety owners pool)
      (GeneralRebaseLiveProjection264.project owners pool s) t ↔
    ∃ after, (Boundary roles).Step r root s after ∧
      GeneralRebaseLiveProjection264.project owners pool after = t ∧
      t ≠ GeneralRebaseLiveProjection264.project owners pool s :=
  GeneralRebaseRawObserver297.strict_exact reach (reachable_metadata reach) safe cover cert owners pool t

end Yulang.GeneralRebaseSourceMetadata297
