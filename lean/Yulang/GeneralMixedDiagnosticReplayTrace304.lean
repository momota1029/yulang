import Yulang.GeneralMixedDiagnosticReplayStep304
import Yulang.GeneralNominalVersionedMixedEmbedding234

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralMixedDiagnosticReplayTrace304
open GeneralDeclarations GeneralSourceDictionaries CommonRoleOutermostResolver
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalVersionedInstall232 (install)
open GeneralNominalVersionedMixedKernel234 (Step Installable Committed)
open GeneralNominalSaturationState (Generated)
open GeneralDeferredLadderOperationalView304 (choices generated_iff committed_iff after_choices)
open GeneralDeferredLadderResnapshot304 (HeadView resnapshot)
open GeneralMixedDiagnosticSlice304 (Semantics)
open GeneralMixedDiagnosticSliceReplay304 (KeepsRequests stays_on_other_side semantics_after)
open GeneralMixedDiagnosticReplayStep304 (mirrored_installable after_head)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)

variable {roles : Roles.RoleDecls}

abbrev operationalRegistry := GeneralNominalCenteredHeadAllocEncoding.registry
abbrev Reached (reg : Registry) (root : Occurrence roles) :=
  B4TargetV8.Reachable (boundary roles) reg root

/-- A subrelation of actual mixed-kernel steps, retaining just installs
that do not widen any live output-request class. -/
inductive Trace (reg : Registry) (root : Occurrence roles) : Nat → State roles → State roles → Prop
  | zero (s : State roles) : Trace reg root 0 s s
  | more : Trace reg root count start s →
      (e : Effect roles) →
      Installable (operationalRegistry reg) s e →
      KeepsRequests s e.plan →
      Generated s.core.erased.current root e.plan.packet.site.occurrence →
      ¬ Committed s e.plan →
      Trace reg root (count+1) start (install s e)

theorem trace_raw (path : Trace reg root length a b) :
    B4Target.Steps ((boundary roles).Step reg root) a b := by
  induction path with
  | zero => exact .refl
  | more _ e good _ generated novel ih =>
    exact .tail ih ⟨_,generated,.install e good novel⟩

structure Agree (a b : State roles) : Prop where
  head : HeadView a b
  sliced : Semantics a b
  chosen : choices a = choices b

theorem Agree.symm {a b : State roles} (same : Agree a b) : Agree b a :=
  ⟨same.head.symm,same.sliced.symm,same.chosen.symm⟩

theorem exact_trace {reg : Registry} {root : Occurrence roles}
    {a b : State roles} (same : Agree a b) (targetReached : Reached reg root b)
    (path : Trace reg root length a x) :
    ∃ y, Trace reg root length b y ∧ Agree x y ∧ Reached reg root y := by
  induction path with
  | zero => exact ⟨b,.zero b,same,targetReached⟩
  | more _ e good stable generated novel ih =>
    obtain ⟨bNow,tr,agree,reached⟩ := ih same
    let f := resnapshot agree.head e good.snapshot_eq
    have bGood := mirrored_installable agree.head agree.chosen e good stable
      (GeneralNominalVersionedMixedEmbedding234.source_cache reached)
    have bStable : KeepsRequests bNow f.plan := stays_on_other_side agree.head e.plan stable
    have bGenerated : Generated bNow.core.erased.current root f.plan.packet.site.occurrence :=
      (generated_iff agree.head.raw).mp generated
    have bNovel : ¬ Committed bNow f.plan :=
      fun found => novel ((committed_iff agree.head.raw e.plan).mpr found)
    refine ⟨install bNow f,.more tr f bGood bStable bGenerated bNovel,?_,?_⟩
    · exact ⟨after_head agree.head e good.snapshot_eq stable,
        semantics_after agree.head agree.sliced e good.snapshot_eq stable,
        after_choices agree.chosen e f rfl rfl⟩
    · obtain ⟨seed,initial,steps⟩ := reached
      exact ⟨seed,initial,.tail steps ⟨_,bGenerated,.install f bGood bNovel⟩⟩

theorem final_local {reg : Registry} {root : Occurrence roles} {a b : State roles}
    (same : Agree a b) (targetReached : Reached reg root b) (path : Trace reg root length a x) :
    ∃ y, Trace reg root length b y ∧
      ∀ demand front, (B4TargetV8.Local (boundary roles) reg x demand front ↔
        B4TargetV8.Local (boundary roles) reg y demand front) := by
  obtain ⟨y,tr,agree,_⟩ := exact_trace same targetReached path
  refine ⟨y,tr,?_⟩
  intro demand front
  exact (GeneralNominalVersionedMixedSourceBoundary234.local_iff.trans
    (GeneralNominalVersionedMixedBoundary234.local_iff.trans
      ((GeneralMixedDiagnosticLocal304.local_iff agree.head agree.sliced (operationalRegistry reg) demand front).trans
        (GeneralNominalVersionedMixedBoundary234.local_iff.symm.trans
          GeneralNominalVersionedMixedSourceBoundary234.local_iff.symm))))

end Yulang.GeneralMixedDiagnosticReplayTrace304
