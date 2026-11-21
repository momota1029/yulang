import Yulang.GeneralPositiveForkHalt309

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 15000000
namespace Yulang.GeneralPositiveForkMachine309
open GeneralPositiveForkSource309 (initial init_model init_source root compiled)
open GeneralPositiveForkPlan309 (plan)
open GeneralPositiveForkPreinstall309 (frame member_parent effect)
open GeneralPositiveForkInstall309 (after step edges)
open GeneralPositiveForkHalt309 (halted point_closed known0 known1)
open GeneralNominalVersionedMixedKernel234 (Step Installable)
open GeneralNominalVersionedMixedTerminalStable234 (HeadlessUnknown EqualityClosed no_refresh generated_only)
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralDeclarationExamples (roles)

theorem initial_headless : HeadlessUnknown initial := by
  refine ⟨_,init_model,?_⟩
  intro id occurs unknown _ _
  have small := init_source.below_seed _ occurs
  change id ≤ 1 at small
  have exactCases : id = 0 ∨ id = 1 := by omega
  rcases exactCases with rfl|rfl
  · exact unknown known0
  · exact unknown known1

theorem initial_equality : EqualityClosed initial := by
  intro a b _ _ entailed m raw
  exact entailed m ((GeneralNominalVersionedJournal232.initial_models ..).mpr
    ⟨raw,GeneralNominalCenters.point_root_holds _ _ (fun _ => rfl) _⟩)

theorem same_effect (e : Effect roles) (enabled : Installable compiled initial e)
    (atRoot : e.plan.packet.site.occurrence = root) : e = effect := by
  have f := e.frame
  rw [enabled.registry_eq,enabled.snapshot_eq,atRoot] at f
  have eq := GeneralRebaseScopedFrame276.same_frame f frame (member_parent f.visible f.role_eq)
    (List.mem_singleton.mp f.raw_recorded) (List.mem_singleton.mp f.center_recorded)
  rcases e with ⟨reg,snap,p,_,_,_⟩
  have first : reg = compiled := enabled.registry_eq
  have second : snap = initial.core := enabled.snapshot_eq
  subst reg; subst snap
  cases eq
  rfl

theorem exact_initial (t : State roles) : Step compiled root initial t ↔ t = after := by
  constructor
  · rintro ⟨focus,generated,op⟩
    have rootOnly := generated_only rfl rfl generated
    cases op with
    | administrative act =>
      cases act with
      | enqueue _ missing =>
        exact False.elim (missing _ (List.mem_singleton_self _) rootOnly.symm)
      | refresh _ cert _ tracked old new => exact False.elim (no_refresh initial_headless cert tracked old new)
      | equate a b one two entailed novel => exact False.elim (novel (initial_equality a b one two entailed))
      | reobserve rev _ improves =>
        exact False.elim (GeneralNominalReobservationSteps.pointClosed_no_revision (state := initial.core.erased.current) point_closed rev improves)
    | refresh _ _ cert _ tracked old new => exact False.elim (no_refresh initial_headless cert tracked old new)
    | install e enabled _ => exact congrArg (GeneralNominalVersionedInstall232.install initial) (same_effect e enabled rootOnly)
    | merge a b one two _ novel =>
      cases List.mem_singleton.mp one
      cases List.mem_singleton.mp two
      exact False.elim (novel (.refl _))
  · rintro rfl
    exact step

theorem distinct : initial ≠ after := by
  intro same
  have j := congrArg (fun s : State roles => s.core.erased.current.edges) same
  rw [edges] at j
  cases j

inductive Phase where | pre | post deriving DecidableEq, Repr
abbrev raw : Phase → State roles | .pre => initial | .post => after
def next : Phase → Option Phase | .pre => some .post | .post => none

theorem next_exact (p : Phase) (t : State roles) :
    Step compiled root (raw p) t ↔ ∃ q, next p = some q ∧ t = raw q := by
  cases p
  · rw [exact_initial]
    constructor
    · intro r; exact ⟨.post,rfl,r⟩
    · rintro ⟨q,h,r⟩
      cases Option.some.inj h
      exact r
  · exact ⟨fun impossible => False.elim (halted _ impossible),by rintro ⟨_,hit,_⟩; cases hit⟩

theorem all_reachable (t : State roles)
    (trace : B4Target.Steps (Step compiled root) initial t) : t = initial ∨ t = after := by
  induction trace with
  | refl => exact Or.inl rfl
  | tail _ one ih =>
    rcases ih with rfl|rfl
    · exact Or.inr ((exact_initial _).mp one)
    · exact False.elim (halted _ one)

theorem accessible : Acc (fun t s => Step compiled root s t) initial := by
  refine .intro _ (fun t h => ?_)
  rw [(exact_initial _).mp h]
  exact .intro _ (fun _ bad => False.elim (halted _ bad))

end Yulang.GeneralPositiveForkMachine309
