import Yulang.GeneralDictionarySupportRecursiveJoint

/-! Exact one-step trace shape for the concrete recursive support fixture.
This is not a general progress theorem or a canonical evaluation strategy. -/
namespace Yulang.GeneralDictionarySupportRecursiveTrace
open GeneralDictionarySupportRecursiveExample GeneralDictionarySupportRecursiveClassification
open GeneralDictionarySupportRecursiveClosure
open GeneralNominalExamples
open GeneralDeclarationExamples (roles display)
open GeneralNominalSaturationState GeneralSourceDictionaries

private theorem initial_generated (focus : Occurrence roles) (reached : Generated start.current displayRoot focus) :
    focus = displayRoot := by
  induction reached with
  | root => rfl
  | child _ member _ => cases member
  | alias _ _ member _ _ =>
    have same : _ = GeneralNominalDemandMerging.pointSite displayRoot := List.mem_singleton.mp member
    exact congrArg GeneralNominalDemandMerging.Site.occurrence same

/-- Any enabled initial packet is the already exhibited concrete packet. -/
theorem initial_packet_unique (p : Packet roles)
    (enabled : GeneralNominalFeedbackSteps.Installable registry start.current p) : p = packet := by
  rcases p with ⟨preg,pctx,psite,pdecl,pchecked,pbounds⟩
  have reg := enabled.1.1
  have ctx := enabled.1.2.1
  have member := enabled.1.2.2.1
  change preg = registry at reg
  change pctx = context true at ctx
  change psite ∈ [GeneralNominalDemandMerging.pointSite displayRoot] at member
  have site := List.mem_singleton.mp member
  subst preg; subst pctx; subst psite
  have selected := enabled.2.1
  have original := GeneralNominalSupportBoundary.selected_old GeneralNominalSupportExamples.display_selected
  have same := GeneralNominalFeedbackK2.local_functional selected original
  have key := (CommonRoleOutermostResolver.Frontier.selected.inj same).1
  have visible := enabled.1.2.2.2.1
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with decl | decl | decl
  · subst pdecl; cases key
  · subst pdecl
    have found := enabled.1.2.2.2.2.2.1
    change GeneralNominalRecursiveCandidates.arguments (context true) displayRoot = some pbounds at found
    have located : GeneralNominalRecursiveCandidates.arguments (context true) displayRoot = some [(0,0)] := rfl
    have equal := Option.some.inj (found.symm.trans located)
    subst pbounds
    rfl
  · subst pdecl; cases key

private theorem initial_known (source : Nat) (member : source ∈ GeneralNominalState.sources start.current.context.state) :
    GeneralNominalState.Known start.current.context.state source := by
  have small : source = 0 ∨ source = 1 := by
    change source ∈ [0,1,0,1] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    omega
  rcases small with rfl | rfl
  · exact ⟨(0 : Fin 2),rfl,Or.inr ⟨listDescriptor,rfl⟩⟩
  · exact ⟨(1 : Fin 2),rfl,Or.inl (by decide +kernel)⟩

/-- Initial administrative changes are impossible: all sources are Known,
nominal descriptors are point-valued, and its context already describes all
journal models. -/
theorem initial_no_administrative (after : State roles)
    (update : GeneralNominalSupportSteps.Administrative registry start.current displayRoot after) : False := by
  cases update with
  | enqueue _ absent =>
    exact absent (GeneralNominalDemandMerging.pointSite displayRoot) (List.mem_singleton_self _) rfl
  | refresh _ _ source member unknown _ => exact unknown (initial_known source member)
  | equate first last _ _ equal novel =>
    exact novel (fun m valid => equal m ((initial_models ..).mpr valid))
  | reobserve revision _ improved =>
    have closed : GeneralNominalReobservationSteps.PointClosed start.current.context.state := by
      exact point_closed
    exact GeneralNominalReobservationSteps.pointClosed_no_revision closed revision improved

/-- Every actual source-support Step at start is exactly the exhibited finish,
independently of the supplied support certificate. -/
theorem first_step_unique (after : GeneralNominalSupport.Tracked roles)
    (step : GeneralNominalSupportSteps.Step registry displayRoot start after) : after = finish := by
  obtain ⟨focus,reached,update⟩ := step
  have same := initial_generated focus reached
  cases update with
  | administrative _ _ update =>
    rw [same] at update
    exact False.elim (initial_no_administrative _ update)
  | install p support enabled _ _ =>
    have packetSame := initial_packet_unique p enabled
    subst p
    rfl
  | merge first last support one two _ novel _ =>
    have oneSame : first = GeneralNominalDemandMerging.pointSite displayRoot := List.mem_singleton.mp one
    have twoSame : last = GeneralNominalDemandMerging.pointSite displayRoot := List.mem_singleton.mp two
    subst first; subst last
    exact False.elim (novel (.refl _))

theorem finish_no_step (after : GeneralNominalSupport.Tracked roles) :
    ¬ GeneralNominalSupportSteps.Step registry displayRoot finish after := by
  rintro ⟨focus,reached,update⟩
  exact stable focus reached after update

/-- Every finite actual trace is empty, or takes the single installation and
cannot continue. No unrestricted source program is covered by this result. -/
theorem trace_endpoints (after : GeneralNominalSupport.Tracked roles)
    (path : B4Target.Steps (GeneralNominalSupportSteps.Step registry displayRoot) start after) :
    after = start ∨ after = finish := by
  induction path with
  | refl => exact Or.inl rfl
  | tail _ step ih =>
    rcases ih with previous | previous
    · subst_vars
      exact Or.inr (first_step_unique _ step)
    · subst_vars
      exact False.elim (finish_no_step _ step)

theorem initial_not_stable : ¬ GeneralNominalSupportSteps.Stable registry start displayRoot := by
  intro closed
  obtain ⟨focus,reached,update⟩ := actual_step
  exact closed focus reached finish update

/-- Stable endpoints of finite executions from this concrete initial source
are uniquely the proved recursive completion. -/
theorem stable_endpoint_iff (after : GeneralNominalSupport.Tracked roles)
    (path : B4Target.Steps (GeneralNominalSupportSteps.Step registry displayRoot) start after) :
    GeneralNominalSupportSteps.Stable registry after displayRoot ↔ after = finish := by
  constructor
  · intro halted
    rcases trace_endpoints after path with same | same
    · subst after; exact False.elim (initial_not_stable halted)
    · exact same
  · rintro rfl
    exact stable

end Yulang.GeneralDictionarySupportRecursiveTrace
