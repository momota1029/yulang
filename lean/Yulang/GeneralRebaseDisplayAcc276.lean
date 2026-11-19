import Yulang.GeneralRebaseDisplayEvidenceAt276

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 9900000
namespace Yulang.GeneralRebaseDisplayAcc276
open GeneralNominalExamples (registry context state displayRoot displayChild model)
open GeneralNominalNonleafPlan193 (plan)
open GeneralDeclarationExamples (roles)
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalVersionedMixedKernel234 (Step Installable)
open GeneralRebaseDisplayFrame276 (before after frame effect source_ids)
open GeneralRebaseDisplayStable276 (halted)
open GeneralRebaseDisplayStep276 (actual_step)

theorem initial_generated {focus : GeneralSourceDictionaries.Occurrence roles}
 (path : GeneralNominalSaturationState.Generated before.core.erased.current displayRoot focus) :
 focus = displayRoot :=
 GeneralNominalVersionedMixedTerminalStable234.generated_only rfl rfl path

theorem initial_known (id : Nat) (supported : id ∈ GeneralNominalState.sources (state true)) :
 GeneralNominalState.Known before.core.erased.current.context.state id := by
 have small := source_ids id supported
 have either : id = 0 ∨ id = 1 := by omega
 rcases either with rfl|rfl
 · exact GeneralRebaseDisplayEndpoint276.known_zero
 · exact GeneralRebaseDisplayEndpoint276.known_one

theorem initial_effect_unique (candidate : Effect roles) (enabled : Installable registry before candidate)
 (rooted : candidate.plan.packet.site.occurrence = displayRoot) : candidate = effect := by
 have found := candidate.frame
 rw [enabled.registry_eq,enabled.snapshot_eq,rooted] at found
 have samePlan := GeneralRebaseScopedFrame276.same_frame found frame
   (GeneralRebaseScopedFrame276.declaration_for_focus found GeneralRebaseDisplayFrame276.wrong_not_prepared)
   (List.mem_singleton.mp found.raw_recorded) (List.mem_singleton.mp found.center_recorded)
 rcases candidate with ⟨reg,core,p,fr,unique,ready⟩
 have eReg : reg = registry := enabled.registry_eq
 have eCore : core = before.core := enabled.snapshot_eq
 change p = plan at samePlan
 subst reg; subst core; subst p
 rfl

theorem only_step (next : State roles) (given : Step registry displayRoot before next) : next = after := by
 obtain ⟨focus,generated,op⟩ := given
 have atRoot := initial_generated generated
 cases op with
 | administrative op =>
   cases op with
   | enqueue _ absent =>
     exact False.elim (absent _ (List.mem_singleton_self _) atRoot.symm)
   | refresh context cert id tracked unknown known =>
     exact False.elim (unknown (initial_known id tracked))
   | equate a b _ _ same novel =>
     have atEnd : GeneralNominalVersionedMixedKernel234.Equal after a b := fun m valid =>
       same m (GeneralNominalVersionedMixedKernel234.step_models actual_step valid)
     have sameID := GeneralRebaseDisplaySeparators276.equality_names a b atEnd
     subst b
     exact False.elim (novel (fun _ _ => ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩))
   | reobserve revision _ improves =>
     exact False.elim (GeneralNominalReobservationSteps.pointClosed_no_revision (state := before.core.erased.current)
        (fun slot descriptor seen => GeneralRebaseDisplayStable276.point_closed slot descriptor seen) revision improves)
 | refresh _ context cert id tracked unknown known =>
   exact False.elim (unknown (initial_known id tracked))
 | install candidate enabled novel =>
   have same := initial_effect_unique candidate enabled atRoot
   subst candidate
   rfl
 | merge a b x y same novel =>
   change a ∈ [_] at x
   change b ∈ [_] at y
   cases List.mem_singleton.mp x
   cases List.mem_singleton.mp y
   exact False.elim (novel (.refl _))

theorem step_exact (next : State roles) : Step registry displayRoot before next ↔ next = after :=
 ⟨only_step next,by rintro rfl; exact actual_step⟩

theorem source_acc : Acc (fun next prev => Step registry displayRoot prev next) before := by
 constructor
 intro next action
 cases only_step next action
 constructor
 intro last forbidden
 exact False.elim (halted last forbidden)

theorem exact_reached (next : State roles)
 (path : B4Target.Steps (Step registry displayRoot) before next) : next = before ∨ next = after := by
 induction path with
 | refl => exact Or.inl rfl
 | tail _ action ih =>
   rcases ih with rfl|rfl
   · exact Or.inr (only_step _ action)
   · exact False.elim (halted _ action)

end Yulang.GeneralRebaseDisplayAcc276
