import Yulang.GeneralRebaseSourceClassification267
import Yulang.GeneralNominalVersionedInstallStep232

namespace Yulang.GeneralRebaseInstallChecks267
open GeneralNominalSaturationState (State Packet)
open GeneralNominalCenters (Plan)
open GeneralSourceDictionaries (Occurrence)
open GeneralRebaseExecutableAlias267 (aliased aliased_exact)

def choice (state : State roles) (packet : Packet roles) : Bool :=
 state.packets.all fun prior =>
   !(aliased state packet.site.occurrence.identity prior.site.occurrence.identity) ||
   packet.declaration.id == prior.declaration.id

theorem choice_exact (state : State roles) (packet : Packet roles) :
 choice state packet = true ↔ GeneralNominalCycleSteps.ChoiceCompatible state packet := by
 simp only [choice,List.all_eq_true,Bool.or_eq_true,Bool.not_eq_true',beq_iff_eq,
   ←Bool.not_eq_true,aliased_exact,GeneralNominalCycleSteps.ChoiceCompatible]
 constructor
 · intro every prior listed alias
   exact (every prior listed).resolve_left (fun rejected => rejected alias)
 · intro every prior listed
   by_cases linked : GeneralNominalSaturationState.Alias state
       packet.site.occurrence.identity prior.site.occurrence.identity
   · exact Or.inr (every prior listed linked)
   · exact Or.inl linked

local instance : DecidableEq (Occurrence roles) := GeneralRebaseOccurrenceEq267.occurrenceEq

def edgesRecorded (state : State roles) (plan : Plan roles) : Bool :=
 (GeneralNominalVersionedFrame231.children plan.packet).all fun child =>
   decide ((plan.packet.site.occurrence,child) ∈ state.edges)

theorem edgesRecorded_exact (state : State roles) (plan : Plan roles) :
 edgesRecorded state plan = true ↔ ∀ child ∈ GeneralNominalVersionedFrame231.children plan.packet,
   (plan.packet.site.occurrence,child) ∈ state.edges := by
 simp only [edgesRecorded,List.all_eq_true,decide_eq_true_eq]

theorem missing_edge_proves_novel (state : GeneralNominalVersionedJournal232.State roles) (plan : Plan roles)
 (missing : edgesRecorded state.core.erased.current plan = false) :
 ¬ GeneralNominalVersionedInstallStep232.Committed state plan := by
 intro recorded
 have conflict := (edgesRecorded_exact _ _).mpr recorded.2
 simp [missing] at conflict

def semanticCommitted (state : GeneralNominalVersionedJournal232.State roles) (plan : Plan roles) : Prop :=
 ∀ model, GeneralNominalVersionedJournal232.Models state model →
   GeneralNominalVersionedPlans231.Holds plan model ∧
   GeneralNominalVersionedEffects231.ClassEffects state.core plan.packet.site.occurrence plan model

theorem committed_exact (state : GeneralNominalVersionedJournal232.State roles) (plan : Plan roles) :
 GeneralNominalVersionedInstallStep232.Committed state plan ↔
 semanticCommitted state plan ∧ edgesRecorded state.core.erased.current plan = true :=
 and_congr_right' (edgesRecorded_exact _ _).symm

theorem novel_exact (state : GeneralNominalVersionedJournal232.State roles) (plan : Plan roles) :
 (¬ GeneralNominalVersionedInstallStep232.Committed state plan) ↔
 edgesRecorded state.core.erased.current plan = false ∨ ¬ semanticCommitted state plan := by
 rw [committed_exact]
 cases h : edgesRecorded state.core.erased.current plan <;> simp

end Yulang.GeneralRebaseInstallChecks267
