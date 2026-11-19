import Yulang.GeneralRebaseTerminalPublic274
import Yulang.GeneralRebaseTypeOnlyAtoms273

namespace Yulang.GeneralRebaseTerminalRowTransfer274
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedPlans231
open GeneralNominalVersionedJournal232 (State Models)
open GeneralRebaseRowIrrelevance273 (SameTypes)
open GeneralRebaseTypeOnlyAtoms273 (all_iff atomTypeOnly)
open GeneralNominalVersionedPacketFrame236 (holds_shape)
open PresenceNormalForm (All)

def Invariant (valid : Assignment → Prop) : Prop :=
 ∀ {first last}, SameTypes first last → (valid first ↔ valid last)

theorem transfer_same (first last : Assignment) (same : SameTypes first last) :
 GeneralNominalAssignmentCongruence238.Same first last ↔ ∀ id, (first id).2 = (last id).2 := by
 constructor
 · intro h id; exact (h id).2
 · intro h id
   refine ⟨?_,h id⟩
   rw [same id]
   exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩

theorem ordinary (plan : Plan roles)
 (merges : (GeneralNominalVersionedAllocation231.merges plan.packet.context.state plan.packet.registry
   plan.packet.site.occurrence.identity plan.packet.declaration plan.packet.bindings).all atomTypeOnly = true)
 (checks : (GeneralNominalRecursiveInspection.selfChecks plan.packet.context.state
   (GeneralNominalPacketSupport.report plan.packet)).all atomTypeOnly = true) :
 Invariant (Ordinary plan.packet) := by
 intro first last same
 unfold Ordinary
 apply and_congr ?_ (and_congr (all_iff same _ merges) (all_iff same _ checks))
 unfold GeneralNominalAllocation.Compatible
 exact forall_congr' fun a => forall_congr' fun _ => forall_congr' fun b => forall_congr' fun _ =>
   forall_congr' fun _ => by rw [same a.2.1,same b.2.2]

theorem head (plan : Plan roles) (raw : Invariant (GeneralNominalState.Models plan.packet.context.state))
 (ordinary : Invariant (Ordinary plan.packet)) : Invariant (HeadModels plan.packet) := by
 intro first last same
 unfold HeadModels
 rw [private_models_iff,private_models_iff]
 exact and_congr (and_congr (raw same) (ordinary same))
   (GeneralRebaseRowIrrelevance273.projection same _ _)

theorem holds (plan : Plan roles) (head : Invariant (HeadModels plan.packet)) : Invariant (Holds plan) := by
 intro first last same
 rw [holds_shape,holds_shape]
 apply and_congr (head same)
 apply and_congr (GeneralRebaseRowIrrelevance273.site same plan.input)
 apply and_congr
 · exact forall_congr' fun n => forall_congr' fun _ => by
     rw [same (GeneralNominalVersionedFrame231.binder plan n)]
     exact GeneralRebaseRowIrrelevance273.capture same _ _
 apply and_congr (GeneralRebaseRowIrrelevance273.head_schema same plan plan.headSchema)
 apply and_congr
 · exact forall_congr' fun eq => forall_congr' fun _ => forall_congr' fun _ =>
     GeneralRebaseRowIrrelevance273.equation same plan eq
 apply and_congr
 · exact forall_congr' fun clause => forall_congr' fun _ => forall_congr' fun valid =>
     and_congr (GeneralRebaseRowIrrelevance273.site same _) (GeneralRebaseRowIrrelevance273.schema same plan (childSchema plan clause valid))
 · exact GeneralRebaseRowIrrelevance273.schema same plan (emittedSchema plan)

theorem raw_site (site : GeneralNominalDemandMerging.Site roles) :
 Invariant (GeneralNominalSaturationState.SiteHolds site) := by
 intro first last same
 unfold GeneralNominalSaturationState.SiteHolds
 exact forall_congr' fun index => forall_congr' fun origin => forall_congr' fun _ => by
   simp only [GeneralRebaseRowIrrelevance273.occurs same,GeneralRebaseRowIrrelevance273.capture same]

theorem legacy (s : State roles) (empty : GeneralNominalVersionedMixedRegistry234.LegacyEmpty s)
 (current : Invariant (GeneralNominalState.Models s.core.erased.current.context.state))
 (base : Invariant (GeneralNominalState.Models s.core.erased.source.state)) :
 Invariant (GeneralNominalVersionedJournal232.Legacy.Models s.legacy) := by
 intro first last same
 unfold GeneralNominalVersionedJournal232.Legacy.Models GeneralNominalCenteredHeadMatStepJournal.Models
 rw [empty.1,empty.2]
 simp only [List.not_mem_nil,false_implies]
 exact and_congr (current same) (and_congr (base same)
   (and_congr (forall_congr' fun site => forall_congr' fun _ => raw_site site same)
     (and_congr (forall_congr' fun site => forall_congr' fun _ => GeneralRebaseRowIrrelevance273.site same site) Iff.rfl)))

theorem journal (s : State roles)
 (legacy : Invariant (GeneralNominalVersionedJournal232.Legacy.Models s.legacy))
 (plans : ∀ p ∈ s.plans, Invariant (HeadModels p.packet))
 (effects : ∀ e ∈ s.effects, Invariant (HeadModels e.plan.packet)) :
 Invariant (Models s) := by
 intro first last same
 unfold Models
 apply and_congr (legacy same)
 apply and_congr
 · exact forall_congr' fun p => forall_congr' fun member => holds p (plans p member) same
 · apply forall_congr'; intro e
   apply forall_congr'; intro member
   unfold GeneralNominalVersionedJournal232.Effect.Holds GeneralNominalVersionedJournal232.Effect.Live
   exact and_congr
     (and_congr (effects e member same) (GeneralRebaseRowIrrelevance273.live same e.snapshot _ e.plan))
     (GeneralRebaseRowIrrelevance273.live same s.core _ e.plan)

end Yulang.GeneralRebaseTerminalRowTransfer274
