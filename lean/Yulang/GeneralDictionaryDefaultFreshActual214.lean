import Yulang.GeneralDictionaryDefault214ActualJournal
import Yulang.GeneralDictionaryDefaultEvidenceSplit212
import Yulang.GeneralNominalBinderIdentity181

/-! Actual-source overlap forces a historical invocation with the same key.
This uses corrected208 traces and does not cast to a legacy boundary. -/
namespace Yulang.GeneralDictionaryDefaultFreshActual214
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralDictionaryDefaultDepth208 (InstalledDepthBound)
open GeneralDictionaryDefault214ActualReadback (Actual)
open GeneralDictionaryDefault214ActualSupport (registered_packets)
open GeneralDictionaryDefaultEvidenceSplit212 (HistoricalInvocation)
variable {roles : Roles.RoleDecls}

theorem binder_identity
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (plan : Plan roles) (registered : plan ∈ state.core.plans) (name : Nat)
    (equal : plan.binder name = fresh context.state.seed invocation declaration 8 owner position) :
    name = owner ∧ position = 0 ∧
    plan.packet.site.occurrence.identity = invocation ∧ plan.packet.declaration.id = declaration ∧
    name ∉ plan.packet.declaration.outputNames ∧
    ((GeneralNominalPacketSupport.capture plan.packet).inputs name).1 ≠
      ((GeneralNominalPacketSupport.capture plan.packet).inputs name).2 := by
  have separate := GeneralDictionaryDefaultRawSeparation213.historical_capture_separate
    (invocation := invocation) (declaration := declaration) (owner := owner) (position := position)
    source bound path plan.packet (registered_packets path plan registered) (by decide : 7 ≤ 8) name
  have notOutput : name ∉ plan.packet.declaration.outputNames := by
    intro output
    have value : plan.binder name = (GeneralNominalPacketSupport.capture plan.packet).outputs name := by
      simp only [Plan.binder,output,ite_true]
    exact separate.1 (equal.symm.trans value)
  have nonpoint : ((GeneralNominalPacketSupport.capture plan.packet).inputs name).1 ≠
      ((GeneralNominalPacketSupport.capture plan.packet).inputs name).2 := by
    intro point
    have value : plan.binder name = ((GeneralNominalPacketSupport.capture plan.packet).inputs name).1 := by
      simp only [Plan.binder,notOutput,ite_false,point,ite_true]
    exact separate.2.1 (equal.symm.trans value)
  rw [GeneralNominalBinderIdentity181.binder_fresh plan name notOutput nonpoint,
    GeneralDictionaryDefault214ActualSites.plan_seed path plan registered] at equal
  have identities := (GeneralNominalCenteredAllocation.fresh_identity context.state.seed
    (plan.packet.site.occurrence.identity,plan.packet.declaration.id,8,name,0)
    (invocation,declaration,8,owner,position)).mp equal
  simp only [Prod.mk.injEq,true_and] at identities
  exact ⟨identities.2.2.1,identities.2.2.2.symm,identities.1,identities.2.1,notOutput,nonpoint⟩

theorem actual_historical
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (actual : Actual state (fresh context.state.seed focus.identity key 8 owner position) origin) :
    HistoricalInvocation state focus key := by
  obtain ⟨plan,registered,entry,_,_,same,_⟩ := actual
  have identity := binder_identity source bound path plan registered entry.name same
  exact ⟨plan,registered,identity.2.2.1,identity.2.2.2.1⟩

theorem fresh_not_actual
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (fresh : ¬ HistoricalInvocation state focus key) :
    ¬ Actual state (GeneralNominalCenters.fresh context.state.seed focus.identity key 8 owner position) origin :=
  fun actual => fresh (actual_historical source bound path actual)
end Yulang.GeneralDictionaryDefaultFreshActual214

namespace Yulang.GeneralDictionaryDefaultFreshActual214
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralDictionaryDefaultDepth208 (InstalledDepthBound)
open GeneralDictionaryDefaultEvidenceSplit212 (HistoricalInvocation)
variable {roles : Roles.RoleDecls}

/-- Purpose-eight candidate binders cannot be read by any registered site's
actual input or any existing snapshot/live effect before this invocation/key
has been installed. Packet child schemas are not included in this conclusion. -/
theorem fresh_site_effect_separate
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (unrecorded : ¬ HistoricalInvocation state focus key) :
    (∀ site ∈ state.core.sites,
      fresh context.state.seed focus.identity key 8 owner position ∉ GeneralNominalCenteredFrame179.siteSources site) ∧
    (∀ effect ∈ state.effects,
      fresh context.state.seed focus.identity key 8 owner position ∉
        GeneralDictionaryDefault214ActualJournal.effectSources state effect) := by
  constructor
  · intro site registered member
    obtain ⟨origin,actual⟩ := GeneralDictionaryDefault214ActualSupport.site_support_actual source bound path site registered member
    exact fresh_not_actual source bound path unrecorded actual
  · intro effect registered member
    obtain ⟨origin,actual⟩ := GeneralDictionaryDefault214ActualJournal.effect_support_actual source bound path effect registered member
    exact fresh_not_actual source bound path unrecorded actual

theorem fresh_capture_head_separate
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (unrecorded : ¬ HistoricalInvocation state focus key)
    (plan : Plan roles) (registered : plan ∈ state.core.plans) :
    fresh context.state.seed focus.identity key 8 owner position ∉
      GeneralNominalCenteredFrame179.captureSources plan ∧
    fresh context.state.seed focus.identity key 8 owner position ∉
      GeneralNominalHeadLedgerFrame182.headSources plan := by
  constructor
  · intro member
    obtain ⟨origin,actual⟩ := GeneralDictionaryDefault214ActualSupport.capture_support_actual source bound path plan registered member
    exact fresh_not_actual source bound path unrecorded actual
  · intro member
    obtain ⟨origin,actual⟩ := GeneralDictionaryDefault214ActualJournal.head_support_actual source bound path plan registered member
    exact fresh_not_actual source bound path unrecorded actual
end Yulang.GeneralDictionaryDefaultFreshActual214
