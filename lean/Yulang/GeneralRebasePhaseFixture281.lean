import Yulang.GeneralRebasePhaseMachine281
import Yulang.GeneralRebaseTerminalObservation274

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralRebasePhaseFixture281
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryJournalRefinement228Source (root roles)
open GeneralDictionaryOptionalInitial229 (sourceRegistry registry declaration start)
open GeneralDictionaryVersionedInitialFrame233 (before)
open GeneralDictionaryVersionedPointStage233 (point)
open GeneralDictionaryVersionedSecondInstall233 (installed plan effect)
open GeneralRebasePhaseKeys281 (Codec Key owner Seen Added)
open GeneralRebasePhaseMachine281 (Step)
open GeneralRebaseChartFixtures281 (outputChart)
open GeneralRebaseChartStep281 (Public Recorded)
open GeneralRebaseMixedCounts277 (Actual)
open GeneralRebaseCompoundSourceTypes273 (PublicSource Body)
open GeneralRebaseTerminalMachine274 (firstBindings pointBindings)

noncomputable abbrev first := GeneralDictionaryVersionedInitialFrame233.installed
abbrev initialPlan := GeneralDictionaryOptionalInstall229.plan

inductive Phase where
  | loose | point
  deriving DecidableEq, Repr

def classify (p : Plan roles) : Option Phase :=
  if owner p = (root.identity,declaration.id) then
    if p.packet.bindings = firstBindings then some .loose
    else if p.packet.bindings = pointBindings then some .point
    else none
  else none

def codec : Codec roles Phase :=
  ⟨[.loose,.point],classify,by intro p q h; cases q <;> simp⟩

theorem initial_code : codec.classify initialPlan = some .loose := by
  change classify initialPlan = some .loose
  unfold classify
  rw [ite_eq_left (show owner initialPlan = (root.identity,declaration.id) from rfl),
      ite_eq_left (show initialPlan.packet.bindings = firstBindings from
        GeneralDictionaryOptionalInstall229.bindings_exact)]

theorem new_code : codec.classify plan = some .point := by
  change classify plan = some .point
  unfold classify
  rw [ite_eq_left (show owner plan = (root.identity,declaration.id) from rfl)]
  rw [GeneralDictionaryVersionedPoint233.bindings_exact]
  rfl

theorem phase_missing : ¬ Seen codec point (owner plan,.point) := by
  rintro ⟨old,recorded,_,got⟩
  change old ∈ [initialPlan] at recorded
  cases List.mem_singleton.mp recorded
  rw [initial_code] at got
  cases got

theorem progress : Added codec point installed :=
  (GeneralRebasePhaseKeys281.fresh_iff (effect := effect) codec).mpr ⟨.point,new_code,phase_missing⟩

theorem retained_service : Step outputChart codec sourceRegistry root point installed :=
  GeneralRebasePhaseMachine281.phase_kept GeneralRebaseChartPointService281.raw_service progress

theorem initial_source : (boundary roles).Initial sourceRegistry root before :=
  ⟨start,GeneralDictionaryOptionalInitial229.initial,rfl⟩

theorem raw_first : Actual sourceRegistry root before first :=
  GeneralNominalVersionedMixedKernel234.old_step GeneralDictionaryVersionedInitialStep233.step

theorem raw_observe : Actual sourceRegistry root first point :=
  GeneralNominalVersionedMixedKernel234.old_step GeneralDictionaryVersionedPointStage233.step

theorem first_fact : GeneralRebaseSemanticChart281.Gain outputChart.facts outputChart.meaning (Public outputChart) before first :=
  ⟨(),List.mem_cons_self,GeneralRebaseChartFixtures281.Compound.before_not_entailed,fun m witnessed =>
    ((GeneralRebaseCompoundSourceTypes273.restricted_exact m).mp
      ((GeneralRebaseTerminalPublic274.first_exact m).mp witnessed)).2⟩

theorem first_kept : Step outputChart codec sourceRegistry root before first :=
  Or.inl (GeneralRebaseChartStep281.semantic_kept raw_first first_fact)

theorem observe_kept : Step outputChart codec sourceRegistry root first point :=
  Or.inl (GeneralRebaseChartStep281.quiet_kept raw_observe rfl)

theorem all_three : B4Target.Steps (Step outputChart codec sourceRegistry root) before installed :=
  .tail (.tail (.tail .refl first_kept) observe_kept) retained_service

theorem accessible : Acc (fun after before => Step outputChart codec sourceRegistry root before after) before :=
  GeneralRebasePhaseMachine281.accessible outputChart codec initial_source

theorem point_key_recorded : Seen codec installed (owner plan,.point) :=
  ⟨plan,List.mem_cons_self,rfl,new_code⟩

end Yulang.GeneralRebasePhaseFixture281
