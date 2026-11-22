import Yulang.GeneralDeclarativeStoppedProjection340
import Yulang.GeneralDeclarativeStoppedFixture339

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
namespace Yulang.GeneralDeclarativeStoppedCurrent340
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalCenteredHeadOutputs (requests)
open GeneralNominalCenteredHeadMatEffects (Ready)
open GeneralDeclarativeStoppedOrder339 (compileRequests checked_order complete_known member_authored)
open GeneralDeclarativeStoppedOutput339 (Receipt row_present)
open GeneralDeclarativeStoppedProjection340 (View Models project append exact_models append_exact)
open GeneralStoppedProjectedTrace335 (current)
open GeneralStoppedInstallHistory335 (InstalledBetween installed_origin)
open GeneralDeclarativeHead320 (Equation)
open GeneralSourceState (Output)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (All₂)
open B4Target (Steps)

/-- Latest literal rows of a real installed effect, validated in the
very same arbitrary raw model, retaining the interval constraints. -/
theorem ordered_outputs {root : GeneralSourceDictionaries.Occurrence roles}
    {first last : State roles} {effect : Effect roles} (path : Steps (Step registry root) first last)
    (empty : first.effects = []) (present : effect ∈ last.effects)
    (observed : project (current last) = some normalized)
    (ready : Ready last.core effect.plan.packet.site.occurrence effect.plan)
    (m : Assignment) (fit : GeneralNominalVersionedJournal232.Models last m) :
    ∃ rows, compileRequests effect.plan (requests last.core effect.plan.packet.site.occurrence) = some rows ∧
      rows.map Equation.left = (requests last.core effect.plan.packet.site.occurrence).map Output.target ∧
      Models (append normalized rows) m ∧ InstalledBetween registry root first last effect ∧
      All₂ (Receipt last effect) (requests last.core effect.plan.packet.site.occurrence) rows := by
  obtain ⟨rows,got⟩ := complete_known ready (fun _ h => h)
  obtain ⟨each,order⟩ := checked_order (fun _ h => h) got
  have valid := (exact_models _ m observed).mpr fit.1.1
  refine ⟨rows,got,order,(append_exact normalized rows m).mpr ⟨valid,?_⟩,
    installed_origin path empty present,each⟩
  intro row inRows
  obtain ⟨_,_,known⟩ := member_authored each inRows
  exact (row_present present known fit).1

open GeneralDictionaryCompoundFrame238 (installed effect)
open GeneralDictionaryCompoundStep238 (installed_model)
open GeneralDictionaryCompoundVersionedModel238 (extended)
open GeneralDictionaryJournalRefinement228Source (descriptor)
open GeneralDeclarativeStoppedFixture339 (row fixed actual)
open GeneralDeclarativeStoppedIntervals340 (Row rowAt mem_table)

abbrev nonpoint : Row := ⟨0,0,0,[.ty 4 2,.ty 4 2]⟩

theorem nonpoint_slot : (current installed).nominals ⟨0,by decide⟩ = some (descriptor (4,2)) := rfl

theorem nonpoint_table : nonpoint ∈ GeneralDeclarativeStoppedIntervals340.table (current installed) :=
  (mem_table _ _).mpr ⟨⟨0,by decide⟩,_,nonpoint_slot,rfl⟩

noncomputable abbrev fixtureView : View :=
  ⟨⟨GeneralStoppedLower335.normal (current installed),[⟨2,.primitive .emptyRecord []⟩]⟩,
    GeneralDeclarativeStoppedIntervals340.table (current installed)⟩

theorem fixture_projected : project (current installed) = some fixtureView := rfl

/-- Exact nonpoint fixture including its previously blocked interval
and its actual associated target 4. This is one install, not an
assertion that the raw fixture was a successful terminal run. -/
theorem fixture_output {m : Assignment} (fit : GeneralNominalVersionedJournal232.Models installed m) :
    Models (append fixtureView [row]) m ∧ nonpoint ∈ fixtureView.intervals ∧ row.left = 4 := by
  have now := (exact_models _ m fixture_projected).mpr fit.1.1
  have e : effect ∈ installed.effects := List.mem_cons_self
  obtain ⟨valid,target⟩ := row_present e actual fit
  refine ⟨(append_exact fixtureView [row] m).mpr ⟨now,?_⟩,nonpoint_table,target⟩
  intro r inRows
  rcases List.mem_singleton.mp inRows with rfl
  exact valid

theorem fixture_nonvacuous : Models (append fixtureView [row]) extended :=
  (fixture_output installed_model).1

end Yulang.GeneralDeclarativeStoppedCurrent340
