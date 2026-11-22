import Yulang.GeneralDeclarativeStoppedOrder339

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStoppedOrigins339
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeOrigins321 (Supported restriction Backed backed_iff Available)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (Effect Models)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalCenteredHeadOutputs (requests)
open GeneralNominalCenteredHeadMatEffects (Ready)
open GeneralStoppedProjectedTrace335 (normalized)
open GeneralStoppedInstallHistory335 (InstalledBetween)
open GeneralDeclarativeStoppedOutput339 (Receipt)
open GeneralDeclarativeStoppedOrder339 (compileRequests installed_outputs)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (All₂)
open B4Target (Steps)

/-- Preserve old source support. A new row carrying an installed
effect's genuine owner is an *output* origin, never unconditionally
an input origin or a claim that the owner has completed. -/
def attach {base : State} (p : Supported base done) (owner : Nat) (rows : List Equation) :
    Supported (appendFacts base rows) done where
  derivesFrom e o := p.derivesFrom e o ∨ e ∈ rows ∧ o = .output owner
  ordinary := by
    intro e o origin
    rcases origin with old|⟨added,_⟩
    · exact List.mem_append_left _ (p.ordinary old)
    · exact List.mem_append_right _ added

theorem backed_output {base : State} {p : Supported base done} :
    row ∈ (restriction (attach p owner rows)).equations ↔
      row ∈ (restriction p).equations ∨ row ∈ rows ∧ done owner := by
  rw [backed_iff,backed_iff]
  constructor
  · rintro ⟨origin,source,available⟩
    rcases source with old|⟨given,rfl⟩
    · exact .inl ⟨origin,old,available⟩
    · cases available with
      | completed known => exact .inr ⟨given,known⟩
  · rintro (⟨origin,old,available⟩|⟨new,known⟩)
    · exact ⟨origin,.inl old,available⟩
    · exact ⟨.output owner,.inr ⟨new,rfl⟩,.completed known⟩

theorem pending_no_gain {base : State} {p : Supported base done}
    (pending : ¬done owner) :
    row ∈ (restriction (attach p owner rows)).equations ↔ row ∈ (restriction p).equations := by
  rw [backed_output]
  exact ⟨fun offered => offered.elim id (fun pair => (pending pair.2).elim),Or.inl⟩

theorem actual_outputs {roles : Roles.RoleDecls} {root : Occurrence roles}
    {start final : GeneralNominalVersionedJournal232.State roles} {effect : Effect roles}
    {base : State} (prior : Supported base done)
    (path : Steps (Step registry root) start final) (empty : start.effects = [])
    (retained : effect ∈ final.effects) (lowered : normalized final = some base)
    (known : Ready final.core effect.plan.packet.site.occurrence effect.plan)
    (m : Assignment) (fit : Models final m) :
    ∃ rows,
      compileRequests effect.plan (requests final.core effect.plan.packet.site.occurrence) = some rows ∧
      GeneralDeclarativeHead320.Models (appendFacts base rows) m ∧
      InstalledBetween registry root start final effect ∧
      ∀ row, row ∈ (restriction (attach prior effect.plan.packet.site.occurrence.identity rows)).equations ↔
        row ∈ (restriction prior).equations ∨
          row ∈ rows ∧ done effect.plan.packet.site.occurrence.identity := by
  obtain ⟨rows,there,_,valid,origin,_⟩ := installed_outputs path empty retained lowered known m fit
  exact ⟨rows,there,valid,origin,fun _ => backed_output⟩

end Yulang.GeneralDeclarativeStoppedOrigins339
