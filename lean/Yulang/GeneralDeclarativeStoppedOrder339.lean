import Yulang.GeneralDeclarativeStoppedOutput339

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStoppedOrder339
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralSourceState (Output)
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalCenteredHeadOutputs (requests)
open GeneralNominalCenteredHeadMatEffects (Ready)
open GeneralDictionaryAssociatedProvenance (lookup)
open GeneralNominalCenters (Plan)
open GeneralDeclarativeStoppedOutput339 (Receipt ordinary ready_rhs fixed_target append_current)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralStoppedProjectedTrace335 (normalized)
open GeneralStoppedInstallHistory335 (InstalledBetween)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (All₂)
open B4Target (Steps)

/-- Retain the order and duplicates of the actual current alias-class
requests, including any one-sided requests. A missing RHS gives none,
so partial recognition does not masquerade as complete output capture. -/
def compileRequests (plan : Plan roles) : List Output → Option (List Equation)
  | [] => some []
  | first::rest => do
    let body ← lookup roles plan.packet.declaration first.name
    let one ← ordinary plan first body
    return one :: (← compileRequests plan rest)

theorem checked_order {s : State roles} {effect : Effect roles} {items : List Output}
    (within : items ⊆ requests s.core effect.plan.packet.site.occurrence)
    (computed : compileRequests effect.plan items = some rows) :
    All₂ (Receipt s effect) items rows ∧ rows.map Equation.left = items.map Output.target := by
  induction items generalizing rows with
  | nil =>
    have empty : [] = rows := Option.some.inj computed
    cases empty
    exact ⟨.nil,rfl⟩
  | cons o os ih =>
    cases found : lookup roles effect.plan.packet.declaration o.name with
    | none => simp [compileRequests,found] at computed
    | some body =>
      cases made : ordinary effect.plan o body with
      | none => simp [compileRequests,found,made] at computed
      | some row =>
        cases later : compileRequests effect.plan os with
        | none => simp [compileRequests,found,later] at computed
        | some rest =>
          have shape : row::rest = rows := by simpa [compileRequests,found,made,later] using computed
          cases shape
          obtain ⟨good,equal⟩ := ih (fun _ a => within (List.mem_cons_of_mem _ a)) later
          exact ⟨.cons ⟨within List.mem_cons_self,body,found,made⟩ good,
            by rw [List.map_cons,List.map_cons,fixed_target made,equal]⟩

theorem complete_known {s : State roles} {effect : Effect roles}
    (known : Ready s.core effect.plan.packet.site.occurrence effect.plan)
    (within : items ⊆ requests s.core effect.plan.packet.site.occurrence) :
    ∃ rows, compileRequests effect.plan items = some rows := by
  induction items with
  | nil => exact ⟨[],rfl⟩
  | cons o os ih =>
    obtain ⟨r,h⟩ := ready_rhs known (within List.mem_cons_self)
    obtain ⟨b,a,f⟩ := h.authored
    obtain ⟨rest,computed⟩ := ih (fun _ p => within (List.mem_cons_of_mem _ p))
    exact ⟨r::rest,by simp [compileRequests,a,f,computed]⟩

theorem member_authored {s : State roles} {effect : Effect roles}
    (compiled : All₂ (Receipt s effect) items rows) (given : row ∈ rows) :
    ∃ output ∈ items, Receipt s effect output row := by
  induction compiled with
  | nil => cases given
  | cons current _ more =>
    rcases List.mem_cons.mp given with rfl|tail
    · exact ⟨_,List.mem_cons_self,current⟩
    · obtain ⟨output,actual,h⟩ := more tail
      exact ⟨output,List.mem_cons_of_mem _ actual,h⟩

/-- Bridge all currently recognized requests of a genuinely retained
effect, in literal current request order, into the ordinary projection
of an actual raw execution path. Proof of current coverage is separate
from historical readiness and is not inferred from termination. -/
theorem installed_outputs {registry : Registry} {root : Occurrence roles}
    {start final : State roles} {effect : Effect roles}
    (path : Steps (Step registry root) start final) (empty : start.effects = [])
    (retained : effect ∈ final.effects) (lowered : normalized final = some base)
    (ready : Ready final.core effect.plan.packet.site.occurrence effect.plan)
    (m : Assignment) (fit : Models final m) :
    ∃ rows, compileRequests effect.plan (requests final.core effect.plan.packet.site.occurrence) = some rows ∧
      rows.map Equation.left = (requests final.core effect.plan.packet.site.occurrence).map Output.target ∧
      GeneralDeclarativeHead320.Models (appendFacts base rows) m ∧
      InstalledBetween registry root start final effect ∧
      All₂ (Receipt final effect) (requests final.core effect.plan.packet.site.occurrence) rows := by
  obtain ⟨rows,ran⟩ := complete_known ready (fun _ h => h)
  obtain ⟨pos,literal⟩ := checked_order (fun _ h => h) ran
  have filled : ∀ row ∈ rows, ∃ e ∈ final.effects, ∃ output, Receipt final e output row := by
    intro row part
    obtain ⟨out,_,made⟩ := member_authored pos part
    exact ⟨effect,retained,out,made⟩
  have modeled := (append_current path empty lowered filled m fit).1
  exact ⟨rows,ran,literal,modeled,GeneralStoppedInstallHistory335.installed_origin path empty retained,pos⟩

end Yulang.GeneralDeclarativeStoppedOrder339
