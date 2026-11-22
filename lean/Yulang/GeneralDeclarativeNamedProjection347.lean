import Yulang.GeneralDeclarativeNamedOrdinary347
import Yulang.GeneralDeclarativeCurrentBodies345
import Yulang.GeneralDeclarativeNativeWhere347

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNamedProjection347
open GeneralNominalState (State)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeNamedOrdinary347 (ordinary ordinary_exact)
open GeneralDeclarativeNamedTable347 (Entry table exact_nominals)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeEntailment320 (appendFacts model_append Holds)
open GeneralDeclarativeCurrentJoint345 (Block)
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open CommonRoleOutermostResolver (All₂)

structure View where
  ordinary : GeneralDeclarativeWhere319.State
  descriptors : List Entry

def View.Models (view : View) (m : Assignment) : Prop :=
  GeneralDeclarativeWhere319.Models view.ordinary m ∧ ∀ e ∈ view.descriptors, e.Holds m

def project (s : State) : View := ⟨ordinary s,table s⟩

/-- A total, name-based ordinary model projection with a typed side
table for real nominal ranges. It forgets physical allocation,
versions and occurrences, but preserves raw type/row models exactly.
It does not authorize any ordinary equation for input selection. -/
theorem preserves_models (s : State) (m : Assignment) :
    (project s).Models m ↔ GeneralNominalState.Models s m := by
  change (GeneralDeclarativeWhere319.Models (ordinary s) m ∧ ∀ e ∈ table s,e.Holds m) ↔ _
  rw [ordinary_exact,exact_nominals]
  exact ⟨fun ⟨⟨a,b⟩,c⟩ => ⟨a,c,b⟩,fun ⟨a,b,c⟩ => ⟨⟨a,c⟩,b⟩⟩

def base (s : State) : GeneralDeclarativeHead320.State := ⟨(project s).ordinary,[]⟩

theorem ordinary_holds (s : State) (m : Assignment) (fit : GeneralNominalState.Models s m) :
    GeneralDeclarativeHead320.Models (base s) m := by
  exact ⟨((preserves_models s m).mpr fit).1,fun _ h => False.elim (List.not_mem_nil h)⟩

open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralDeclarativeNativeWhere347 (layout)

/-- The total ordinary projection and the full named nonpoint side
table coexist with all genuinely completed associated output rows in
one arbitrary final native model; no old point-only printer or new
where producer is assumed. -/
theorem current_completed {rs : Roles.RoleDecls} {r : Registry} {root : Occurrence rs}
    {last : GeneralNominalVersionedJournal232.State rs}
    (ok : (boundary rs).Checked r) (run : Reachable r root last)
    (m : Assignment) (fit : GeneralNominalVersionedJournal232.Models last m) :
    ∃ blocks, All₂ (Block r root last) last.effects blocks ∧
      GeneralDeclarativeHead320.Models (appendFacts (base (layout last)) blocks.flatten) m ∧
      (project (layout last)).Models m := by
  have exactRaw : GeneralNominalState.Models (layout last) m := fit.1.1
  obtain ⟨blocks,rows,live⟩ := GeneralDeclarativeCurrentBodies345.attach_any_base
    ok run m fit (ordinary_holds _ m exactRaw)
  exact ⟨blocks,rows,live,(preserves_models _ _).mpr exactRaw⟩

end Yulang.GeneralDeclarativeNamedProjection347
