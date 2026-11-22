import Yulang.GeneralDeclarativeWitnessClassify334

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessCorrespond334
open GeneralDeclarations (Registry Declaration Checked)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeInlineEndpoint331 (candidates)
open GeneralDeclarativeWitnessNode334 (Witness Generation)
open GeneralDeclarativeWitnessClassify334 (Rule selected_witness selected_to_old)
open GeneralDeclarativeCurrentReceipt330 (Staged complete)
open GeneralDeclarativeUnfinishedRoot330 (Local59 selected_old_exact)
open GeneralDeclarativeStableAttempt329 (Elected)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralNominalInspection (Interpretation)
open CommonRoleOutermostResolver (Frontier Tree Dictionary Classify Resolves Summarizes All₂ Result)

abbrev Legacy {s : State} (p : Supported s done) (r : Registry) (i : Interpretation)
    (waiting : Demand → Declaration → Prop) :=
  Local59 s r i p (candidates p r i waiting) (Staged s r i)

theorem old_choice {s : State} {p : Supported s done} (v : Legacy p r i waiting d (.selected key kids)) :
    ∃ impl : Declaration, impl.id = key ∧
      Elected s r i p (candidates p r i waiting) d impl ∧ Staged s r i d impl kids := by
  cases selected_old_exact.mp v with
  | selected readable safe clear matched unique emits =>
    exact ⟨_,rfl,⟨readable,safe,clear,matched,unique⟩,emits⟩

/-- Open reverse correspondence in a factored form. An old staged
ordinary frame must be backed by independent supported observations
and an exact present readback. This does not assume a new verdict
or mention its semantics. -/
def Realized {s : State} (p : Supported s done) (r : Registry) (i : Interpretation)
    (waiting : Demand → Declaration → Prop) : Prop :=
  ∀ d impl kids, Declared r d →
    Elected s r i p (candidates p r i waiting) d impl →
    Staged s r i d impl kids → Nonempty (Generation p r i d impl kids)

theorem old_to_selected {s : State} {p : Supported s done}
    (already : Realized p r i waiting) (declared : Declared r d)
    (old : Legacy p r i waiting d (.selected key kids)) :
    Rule p r i waiting d (.selected key kids) := by
  obtain ⟨impl,keyOf,guard,wrote⟩ := old_choice old
  obtain ⟨g⟩ := already d impl kids declared guard wrote
  rw [← keyOf]
  exact .selected ⟨g,guard⟩

def SelectedMap (r : Registry) (old new : Demand → Frontier Demand → Prop) : Prop :=
  ∀ d, Declared r d → ∀ key kids, old d (.selected key kids) →
    new d (.selected key kids) ∧ ∀ child ∈ kids, Declared r child

section
variable {r : Registry} {old new : Demand → Frontier Demand → Prop}
mutual
theorem maps_selected (f : SelectedMap r old new) (requested : Declared r d)
    (diag : Tree) (dict : Dictionary) (seen : Resolves old d diag)
    (summed : Summarizes diag (.selected dict)) : Resolves new d diag := by
  cases seen with
  | pending _ => cases summed
  | rejected _ => cases summed
  | ambiguous _ => cases summed
  | selected chosen each =>
    obtain ⟨now,all⟩ := f _ requested _ _ chosen
    cases summed with
    | selected eachSummary combined =>
      cases combined with
      | selected children =>
        subst_vars
        exact .selected now (maps_children f all _ _ each eachSummary)
termination_by sizeOf diag

theorem maps_children (f : SelectedMap r old new) (requested : ∀ d ∈ ds, Declared r d)
    (diags : List Tree) (dicts : List Dictionary) (seen : All₂ (Resolves old) ds diags)
    (summed : All₂ Summarizes diags (dicts.map Result.selected)) : All₂ (Resolves new) ds diags := by
  cases dicts with
  | nil => cases summed; cases seen; exact .nil
  | cons one rest =>
    cases summed with
    | cons success tail =>
      cases seen with
      | cons resolved later =>
        exact .cons (maps_selected f (requested _ List.mem_cons_self) _ _ resolved success)
          (maps_children f (fun d found => requested d (List.mem_cons_of_mem _ found)) _ _ later tail)
termination_by sizeOf diags
end
end

theorem forward {s : State} {p : Supported s done} (checked : Checked r) (cover : Coverage r i) :
    SelectedMap r (Rule p r i waiting) (Legacy p r i waiting) := by
  intro d requested key kids chosen
  obtain ⟨impl,_,⟨w⟩⟩ := selected_witness chosen
  obtain ⟨frame,_,_,_⟩ := w.frame checked cover requested
  exact ⟨selected_to_old checked cover requested chosen,
    (complete checked cover w.chosen.viable.1.1 w.chosen.viable.1.2 requested frame w.receipt).2.2⟩

theorem backward {s : State} {p : Supported s done} (checked : Checked r) (cover : Coverage r i)
    (realizes : Realized p r i waiting) : SelectedMap r (Legacy p r i waiting) (Rule p r i waiting) := by
  intro d requested key kids fromOld
  obtain ⟨impl,_,choice,prior,⟨staged⟩,receipt⟩ := old_choice fromOld
  exact ⟨old_to_selected realizes requested fromOld,
    (complete checked cover choice.viable.1.1 choice.viable.1.2 requested staged receipt).2.2⟩

theorem classify_to_old {s : State} {p : Supported s done} (checked : Checked r) (cover : Coverage r i)
    (requested : Declared r d) (new : Classify (Rule p r i waiting) d (.selected dict)) :
    Classify (Legacy p r i waiting) d (.selected dict) := by
  obtain ⟨diag,steps,summary⟩ := new
  exact ⟨diag,maps_selected (forward checked cover) requested diag dict steps summary,summary⟩

theorem classify_from_old {s : State} {p : Supported s done} (checked : Checked r) (cover : Coverage r i)
    (realizes : Realized p r i waiting) (requested : Declared r d)
    (old : Classify (Legacy p r i waiting) d (.selected dict)) :
    Classify (Rule p r i waiting) d (.selected dict) := by
  obtain ⟨diag,steps,summary⟩ := old
  exact ⟨diag,maps_selected (backward checked cover realizes) requested diag dict steps summary,summary⟩

end Yulang.GeneralDeclarativeWitnessCorrespond334
