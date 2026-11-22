import Yulang.GeneralDeclarativeWitnessCorrespond334

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessStopped334
open GeneralDeclarations (Registry Declaration Checked)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeWitnessNode334 (Witness Generation)
open GeneralDeclarativeWitnessClassify334 (Rule dictionary_sound)
open GeneralDeclarativeWitnessCorrespond334 (Legacy old_choice)
open GeneralDeclarativeCurrentReceipt330 (complete)
open CommonRoleOutermostResolver (All₂ Tree Dictionary Resolves Summarizes Result Classify)

/-- Successful-stop receipt interface: only nodes actually retained
in this finite ordered result need a current generation receipt.
The old selected report must match that node literally. No global
coverage assertion about other frontier outcomes is needed. -/
inductive Retained {s : State} (p : Supported s done) (r : Registry) (i : Interpretation)
    (waiting : Demand → Declaration → Prop) : Demand → Tree → Prop
  | node : Generation p r i d impl kids → impl ∈ r.declarations →
      Legacy p r i waiting d (.selected impl.id kids) →
      All₂ (Retained p r i waiting) kids children →
      Retained p r i waiting d (.selected impl.id children)

section
variable {s : State} {p : Supported s done} {r : Registry} {i : Interpretation}
variable {waiting : Demand → Declaration → Prop}

/-- Actual checked declarations with that key coincide, independent
of which compiler observation or receipt produced the output. -/
theorem same_key_of_visible (checked : Checked r) (a b : Declaration)
    (av : a ∈ r.declarations) (bv : b ∈ r.declarations) (id : a.id = b.id) : a = b := by
  have claim (ds : List Declaration) (unique : (ds.map Declaration.id).Nodup)
      (av : a ∈ ds) (bv : b ∈ ds) : a = b := by
    induction ds with
    | nil => cases av
    | cons head rest ih =>
      have h := List.nodup_cons.mp (show (head.id :: rest.map Declaration.id).Nodup from unique)
      rcases List.mem_cons.mp av with eqA | aRest <;> rcases List.mem_cons.mp bv with eqB | bRest
      · exact eqA.trans eqB.symm
      · subst a
        exact (h.1 (id.symm ▸ List.mem_map_of_mem bRest)).elim
      · subst b
        exact (h.1 (id ▸ List.mem_map_of_mem aRest)).elim
      · exact ih h.2 aRest bRest
  exact claim _ checked.1 av bv

mutual
theorem resolves (checked : Checked r) (coverage : Coverage r i)
    (d : Demand) (tree : Tree) (declared : Declared r d)
    (kept : Retained p r i waiting d tree) : Resolves (Rule p r i waiting) d tree := by
  cases kept with
  | node saved visible old each =>
    obtain ⟨other,id,guard,_⟩ := old_choice old
    have eq := same_key_of_visible checked _ _ guard.viable.1.1 visible id
    subst other
    have now : Witness p r i waiting _ _ _ := ⟨saved,guard⟩
    obtain ⟨frame,_,_,_⟩ := now.frame checked coverage declared
    have all := (complete checked coverage guard.viable.1.1 guard.viable.1.2 declared frame now.receipt).2.2
    exact .selected (.selected now) (resolves_children checked coverage _ _ all each)
termination_by sizeOf tree
theorem resolves_children (checked : Checked r) (coverage : Coverage r i)
    (kids : List Demand) (trees : List Tree) (declared : ∀ d ∈ kids, Declared r d)
    (kept : All₂ (Retained p r i waiting) kids trees) :
    All₂ (Resolves (Rule p r i waiting)) kids trees := by
  cases kept with
  | nil => exact .nil
  | cons here tail =>
    exact .cons (resolves checked coverage _ _ (declared _ List.mem_cons_self) here)
      (resolves_children checked coverage _ _ (fun _ h => declared _ (List.mem_cons_of_mem _ h)) tail)
termination_by sizeOf trees
end

theorem selected_receipt (checked : Checked r) (coverage : Coverage r i) (declared : Declared r d)
    (kept : Retained p r i waiting d tree) (output : Summarizes tree (.selected dict)) :
    Classify (Rule p r i waiting) d (.selected dict) ∧
      ∀ m, Models s m → Evidence r i m d dict := by
  have replay : Classify (Rule p r i waiting) d (.selected dict) :=
    ⟨tree,resolves checked coverage d tree declared kept,output⟩
  exact ⟨replay,dictionary_sound checked coverage declared replay⟩

/- Conversely every actually witnessed successful tree yields its
own finite old reports and ordinary receipts. This stays local to
the visited occurrences, unlike the disproved global converse. -/
mutual
theorem retain_selected (checked : Checked r) (cover : Coverage r i)
    (d : Demand) (tree : Tree) (dict : Dictionary) (declared : Declared r d)
    (now : Resolves (Rule p r i waiting) d tree)
    (summary : Summarizes tree (.selected dict)) : Retained p r i waiting d tree := by
  cases now with
  | pending _ => cases summary
  | ambiguous _ => cases summary
  | rejected _ => cases summary
  | selected here each =>
    obtain ⟨impl,id,⟨w⟩⟩ := GeneralDeclarativeWitnessClassify334.selected_witness here
    subst_vars
    obtain ⟨frame,_,_,_⟩ := w.frame checked cover declared
    have all := (complete checked cover w.chosen.viable.1.1 w.chosen.viable.1.2 declared frame w.receipt).2.2
    cases summary with
    | selected subtotals combined =>
      cases combined with
      | selected _ =>
        subst_vars
        exact .node w.toGeneration w.chosen.viable.1.1
          (GeneralDeclarativeWitnessClassify334.selected_to_old checked cover declared here)
          (retain_children checked cover _ _ _ all each subtotals)
termination_by sizeOf tree

theorem retain_children (checked : Checked r) (cover : Coverage r i)
    (kids : List Demand) (children : List Tree) (dicts : List Dictionary)
    (declared : ∀ d ∈ kids, Declared r d)
    (now : All₂ (Resolves (Rule p r i waiting)) kids children)
    (summary : All₂ Summarizes children (dicts.map Result.selected)) :
    All₂ (Retained p r i waiting) kids children := by
  cases dicts with
  | nil => cases summary; cases now; exact .nil
  | cons here rest =>
    cases summary with
    | cons one tail =>
      cases now with
      | cons chosen each =>
        exact .cons (retain_selected checked cover _ _ _ (declared _ List.mem_cons_self) chosen one)
          (retain_children checked cover _ _ _ (fun _ h => declared _ (List.mem_cons_of_mem _ h)) each tail)
termination_by sizeOf children
end

theorem selected_iff_retained (checked : Checked r) (cover : Coverage r i)
    (declared : Declared r d) :
    Classify (Rule p r i waiting) d (.selected dict) ↔
      ∃ tree, Retained p r i waiting d tree ∧ Summarizes tree (.selected dict) := by
  constructor
  · rintro ⟨tree,seen,summary⟩
    exact ⟨tree,retain_selected checked cover d tree dict declared seen summary,summary⟩
  · rintro ⟨tree,keep,summary⟩
    exact (selected_receipt checked cover declared keep summary).1

end
end Yulang.GeneralDeclarativeWitnessStopped334
