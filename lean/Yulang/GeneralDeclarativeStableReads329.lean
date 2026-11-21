import Yulang.GeneralDeclarativeStableTies329
import Yulang.GeneralDeclarativeSourceNames321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStableReads329
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarationPatterns (Constructors Pattern normalize variablesArgs normalizeArgs)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarativeTraceNames321 (names)
open GeneralDeclarativeOpaqueNested328 (occurrences)
open GeneralDeclarativeTermWalk322 (Walk)
open GeneralDeclarativeTermOccurrences322 (actual_positions)
open GeneralDeclarativeEqualities322 (Derives entails)
open GeneralDeclarativeGrowth327 (Extends facts derives)
open GeneralDeclarativeStableTies329 (pairOf Present Consequence rows repeated_binds used_after)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeEntailment320 (appendFacts conservative_append)
open GeneralDeclarativeNFHead324 (fact)
open CommonRoleOutermostResolver (All₂)

structure One (s : State) (c : Constructors) (i : Interpretation) (arg : Capture)
    (p : Pattern) (spans : List (Nat × Capture)) : Prop where
  fits : Bounds s arg
  actual : ∃ code form, translate c i (normalize p) = some code ∧
    Derives s (.variable arg.center) form ∧ Walk .actual form code (occurrences spans)

inductive Heads (s : State) (c : Constructors) (i : Interpretation) :
    List Capture → List Pattern → List (Nat × Capture) → Prop where
  | nil : Heads s c i [] [] []
  | cons : One s c i a p first → Heads s c i as ps rest →
    Heads s c i (a :: as) (p :: ps) (first ++ rest)

theorem names_one {s : State} (x : One s c i a p spans) :
    spans.map Prod.fst = (normalize p).variables := by
  obtain ⟨code,_,printed,_,walk⟩ := x.actual
  have uses := (actual_positions walk).1
  rw [GeneralDeclarativeSourceNames321.actual_names _ printed] at uses
  simpa only [occurrences,List.map_map,Function.comp_def] using uses

theorem names_all {s : State} (h : Heads s c i as ps spans) :
    spans.map Prod.fst = variablesArgs (normalizeArgs ps) := by
  induction h with
  | nil => rfl
  | cons first _ other =>
    simp only [normalizeArgs,variablesArgs,List.map_append,names_one first,other]

theorem weakened {a b : State} (g : Extends a b) (read : Heads a c i xs ps all) :
    Heads b c i xs ps all := by
  induction read with
  | nil => exact .nil
  | cons first _ others =>
    obtain ⟨u,v,print,actual,walk⟩ := first.actual
    exact .cons ⟨GeneralDeclarativeGrowth327.fits g first.fits,u,v,print,derives g actual,walk⟩ others

theorem present_subset {s : State} (all : Present s selected xs) (sub : ys ⊆ xs) :
    Present s selected ys := by
  intro eq seen
  obtain ⟨u,chosen,rfl⟩ := List.mem_map.mp seen
  obtain ⟨source,diff⟩ := List.mem_filter.mp chosen
  exact all (List.mem_map.mpr ⟨u,List.mem_filter.mpr ⟨sub source,diff⟩,rfl⟩)

theorem literal_head {s : State} (walk : Heads s c i as ps spans)
    (closed : Present s selected (spans.map pairOf)) :
    All₂ (fun a p => Bounds s a ∧ Result s (fact c i selected a p)) as ps := by
  induction walk with
  | nil => exact .nil
  | @cons a p first as ps rest here more ih =>
    obtain ⟨code,form,printed,read,walk⟩ := here.actual
    rw [List.map_append] at closed
    exact .cons ⟨here.fits,GeneralDeclarativeForwardHead325.by_walk printed (entails read)
      walk (repeated_binds (present_subset closed (fun _ h => List.mem_append_left _ h)))⟩
      (ih (present_subset closed (fun _ h => List.mem_append_right _ h)))

theorem transport_models {s t : State}
    (ranges : ∀ a ∈ as, Bounds s a) (models : ∀ m, Models s m → Models t m)
    (holds : All₂ (fun a p => Bounds t a ∧ Result t (fact c i selected a p)) as ps) :
    All₂ (fun a p => Bounds s a ∧ Result s (fact c i selected a p)) as ps := by
  induction holds with
  | nil => exact .nil
  | cons first rest ih =>
    obtain ⟨batch,printed,every⟩ := first.2
    exact .cons ⟨ranges _ List.mem_cons_self,batch,printed,
      fun f inList m valid => every f inList m (models m valid)⟩
      (ih fun a h => ranges a (List.mem_cons_of_mem _ h))

theorem ranges {s : State} (read : Heads s c i as ps spans) :
    ∀ a ∈ as, Bounds s a := by
  induction read with
  | nil => intro _ h; cases h
  | cons here _ rest =>
    intro a found
    rcases List.mem_cons.mp found with rfl|after
    · exact here.fits
    · exact rest a after

/-- Derived or explicit ordinary selected ties suffice. If proving a
derived tie via a temporary explicit row, the set of models is the
same and the returned head judgment stays in the actual current state. -/
theorem head {s : State} (walk : Heads s c i as ps spans)
    (closed : Consequence s selected (spans.map pairOf)) :
    All₂ (fun a p => Bounds s a ∧ Result s (fact c i selected a p)) as ps :=
  transport_models (ranges walk) (fun m fit => (conservative_append closed m).mpr fit)
    (literal_head (weakened (facts s (rows selected (spans.map pairOf))) walk)
      (used_after selected (spans.map pairOf)))

end Yulang.GeneralDeclarativeStableReads329
