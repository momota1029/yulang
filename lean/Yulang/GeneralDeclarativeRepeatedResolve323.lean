import Yulang.GeneralDeclarativeRepeatedReads323
import Yulang.GeneralDeclarativeRank321
import Yulang.GeneralDeclarativeGraphRows321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRepeatedResolve323
open GeneralDeclarativeRepeatedSource323
open GeneralDeclarativeRepeatedReads323 (parentNames childNames place probes child_probe parent_ready child_ready
  parent_reads child_reads actual_child)
open GeneralDeclarativeExampleSource320 (interp point)
open GeneralDeclarativeStableRigid323 (Rule Closed Generates stable_sound)
open GeneralDeclarativeRigidLocal323 (RootClosed)
open GeneralDeclarativeEndpointProbe321 (HeadMatches)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativePriority321 (Candidates Recurs Local)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeK2Graph321 (Shape)
open GeneralDeclarativeRank321 (graph_no_cycle)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeEvidence320 (Evidence)
open CommonRoleOutermostResolver (Classify Dictionary Tree All₂)

def level (n : Nat) : Nat := if n ≤ 2 ∨ (10 ≤ n ∧ n ≤ 12) then 1 else 0

theorem monotonic_bound (h : Bound state.normal x y) : level x = level y := by
  induction h with
  | refl => rfl
  | interval registered =>
    change _ ∈ [(0,1),(1,2),(10,11),(11,12)] at registered
    simp only [List.mem_cons,List.not_mem_nil,or_false] at registered
    rcases registered with h|h|h|h <;> cases h <;> rfl
  | constraint impossible => cases impossible
  | trans _ _ l r => exact l.trans r

theorem row_level {a b : Nat} (seen : (⟨a,.variable b⟩ : Equation) ∈ state.equations) : level a = level b := by
  change _ ∈ eqs at seen
  simp only [eqs,List.mem_cons,List.not_mem_nil,or_false] at seen
  rcases seen with h|h|h|h|h|h|h|h <;> cases h <;> rfl

theorem no_cycle : ∀ n, ¬AliasCycle state (observed state) n := by
  apply graph_no_cycle level
  · intro x y known
    induction known with
    | bounds a _ => exact monotonic_bound a
    | forward row => exact row_level row
    | backward row => exact (row_level row).symm
    | trans _ _ a b => exact a.trans b
  · rintro n shape v ⟨term,known,normal⟩ there
    change _ ∈ eqs at known
    simp only [eqs,List.mem_cons,List.not_mem_nil,or_false] at known
    rcases known with h|h|h|h|h|h|h|h <;> cases h
    all_goals cases normal
    all_goals first
      | (cases List.mem_singleton.mp there; decide +kernel)
      | cases there

def tests : Candidates :=
  ⟨HeadMatches (restriction support) registry.constructors interp,
    fun d impl => ¬HeadMatches (restriction support) registry.constructors interp d impl⟩

theorem no_recurs (d) : ¬Recurs state registry interp tests d := by
  rintro (⟨arg,_,cycle⟩|⟨impl,_,i,arg,pat,code,_,_,_,site,_,cycle⟩)
  · exact no_cycle arg.lower cycle
  · exact no_cycle site cycle

theorem parent_only (impl) (vis : impl ∈ registry.declarations) (role : impl.role = goal.role) :
    impl = parent := by
  rcases List.mem_cons.mp vis with same|other
  · exact same
  · cases List.mem_singleton.mp other
    cases role

theorem child_only (impl) (vis : impl ∈ registry.declarations) (role : impl.role = emitted.role) :
    impl = child := by
  rcases List.mem_cons.mp vis with eq|other
  · cases eq
    cases role
  · exact List.mem_singleton.mp other

abbrev chosen := Rule (r := registry) (interp := interp) support tests

theorem root_selected : chosen goal (.selected parent.id [emitted]) := by
  refine .selected parent_ready (no_recurs _) ?_ ⟨⟨List.mem_cons_self,rfl⟩,probes⟩ ?_
    ⟨parentNames,place,actual_child,parent_reads⟩
  · rintro ⟨impl,⟨vis,role⟩,notKnown⟩
    cases parent_only impl vis role
    exact notKnown probes
  · rintro impl ⟨⟨vis,role⟩,_⟩
    rw [parent_only impl vis role]

theorem child_selected : chosen emitted (.selected child.id []) := by
  refine .selected child_ready (no_recurs _) ?_
    ⟨⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩,child_probe⟩ ?_ ⟨childNames,place,rfl,child_reads⟩
  · rintro ⟨impl,⟨vis,role⟩,notKnown⟩
    cases child_only impl vis role
    exact notKnown child_probe
  · rintro impl ⟨⟨vis,role⟩,_⟩
    rw [child_only impl vis role]

abbrev dictionary : Dictionary := .node parent.id [.node child.id []]

theorem selected : Classify chosen goal (.selected dictionary) :=
  ⟨.selected parent.id [.selected child.id []],.selected root_selected (.cons (.selected child_selected .nil) .nil),
    .selected (.cons (.selected .nil (.selected rfl)) .nil) (.selected rfl)⟩

theorem root_batch :
    GeneralDeclarativeEntailment320.BatchRecipe state registry interp goal parent.id [emitted] := by
  rw [← actual_child]
  exact GeneralDeclarativeRigidLocal323.exact_batch checked well_covered List.mem_cons_self rfl
    (fun _ h => False.elim (List.not_mem_nil h)) parent_reads
    (fun _ h => False.elim (List.not_mem_nil h))

theorem child_batch :
    GeneralDeclarativeEntailment320.BatchRecipe state registry interp emitted child.id [] :=
  GeneralDeclarativeRigidLocal323.exact_batch checked well_covered (List.mem_cons_of_mem _ List.mem_cons_self) rfl
    (fun _ h => False.elim (List.not_mem_nil h)) child_reads
    (fun _ h => False.elim (List.not_mem_nil h))

theorem evidence (m) (valid : Models state m) : Evidence registry interp m goal dictionary :=
  .node (GeneralDeclarativeEntailment320.batch_recipe_sound checked root_batch m valid)
    (.cons (.node (GeneralDeclarativeEntailment320.batch_recipe_sound checked child_batch m valid) .nil) .nil)

theorem genuine_repeated_inhabited :
    Classify chosen goal (.selected dictionary) ∧ Models state model ∧ Evidence registry interp model goal dictionary :=
  ⟨selected,fits,evidence model fits⟩

end Yulang.GeneralDeclarativeRepeatedResolve323
