import Yulang.GeneralDeclarativeAliasAuthority327

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeAliasStatus327
open GeneralDeclarativeAliasAuthority327
open GeneralDeclarativeHead320 (Equation Models)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeExampleSource320 (point leaf leaf_checked)
open GeneralDeclarations (Checked)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeGraphRows321 (observed structural shapeOf)
open GeneralDeclarativeK2Graph321 (Descends Shape)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativePriority321 (Candidates Recurs)
open GeneralDeclarativeEndpointProbe321 (HeadMatches)
open GeneralDeclarativeProjectedFrame326 (Rule Frame sound)
open GeneralDeclarativeEmissionForest322 (Placement)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativePlacementEquiv327 (RequestSame)
open CommonRoleOutermostResolver (Classify Dictionary)

theorem checked : Checked reg := by
  refine ⟨by decide +kernel,?_⟩
  intro d inside
  cases List.mem_singleton.mp inside
  exact leaf_checked

theorem no_edges (a b : Nat) :
    ¬ Descends (structural state) a b := by
  rintro ⟨shape,⟨owner,linked,code,row,seen⟩,child⟩
  change (⟨owner,code⟩ : Equation) ∈ rows at row
  simp only [rows,List.mem_cons,List.not_mem_nil,or_false] at row
  rcases row with h|h|h|h <;> have p := congrArg Equation.right h <;> cases p
  all_goals cases seen
  exact List.not_mem_nil child

theorem no_cycles (a : Nat) : ¬AliasCycle state (observed state) a := by
  rintro ⟨descendant,last,seen,_,_⟩
  exact no_edges a descendant seen

def tests (done : Nat → Prop) : Candidates :=
  ⟨HeadMatches (restriction (support done)) reg.constructors interp,
    fun d l => ¬HeadMatches (restriction (support done)) reg.constructors interp d l⟩

theorem acyclic (done : Nat → Prop) (d : Demand) : ¬Recurs state reg interp (tests done) d := by
  rintro (⟨arg,_,cycle⟩|⟨_,_,_,_,_,_,_,_,_,spot,_,cycle⟩)
  · exact no_cycles arg.lower cycle
  · exact no_cycles spot cycle

abbrev dict : Dictionary := .node leaf.id []
abbrev branch (done : Nat → Prop) := Rule state reg interp (support done) (tests done)
abbrev place : Placement := ⟨fun _ _ => point 0,fun _ _ => 5⟩
abbrev run (n : Nat) : Demand := ⟨2,[point n],[⟨1,5⟩]⟩
abbrev written (n : Nat) : Equation := ⟨5,.variable n⟩

theorem probe (n : Nat) (done : Nat → Prop) :
    HeadMatches (restriction (support done)) reg.constructors interp (run n) leaf :=
  .cons ⟨⟨.refl _,.refl _⟩,.variable 0,[⟨0,.lower,n⟩],[⟨0,.upper,n⟩],rfl,.capture,.capture⟩ .nil

theorem source_frame (n : Nat) (done : Nat → Prop) (present : written n ∈ rows) :
    Frame state reg interp (support done) (run n) leaf (fun _ => point n) place := by
  refine ⟨.cons ⟨⟨.refl _,.refl _⟩,.ordinary (.actual rfl .capture ?_)⟩ .nil,
    fun _ _ => ⟨.refl _,.refl _⟩,fun _ absent => False.elim (List.not_mem_nil absent),[written n],rfl,?_⟩
  · intro use found
    cases List.mem_singleton.mp found
    exact .refl _
  · intro row found
    cases List.mem_singleton.mp found
    exact present

theorem can_select (n : Nat) (done : Nat → Prop)
    (allowed : GeneralDeclarativeLowerKnown321.Ready (support done) (run n))
    (present : written n ∈ rows) : Classify (branch done) (run n) (.selected dict) := by
  have step : branch done (run n) (.selected leaf.id []) := by
    refine .selected allowed (acyclic done _) ?_ ⟨⟨List.mem_cons_self,rfl⟩,probe n done⟩ ?_
      ⟨_,place,source_frame n done present,rfl⟩
    · rintro ⟨d,⟨listed,_⟩,deferred⟩
      cases List.mem_singleton.mp listed
      exact deferred (probe n done)
    · rintro d ⟨⟨listed,_⟩,_⟩
      cases List.mem_singleton.mp listed
      rfl
  exact ⟨.selected leaf.id [],.selected step .nil,.selected .nil (.selected rfl)⟩

theorem pending_same_model_names : Classify (branch emptyDone) b .pending :=
  ⟨.pending,.pending (.unsupported not_before (acyclic emptyDone b)),.pending⟩

theorem real_comparison (m) (valid : Models state m) :
    RequestSame m a b ∧ Classify (branch emptyDone) a (.selected dict) ∧
      Classify (branch emptyDone) b .pending ∧ Classify (branch realDone) b (.selected dict) := by
  refine ⟨equal_in_every_model m valid,can_select 0 emptyDone authorized_before ?_,pending_same_model_names,
    can_select 1 realDone authorized_later ?_⟩
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

end Yulang.GeneralDeclarativeAliasStatus327
