import Yulang.GeneralDeclarativeNestedSiblingsFrame332
import Yulang.GeneralDeclarativeNestedChild332

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 19000
set_option maxHeartbeats 16000000
namespace Yulang.GeneralDeclarativeNestedSiblingsResult332
open GeneralDeclarativeNestedSiblingsDecl332 (impl registry checked)
open GeneralDeclarativeNestedDecl332 (root)
open GeneralDeclarativeNestedSiblingsFrame332
open GeneralDeclarativeNestedExample332 (interpretation rows outerRow scalar innerResidual outerResidual)
open GeneralDeclarativeNestedFrame332 (spans capturedExpr rootWrite childWrite)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeGrowth327 (Extends trans fits)
open GeneralDeclarativeLowerKnown321 (Alias Ready knows_alias knows_row)
open GeneralDeclarativeObserverGrowth330 (preserve sources_grow)
open GeneralDeclarativeInlineView331 (match_grows)
open GeneralDeclarativeInlineEndpoint331 (Heads)
open GeneralDeclarativeOpaqueNominal328 (point_bounded)
open GeneralDeclarativeExampleSource320 (leaf)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeRank321 (graph_no_cycle)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativePriority321 (Candidates Recurs)
open GeneralDeclarativeUnfinishedRoot330 (Local59 dictionary_sound)
open GeneralDeclarativeCurrentReceipt330 (Staged literal)
open GeneralDeclarativeStableCompiler329 (Frame)
open GeneralDeclarationExamples (constructors)
open CommonRoleOutermostResolver (Classify Dictionary)

theorem to_final (done : Nat → Prop) : Extends source final :=
  trans (actual_head done).1.grows (trans grow_parent (trans grow_one grow_two))

def current (done : Nat → Prop) : Supported final done := preserve (origins done) (to_final done)

theorem one_alias (done : Nat → Prop) : Alias (restriction (current done)) 18 3 := by
  refine .bounds (.constraint ?_) (.constraint ?_)
  all_goals (change _ ∈ final.normal.ordinary; decide +kernel)

theorem two_alias (done : Nat → Prop) : Alias (restriction (current done)) 20 11 := by
  refine .bounds (.constraint ?_) (.constraint ?_)
  all_goals (change _ ∈ final.normal.ordinary; decide +kernel)

theorem root_ready (done : Nat → Prop) : Ready (current done) root := by
  intro a placed
  cases List.mem_singleton.mp placed
  exact ⟨_,knows_row (from_source (current done) (row := outerRow) ⟨List.mem_cons_self,rfl⟩) rfl⟩

theorem one_ready (done : Nat → Prop) : Ready (current done) first := by
  intro a placed
  cases List.mem_singleton.mp placed
  exact ⟨_,knows_alias (one_alias done) (knows_row
    (from_source (current done) (row := scalar)
      ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),rfl⟩) rfl)⟩

theorem two_ready (done : Nat → Prop) : Ready (current done) second := by
  intro a placed
  cases List.mem_singleton.mp placed
  exact ⟨_,knows_alias (two_alias done) (knows_row
    (from_source (current done) (row := scalar11) ⟨List.mem_append_right _ List.mem_cons_self,rfl⟩) rfl)⟩

theorem root_matches (done : Nat → Prop) :
    Heads (restriction (current done)) constructors interpretation root impl :=
  .cons (match_grows (sources_grow (origins done) (to_final done))
    (GeneralDeclarativeNestedSiblingsFrame332.observed done)) .nil

theorem one_matches (done : Nat → Prop) :
    Heads (restriction (current done)) constructors interpretation first leaf :=
  .cons ⟨(show Bounds final captureOne from fits (trans grow_one grow_two) bound_one),
    .variable 0,[⟨0,.lower,.variable 18⟩],[⟨0,.upper,.variable 19⟩],rfl,.capture,.capture⟩ .nil

theorem two_matches (done : Nat → Prop) :
    Heads (restriction (current done)) constructors interpretation second leaf :=
  .cons ⟨(show Bounds final captureTwo from fits (trans grow_one grow_two) bound_two),
    .variable 0,[⟨0,.lower,.variable 20⟩],[⟨0,.upper,.variable 21⟩],rfl,.capture,.capture⟩ .nil

theorem rows_exact : final.equations = eqs ++
    [⟨16,innerResidual⟩,⟨17,outerResidual⟩,⟨0,capturedExpr⟩,rootWrite,childWrite,secondWrite] := rfl

theorem no_cycles : ∀ n, ¬AliasCycle final (GeneralDeclarativeGraphRows321.observed final) n := by
  apply graph_no_cycle (fun _ => 0) (fun _ _ _ => rfl)
  rintro n code child ⟨rhs,stored,seen⟩ part
  rw [rows_exact] at stored
  simp only [eqs,rows,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at stored
  rcases stored with h|h|h|h|h|h|h|h|h|h <;> cases h <;> cases seen
  all_goals cases part

def tests (done : Nat → Prop) : Candidates :=
  ⟨Heads (restriction (current done)) constructors interpretation,
    fun d impl => ¬Heads (restriction (current done)) constructors interpretation d impl⟩

theorem safe (done : Nat → Prop) (d : Demand) : ¬Recurs final registry interpretation (tests done) d := by
  rintro (⟨arg,_,cycle⟩|⟨_,_,_,_,_,_,_,_,_,site,_,cycle⟩)
  · exact no_cycles arg.lower cycle
  · exact no_cycles site cycle

abbrev branch (done : Nat → Prop) :=
  Local59 final registry interpretation (current done) (tests done) (Staged final registry interpretation)

theorem root_only (d) (some : d ∈ registry.declarations) (role : d.role = root.role) : d = impl := by
  rcases List.mem_cons.mp some with rfl|other
  · rfl
  · cases List.mem_singleton.mp other
    cases role

theorem child_only (d) (some : d ∈ registry.declarations) (role : d.role = 2) : d = leaf := by
  rcases List.mem_cons.mp some with rfl|other
  · cases role
  · exact List.mem_singleton.mp other

theorem root_selects (done : Nat → Prop) : branch done root (.selected impl.id childList) := by
  refine .prior (.selected (root_ready done) (safe done _) ?_
    ⟨⟨List.mem_cons_self,rfl⟩,root_matches done⟩ ?_
    ⟨parent,parent_frame done,literal (trans grow_one grow_two)⟩)
  · rintro ⟨d,⟨visible,role⟩,waiting⟩
    cases root_only d visible role
    exact waiting (root_matches done)
  · intro actual shape
    rw [root_only actual shape.1.1 shape.1.2]

theorem child_selects (done : Nat → Prop) (d : Demand) {state : State}
    (role : d.role = 2) (ready : Ready (current done) d)
    (matched : Heads (restriction (current done)) constructors interpretation d leaf)
    (built : Nonempty (Frame state registry interpretation d leaf [])) (toFinal : Extends state final) :
    branch done d (.selected leaf.id []) := by
  refine .prior (.selected ready (safe done _) ?_
    ⟨⟨List.mem_cons_of_mem _ List.mem_cons_self,role.symm⟩,matched⟩ ?_
    ⟨state,built,literal toFinal⟩)
  · rintro ⟨candidate,⟨visible,same⟩,wait⟩
    cases child_only candidate visible (same.trans role)
    exact wait matched
  · intro other h
    rw [child_only other h.1.1 (h.1.2.trans role)]

abbrev dictionary : Dictionary := .node impl.id [.node leaf.id [],.node leaf.id []]

theorem exact_tree (done : Nat → Prop) : Classify (branch done) root (.selected dictionary) := by
  have left := child_selects done first rfl (one_ready done) (one_matches done) first_frame grow_two
  have right := child_selects done second rfl (two_ready done) (two_matches done)
    second_frame (GeneralDeclarativeClauseBatch327.reflexive final)
  exact ⟨.selected impl.id [.selected leaf.id [],.selected leaf.id []],
    .selected (root_selects done) (.cons (.selected left .nil) (.cons (.selected right .nil) .nil)),
    .selected (.cons (.selected .nil (.selected rfl)) (.cons (.selected .nil (.selected rfl)) .nil))
      (.selected rfl)⟩

theorem every_model (_m : GeneralNominalCommonBridge.Assignment) (fit : Models final _m) :
    GeneralDeclarativeEvidence320.Evidence registry interpretation _m root dictionary :=
  dictionary_sound checked covered wanted_root fit (exact_tree (fun _ => False))

end Yulang.GeneralDeclarativeNestedSiblingsResult332
