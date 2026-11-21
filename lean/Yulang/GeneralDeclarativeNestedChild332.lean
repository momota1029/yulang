import Yulang.GeneralDeclarativeNestedFrame332
import Yulang.GeneralDeclarativeRank321
import Yulang.GeneralDeclarativeUnfinishedRoot330
import Yulang.GeneralDeclarativeInlineView331

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 19000
set_option maxHeartbeats 16000000
namespace Yulang.GeneralDeclarativeNestedChild332
open GeneralDeclarativeNestedDecl332
open GeneralDeclarativeNestedExample332 (interpretation state supports rows outerRow innerRow scalar observed_endpoints)
open GeneralDeclarativeNestedFrame332
  (stage spans grouped fallback targets keep rootStage rootWrite childWrite exact_observed exact_children_and_writes
    root_frame covered declared capturedExpr)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeStableReads329 (Heads)
open GeneralDeclarativeStableCompiler329 (Frame)
open GeneralDeclarativeInlineEndpoint331 (Matches)
open GeneralDeclarativeNestedBody332 (compiler_exact compileBody)
open GeneralDeclarativeStableAssemble329 (merged MergeFacts)
open GeneralDeclarativeGrowth327 (Extends trans facts fits)
open GeneralDeclarativeLowerKnown321 (Alias Ready knows_alias knows_row)
open GeneralDeclarativeObserverGrowth330 (preserve sources_grow)
open GeneralDeclarativeInlineView331 (match_grows)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralDeclarativeOpaqueNominal328 (point point_bounded)
open GeneralDeclarativeExampleSource320 (leaf)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeRank321 (graph_no_cycle)
open GeneralDeclarativePriority321 (Candidates Recurs)
open GeneralDeclarativeUnfinishedRoot330 (Local59 dictionary_sound)
open GeneralDeclarativeCurrentReceipt330 (Staged literal)
open GeneralDeclarationExamples (constructors)
open CommonRoleOutermostResolver (Classify Dictionary)

abbrev capture : Capture := ⟨18,3,19⟩
abbrev leafSpans : List (Nat × Capture) := [(0,capture)]
abbrev childGrouped := merged rootStage keep leafSpans fallback
abbrev final := appendFacts childGrouped.state [childWrite]

theorem gathered (done : Nat → Prop) : MergeFacts stage keep spans fallback :=
  GeneralDeclarativeStableAssemble329.assemble keep spans fallback (exact_observed done).2.2.2.1

theorem root_grows : Extends stage rootStage :=
  trans (gathered (fun _ => False)).preserve.grows (facts _ _)

theorem child_bounds : Bounds rootStage capture := by
  change Bounds rootStage (grouped.captures 0)
  exact fits (facts _ _) ((gathered (fun _ => False)).ranges (0,point 3) List.mem_cons_self)

theorem child_gathered : MergeFacts rootStage keep leafSpans fallback :=
  GeneralDeclarativeStableAssemble329.assemble keep leafSpans fallback (fun use h => by
    cases List.mem_singleton.mp h
    exact child_bounds)

theorem child_grows : Extends rootStage final :=
  trans child_gathered.preserve.grows (facts _ _)

theorem all_grows (done : Nat → Prop) : Extends state final :=
  trans (exact_observed done).1.grows (trans root_grows child_grows)

theorem wanted_child : Declared registry child := by
  intro out wanted
  cases List.mem_singleton.mp wanted
  exact ⟨none,rfl⟩

theorem child_code :
    compileBody registry interpretation child leaf rootStage leafSpans keep fallback targets =
      some (final,[]) := rfl

theorem child_frame : Nonempty (Frame final registry interpretation child leaf []) := by
  have seen : Heads rootStage constructors interpretation child.arguments leaf.head leafSpans := by
    change Heads rootStage constructors interpretation [capture] [.var 0] (leafSpans ++ [])
    exact .cons ⟨child_bounds,.variable 0,.variable 3,rfl,.refl _,.capture⟩ .nil
  obtain ⟨current,kids,f,computed,_,_,_,_,_,_⟩ := compiler_exact checked covered
    (show leaf ∈ registry.declarations from List.mem_cons_of_mem _ List.mem_cons_self)
    rfl wanted_child keep fallback targets seen (fun u member => by
      cases List.mem_singleton.mp member
      exact child_bounds)
  have eq := Option.some.inj (computed.symm.trans child_code)
  cases eq
  exact ⟨f⟩

def current (done : Nat → Prop) : Supported final done := preserve (supports done) (all_grows done)

theorem endpoint_alias (done : Nat → Prop) : Alias (restriction (current done)) 18 3 := by
  refine .bounds (.constraint ?_) (.constraint ?_)
  all_goals (change _ ∈ final.normal.ordinary; decide +kernel)

theorem root_ready (done : Nat → Prop) : Ready (current done) root := by
  intro arg h
  cases List.mem_singleton.mp h
  exact ⟨_,knows_row (from_source (current done) (row := outerRow) ⟨List.mem_cons_self,rfl⟩) rfl⟩

theorem child_ready (done : Nat → Prop) : Ready (current done) child := by
  intro arg h
  cases List.mem_singleton.mp h
  exact ⟨_,knows_alias (endpoint_alias done)
    (knows_row (from_source (current done) (row := scalar)
      ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),rfl⟩) rfl)⟩

theorem root_matches (done : Nat → Prop) :
    GeneralDeclarativeInlineEndpoint331.Heads (restriction (current done)) constructors interpretation root decl :=
  .cons (match_grows (sources_grow (supports done) (all_grows done)) (observed_endpoints done)) .nil

theorem child_matches (done : Nat → Prop) :
    GeneralDeclarativeInlineEndpoint331.Heads (restriction (current done)) constructors interpretation child leaf :=
  .cons ⟨(show Bounds (restriction (current done)) capture from (fits child_grows child_bounds : Bounds final capture)),.variable 0,[⟨0,.lower,.variable 18⟩],
    [⟨0,.upper,.variable 19⟩],rfl,.capture,.capture⟩ .nil

theorem exact_rows : final.equations = rows ++
    [⟨16,GeneralDeclarativeNestedExample332.innerResidual⟩,⟨17,GeneralDeclarativeNestedExample332.outerResidual⟩,
      ⟨0,capturedExpr⟩,rootWrite,childWrite] := rfl

theorem no_cycles : ∀ n, ¬AliasCycle final (observed final) n := by
  apply graph_no_cycle (fun _ => 0) (fun _ _ _ => rfl)
  rintro n shape kid ⟨rhs,row,parsed⟩ occupies
  rw [exact_rows] at row
  simp only [rows,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at row
  rcases row with h|h|h|h|h|h|h|h <;> cases h <;> cases parsed
  all_goals cases occupies

def tests (done : Nat → Prop) : Candidates :=
  ⟨GeneralDeclarativeInlineEndpoint331.Heads (restriction (current done)) constructors interpretation,
    fun d impl => ¬GeneralDeclarativeInlineEndpoint331.Heads (restriction (current done)) constructors interpretation d impl⟩

theorem safe (done : Nat → Prop) (d : Demand) : ¬Recurs final registry interpretation (tests done) d := by
  rintro (⟨arg,_,cycle⟩|⟨_,_,_,_,_,_,_,_,_,site,_,cycle⟩)
  · exact no_cycles arg.lower cycle
  · exact no_cycles site cycle

abbrev branch (done : Nat → Prop) :=
  Local59 final registry interpretation (current done) (tests done) (Staged final registry interpretation)

abbrev dictionary : Dictionary := .node decl.id [.node leaf.id []]

theorem root_only (d) (registered : d ∈ registry.declarations) (role : d.role = root.role) : d = decl := by
  rcases List.mem_cons.mp registered with rfl|tail
  · rfl
  · cases List.mem_singleton.mp tail
    cases role

theorem child_only (d) (registered : d ∈ registry.declarations) (role : d.role = child.role) : d = leaf := by
  rcases List.mem_cons.mp registered with rfl|tail
  · cases role
  · exact List.mem_singleton.mp tail

theorem root_selected (done : Nat → Prop) : branch done root (.selected decl.id [child]) := by
  refine .prior (.selected (root_ready done) (safe done _) ?_
    ⟨⟨List.mem_cons_self,rfl⟩,root_matches done⟩ ?_
    ⟨rootStage,root_frame done,literal child_grows⟩)
  · rintro ⟨d,⟨listed,role⟩,blocked⟩
    cases root_only d listed role
    exact blocked (root_matches done)
  · intro d found
    rw [root_only d found.1.1 found.1.2]

theorem child_selected (done : Nat → Prop) : branch done child (.selected leaf.id []) := by
  refine .prior (.selected (child_ready done) (safe done _) ?_
    ⟨⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩,child_matches done⟩ ?_
    ⟨final,child_frame,literal (GeneralDeclarativeClauseBatch327.reflexive final)⟩)
  · rintro ⟨d,⟨listed,role⟩,blocked⟩
    cases child_only d listed role
    exact blocked (child_matches done)
  · intro d found
    rw [child_only d found.1.1 found.1.2]

theorem tree (done : Nat → Prop) : Classify (branch done) root (.selected dictionary) :=
  ⟨.selected decl.id [.selected leaf.id []],
    .selected (root_selected done) (.cons (.selected (child_selected done) .nil) .nil),
    .selected (.cons (.selected .nil (.selected rfl)) .nil) (.selected rfl)⟩

theorem every_model (_m : GeneralNominalCommonBridge.Assignment) (fit : Models final _m) :
    GeneralDeclarativeEvidence320.Evidence registry interpretation _m root dictionary :=
  dictionary_sound checked covered declared fit (tree (fun _ => False))

end Yulang.GeneralDeclarativeNestedChild332
