import Yulang.GeneralDeclarativeNestedSiblingsDecl332
import Yulang.GeneralDeclarativeNestedIndex332

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 19000
set_option maxHeartbeats 16000000
namespace Yulang.GeneralDeclarativeNestedSiblingsFrame332
open GeneralDeclarativeNestedSiblingsDecl332
open GeneralDeclarativeNestedDecl332 (normal normalizedExpr root)
open GeneralDeclarativeNestedExample332 (interpretation rows uses pat)
open GeneralDeclarativeNestedFrame332 (capturedExpr spans fallback rootWrite childWrite)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeNestedIndex332 (ofRows)
open GeneralDeclarativeNestedDecode332 (normalized normalized_sound)
open GeneralDeclarativeNestedMaterial332 (assemble computed_frame)
open GeneralDeclarativeNestedBody332 (compileBody compiler_exact)
open GeneralDeclarativeInlineMaterial331 (named ordinary)
open GeneralDeclarativeInlineEndpoint331 (Matches)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralDeclarativeStableReads329 (One Heads)
open GeneralDeclarativeStableCompiler329 (Frame)
open GeneralDeclarativeStableAssemble329 (merged MergeFacts)
open GeneralDeclarativeOpaqueConserve328 (Retains)
open GeneralDeclarativeOpaqueNominal328 (point point_bounded)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeGrowth327 (Extends facts trans fits)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralDeclarationExamples (constructors)
open GeneralDeclarativePairDecl326 (clause)
open GeneralDeclarativeExampleSource320 (leaf)
open GeneralDeclarativeOpaqueBatch328 (check)
open GeneralDeclarations (Clause)

abbrev scalar11 : Equation := ⟨11,.primitive (.scalar .bool) []⟩
abbrev eqs := rows ++ [scalar11]
abbrev source : State := ⟨⟨[],[]⟩,eqs⟩
def origins (done : Nat → Prop) : Supported source done :=
  ⟨fun e o => e ∈ eqs ∧ o = .source,fun h => h.1⟩
noncomputable def indexed (done : Nat → Prop) :=
  ofRows eqs (fun _ h => from_source (origins done) ⟨h,rfl⟩)
theorem actual (done : Nat → Prop) :
    normalized (indexed done) constructors interpretation .actual (.variable 0) pat = some (uses .actual) := rfl
theorem lower (done : Nat → Prop) :
    normalized (indexed done) constructors interpretation .lower (.variable 0) pat = some (uses .lower) := rfl
theorem upper (done : Nat → Prop) :
    normalized (indexed done) constructors interpretation .upper (.variable 0) pat = some (uses .upper) := rfl

theorem observed (done : Nat → Prop) :
    Matches (restriction (origins done)) constructors interpretation (point 0) pat := by
  obtain ⟨c,left,l⟩ := normalized_sound (lower done)
  obtain ⟨c',right,u⟩ := normalized_sound (upper done)
  have same := Option.some.inj (left.symm.trans right)
  exact ⟨point_bounded _ _,c,_,_,left,l,same.symm ▸ u⟩

abbrev keep := [5,6,10]
abbrev namedStage := named source (point 0) keep (uses .actual)
abbrev stage := appendFacts namedStage [⟨0,capturedExpr⟩]
abbrev mergedRoot := merged stage keep spans fallback
abbrev parent := appendFacts mergedRoot.state [rootWrite]
abbrev captureOne : Capture := ⟨18,3,19⟩
abbrev captureTwo : Capture := ⟨20,11,21⟩
abbrev first : Demand := ⟨2,[captureOne],[⟨1,5⟩]⟩
abbrev second : Demand := ⟨2,[captureTwo],[⟨1,10⟩]⟩
abbrev childList := [first,second]
abbrev spansOne : List (Nat × Capture) := [(0,captureOne)]
abbrev spansTwo : List (Nat × Capture) := [(0,captureTwo)]
abbrev mergedOne := merged parent keep spansOne fallback
abbrev firstDone := appendFacts mergedOne.state [childWrite]
abbrev mergedTwo := merged firstDone keep spansTwo fallback
abbrev secondWrite : Equation := ⟨10,.variable 11⟩
abbrev final := appendFacts mergedTwo.state [secondWrite]

def targets (producer : Clause) (_ : Nat) : Nat := if producer.id = 20 then 5 else 10

theorem actual_head (done : Nat → Prop) :
    Retains source stage keep ∧ One stage constructors interpretation (point 0) pat spans ∧
    ordinary source (point 0) keep (uses .actual) ⊆ stage.equations ∧
    (∀ o ∈ spans, Bounds stage o.2) ∧ ∀ m, Models stage m ↔ Models namedStage m := by
  obtain ⟨c,decoded,proof⟩ := normalized_sound (actual done)
  have exact := Option.some.inj (decoded.symm.trans normal)
  cases exact
  exact computed_frame (point_bounded _ _) normal proof rfl

theorem covered : Coverage registry interpretation := by
  have base := GeneralDeclarativeNestedFrame332.covered
  constructor
  · intro d listed
    rcases List.mem_cons.mp listed with rfl|other
    · have prior := base.1 GeneralDeclarativeNestedDecl332.decl List.mem_cons_self
      refine ⟨prior.1,?_,prior.2.2⟩
      intro req seen
      rcases picked req seen with rfl|rfl
      · exact prior.2.1 _ List.mem_cons_self
      · refine ⟨⟨trivial,trivial⟩,?_⟩
        intro eq member
        cases List.mem_singleton.mp member
        trivial
    · exact base.1 d (List.mem_cons_of_mem _ other)
  · exact base.2

theorem exact_order_writes :
    compileBody registry interpretation root impl stage spans keep fallback targets = some (parent,childList) ∧
    compileBody registry interpretation first leaf parent spansOne keep fallback targets = some (firstDone,[]) ∧
    compileBody registry interpretation second leaf firstDone spansTwo keep fallback targets = some (final,[]) :=
  ⟨rfl,rfl,rfl⟩

theorem order_is_real :
    check childList [second,first] = false ∧
    check childList [first,⟨2,[captureTwo],[⟨1,5⟩]⟩] = false := ⟨rfl,rfl⟩

theorem gathered (done : Nat → Prop) : MergeFacts stage keep spans fallback :=
  GeneralDeclarativeStableAssemble329.assemble keep spans fallback (actual_head done).2.2.2.1

theorem grow_parent : Extends stage parent := trans (gathered (fun _ => False)).preserve.grows (facts _ _)

theorem bound_one : Bounds parent captureOne := by
  change Bounds parent (mergedRoot.captures 0)
  exact fits (facts _ _) ((gathered (fun _ => False)).ranges (0,point 3) List.mem_cons_self)

theorem bound_two : Bounds parent captureTwo := by
  change Bounds parent (mergedRoot.captures 3)
  exact fits (facts _ _) ((gathered (fun _ => False)).ranges (3,point 11)
    (List.mem_cons_of_mem _ List.mem_cons_self))

theorem gatheredOne : MergeFacts parent keep spansOne fallback :=
  GeneralDeclarativeStableAssemble329.assemble keep spansOne fallback (fun o used => by
    cases List.mem_singleton.mp used
    exact bound_one)

theorem grow_one : Extends parent firstDone := trans gatheredOne.preserve.grows (facts _ _)

theorem gatheredTwo : MergeFacts firstDone keep spansTwo fallback :=
  GeneralDeclarativeStableAssemble329.assemble keep spansTwo fallback (fun o used => by
    cases List.mem_singleton.mp used
    exact fits grow_one bound_two)

theorem grow_two : Extends firstDone final := trans gatheredTwo.preserve.grows (facts _ _)

theorem wanted_root : Declared registry root := GeneralDeclarativeNestedFrame332.declared

theorem wanted_one : Declared registry first := by
  intro request use
  cases List.mem_singleton.mp use
  exact ⟨none,rfl⟩

theorem wanted_two : Declared registry second := by
  intro request use
  cases List.mem_singleton.mp use
  exact ⟨none,rfl⟩

theorem parent_frame (done : Nat → Prop) : Nonempty (Frame parent registry interpretation root impl childList) := by
  have read : Heads stage constructors interpretation root.arguments impl.head spans :=
    .cons (rest := []) (actual_head done).2.1 .nil
  obtain ⟨out,kids,frame,ran,_,_,_,_,_,_⟩ := compiler_exact checked covered
    (show impl ∈ registry.declarations from List.mem_cons_self) rfl wanted_root keep fallback targets read
      (actual_head done).2.2.2.1
  have shape := Option.some.inj (ran.symm.trans exact_order_writes.1)
  cases shape
  exact ⟨frame⟩

theorem first_frame : Nonempty (Frame firstDone registry interpretation first leaf []) := by
  have rootArgs : Heads parent constructors interpretation first.arguments leaf.head spansOne := by
    change Heads parent constructors interpretation [captureOne] [.var 0] (spansOne ++ [])
    exact .cons ⟨bound_one,.variable 0,.variable 3,rfl,.refl _,.capture⟩ .nil
  obtain ⟨t,kids,frame,computed,_,_,_,_,_,_⟩ := compiler_exact checked covered
    (show leaf ∈ registry.declarations from List.mem_cons_of_mem _ List.mem_cons_self) rfl wanted_one
    keep fallback targets rootArgs (fun u member => by cases List.mem_singleton.mp member; exact bound_one)
  have same := Option.some.inj (computed.symm.trans exact_order_writes.2.1)
  cases same
  exact ⟨frame⟩

theorem second_frame : Nonempty (Frame final registry interpretation second leaf []) := by
  have b := fits grow_one bound_two
  have rootArgs : Heads firstDone constructors interpretation second.arguments leaf.head spansTwo := by
    change Heads firstDone constructors interpretation [captureTwo] [.var 0] (spansTwo ++ [])
    exact .cons ⟨b,.variable 0,.variable 11,rfl,.refl _,.capture⟩ .nil
  obtain ⟨t,kids,frame,computed,_,_,_,_,_,_⟩ := compiler_exact checked covered
    (show leaf ∈ registry.declarations from List.mem_cons_of_mem _ List.mem_cons_self) rfl wanted_two
    keep fallback targets rootArgs (fun u member => by cases List.mem_singleton.mp member; exact b)
  have same := Option.some.inj (computed.symm.trans exact_order_writes.2.2)
  cases same
  exact ⟨frame⟩

end Yulang.GeneralDeclarativeNestedSiblingsFrame332
