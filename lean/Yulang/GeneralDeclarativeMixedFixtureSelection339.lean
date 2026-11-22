import Yulang.GeneralDeclarativeMixedFixtureRoutes339

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 2000000
namespace Yulang.GeneralDeclarativeMixedFixtureSelection339
open GeneralDeclarativeMixedFixtureBase339
open GeneralDeclarativeMixedFixtureRoutes339
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeCompoundTree338 (World)
open GeneralDeclarativeMixedTree339 (Node exact_tree)
open GeneralDeclarativeMixedInputs339 (Inputs input_exact)
open GeneralDeclarativeMixedCompiler339 (Selected)
open GeneralDeclarativeMixedDictionary339 (Rule Evidence dictionary_sound)
open GeneralDeclarativeCompoundBatch338 (authored_row)
open GeneralDeclarativeCompoundReadback338 (stored_low)
open GeneralDeclarativeCompoundSources338 (anchors_grow)
open GeneralDeclarativeStableAssemble329 (assemble merged)
open GeneralDeclarativeStableAttempt329 (Elected)
open GeneralDeclarativeInlineEndpoint331 (candidates Heads)
open GeneralDeclarativeEndpointProbe321 (HeadMatches)
open GeneralDeclarativeGrowth327 (Extends fits trans facts)
open GeneralDeclarativeObserverGrowth330 (preserve sources_grow)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralDeclarativeLowerKnown321 (Ready Alias knows_alias knows_row)
open GeneralDeclarativeCurrentReceipt330 (literal)
open GeneralDeclarativePriority321 (Recurs)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeGraphRows321 (observed shapeOf)
open GeneralDeclarativeRank321 (graph_no_cycle)
open GeneralDeclarativeExampleSource320 (leaf)
open GeneralDeclarativeHiddenDecl324 (catalogue interpretation)
open GeneralDeclarativeNestedBody332 (compileBody)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open CommonRoleOutermostResolver (Classify Dictionary)

abbrev childArg : Capture := ⟨20,19,21⟩
abbrev child : Demand := ⟨2,[childArg],[⟨1,5⟩]⟩
abbrev rootBuilt := (merged w3.state keep used fallback).state
abbrev rootWrite : Equation := ⟨6,.variable 11⟩
abbrev rootFinal := appendFacts rootBuilt [rootWrite]
abbrev childUses : List (Nat × Capture) := [(0,childArg)]
abbrev childBuilt := (merged rootFinal keep childUses fallback).state
abbrev childWrite : Equation := ⟨5,.variable 19⟩
abbrev final := appendFacts childBuilt [childWrite]

theorem root_compiles : compiled = some (rootFinal,[child]) := rfl
theorem child_compiles : compileBody registry interpretation child leaf rootFinal childUses keep fallback targets =
    some (final,[]) := rfl
theorem bodyGrows {s : State} {uses : List (Nat × Capture)}
    (known : ∀ x ∈ uses, Bounds s x.2) (writes : List Equation) :
    Extends s (appendFacts (merged s keep uses fallback).state writes) :=
  GeneralDeclarativeGrowth327.trans (facts _ _) (GeneralDeclarativeGrowth327.trans
    (assemble keep uses fallback known).preserve.grows (facts _ _))
theorem root_grows : Extends w3.state rootFinal :=
  bodyGrows (input_exact GeneralDeclarativeMixedFixtureRoutes339.observed).2.2 _
theorem child_bounds : Bounds rootFinal childArg := by
  refine ⟨.constraint ?_,.constraint ?_⟩
  all_goals decide +kernel
theorem child_grows : Extends rootFinal final :=
  bodyGrows (fun _ h => by cases List.mem_singleton.mp h; exact child_bounds) _
theorem named_final : Extends w3.state final := GeneralDeclarativeGrowth327.trans root_grows child_grows
theorem initial_final : Extends initial final :=
  GeneralDeclarativeGrowth327.trans (exact_tree routed).1.1.1 named_final

def current : Supported final (fun _ => False) := preserve w3.source named_final
theorem previous_source : Extends (restriction support) (restriction current) :=
  GeneralDeclarativeGrowth327.trans (exact_tree routed).1.1.2.2 (sources_grow w3.source named_final)

def height (n : Nat) : Nat := if n < 3 then 3 else if 7 ≤ n ∧ n < 10 then 2 else if 13 ≤ n ∧ n < 16 then 1 else 0
def edgeOK (edge : Nat × Nat) : Bool := decide (height edge.1 ≤ height edge.2)
def atomOK (a : PresenceNormalForm.Atom Nat) : Bool :=
  match a with | .tyLe (.var n) (.var m) => edgeOK (n,m) | _ => true
def rowOK (e : Equation) : Bool :=
  match e.right with | .variable n => decide (height e.left = height n) | _ => true
def decreases (e : Equation) : Bool :=
  match shapeOf e.right with
  | none => true
  | some tag => tag.children.all (fun n => decide (height n < height e.left))

theorem safe : ∀ k, ¬AliasCycle final (GeneralDeclarativeGraphRows321.observed final) k := by
  have edges : final.normal.intervals.all edgeOK = true := by decide +kernel
  have atoms : final.normal.ordinary.all atomOK = true := by decide +kernel
  have stored : final.equations.all rowOK = true := by decide +kernel
  have shape : final.equations.all decreases = true := by decide +kernel
  have boundsUp {a b} (h : GeneralDeclarativeBounds319.Bound final.normal a b) : height a ≤ height b := by
    induction h with
    | interval seen => exact of_decide_eq_true (List.all_eq_true.mp edges _ seen)
    | constraint seen => exact of_decide_eq_true (List.all_eq_true.mp atoms _ seen)
    | refl _ => exact Nat.le_refl _
    | trans _ _ low high => exact Nat.le_trans low high
  have level {a b} (h : Alias final a b) : height a = height b := by
    induction h with
    | bounds one two => exact Nat.le_antisymm (boundsUp one) (boundsUp two)
    | forward row => exact of_decide_eq_true (List.all_eq_true.mp stored _ row)
    | backward row => exact (of_decide_eq_true (List.all_eq_true.mp stored _ row)).symm
    | trans _ _ a b => exact a.trans b
  apply graph_no_cycle height (fun _ _ => level)
  rintro n tag descendant ⟨rhs,found,code⟩ member
  have measured := List.all_eq_true.mp shape ⟨n,rhs⟩ found
  change decreases ⟨n,rhs⟩ = true at measured
  unfold decreases at measured
  rw [code] at measured
  exact of_decide_eq_true (List.all_eq_true.mp measured descendant member)

def wait (_ : Demand) (_ : Declaration) : Prop := False
theorem no_cycle (d : Demand) : ¬Recurs final registry interpretation (candidates current registry interpretation wait) d := by
  rintro (⟨a,_,cy⟩|⟨_,_,_,_,_,_,_,_,_,site,_,cy⟩)
  · exact safe a.lower cy
  · exact safe site cy

theorem root_picks : Elected final registry interpretation current (candidates current registry interpretation wait) root decl := by
  have rdy : Ready current root := by
    intro a h; cases List.mem_singleton.mp h
    exact ⟨_,knows_row (previous_source.equations loKnown) rfl⟩
  have ready := source_positive (q := current) previous_source (fits initial_final bounds)
  refine ⟨rdy,no_cycle root,fun ⟨_,_,bad⟩ => bad,⟨⟨List.mem_cons_self,rfl⟩,.inr ready⟩,?_⟩
  intro other allowed
  rcases List.mem_cons.mp allowed.1.1 with rfl|second
  · rfl
  · cases List.mem_singleton.mp second
    cases allowed.1.2

theorem child_lower : GeneralDeclarativeLowerKnown321.Knows (restriction current)
    childArg.lower (.primitive (.scalar .int) 0) := by
  have into : Alias (restriction current) 20 3 := by
    refine .bounds (.constraint ?_) (.constraint ?_)
    all_goals decide +kernel
  exact knows_alias into (knows_row (previous_source.equations scalarKnown) rfl)

theorem child_picks : Elected final registry interpretation current (candidates current registry interpretation wait) child leaf := by
  have rdy : Ready current child := by
    intro a h; cases List.mem_singleton.mp h
    exact ⟨_,child_lower⟩
  have range := fits child_grows child_bounds
  have seen : HeadMatches (restriction current) catalogue interpretation child leaf :=
    .cons ⟨range,.variable 0,[⟨0,.lower,20⟩],[⟨0,.upper,21⟩],rfl,.capture,.capture⟩ .nil
  refine ⟨rdy,no_cycle child,fun ⟨_,_,bad⟩ => bad,
    ⟨⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩,.inl seen⟩,?_⟩
  intro other allowed
  rcases List.mem_cons.mp allowed.1.1 with rfl|second
  · cases allowed.1.2
  · cases List.mem_singleton.mp second
    rfl

def rootSelection : Selected current w3.reads registry interpretation wait root decl [child] where
  slice := ⟨initial,support,initial_final,previous_source⟩
  seed := []
  keep := keep
  named := w3
  spans := used
  inputs := GeneralDeclarativeMixedFixtureRoutes339.observed
  fallback := fallback
  targets := targets
  ordinary := rootFinal
  compiler := root_compiles
  receipt := literal child_grows
  retained := fun _ h => h
  chosen := root_picks

def childSupport : Supported rootFinal (fun _ => False) := preserve w3.source root_grows
abbrev childWorld : World (fun _ => False) := ⟨rootFinal,childSupport,w3.reads⟩

theorem childSources : Extends (restriction childSupport) (restriction current) := by
  refine ⟨child_grows.constraints,child_grows.intervals,?_⟩
  intro e given
  exact (sources_grow w3.source named_final).equations
    ((GeneralDeclarativeObserverGrowth330.backed_same w3.source root_grows e).mp given)

def childSelection : Selected current w3.reads registry interpretation wait child leaf [] where
  slice := ⟨rootFinal,childSupport,child_grows,childSources⟩
  seed := w3.reads
  keep := keep
  named := childWorld
  spans := childUses
  inputs := by
    change Inputs catalogue interpretation keep childWorld [childArg] [GeneralDeclarationPatterns.Pattern.var 0] childWorld [(0,childArg)]
    simpa only [List.append_nil] using Inputs.cons (c := catalogue) (i := interpretation)
      (p := GeneralDeclarationPatterns.Pattern.var 0)
      (Node.binder (c := catalogue) (i := interpretation) (w := childWorld) (keep := keep) (n := 0) (arg := childArg) child_bounds) Inputs.nil
  fallback := fallback
  targets := targets
  ordinary := final
  compiler := child_compiles
  receipt := literal (GeneralDeclarativeClauseBatch327.reflexive _)
  retained := fun _ h => h
  chosen := child_picks

abbrev dictionary : Dictionary := .node 97 [.node leaf.id []]
theorem selected : Classify (Rule current w3.reads registry interpretation wait) root (.selected dictionary) :=
  ⟨.selected decl.id [.selected leaf.id []],
    .selected (.compound rootSelection) (.cons (.selected (.compound childSelection) .nil) .nil),
    .selected (.cons (.selected .nil (.selected rfl)) .nil) (.selected rfl)⟩

theorem every_model (m) (valid : GeneralDeclarativeExactOverlay337.ModelsExact final w3.reads m) :
    Evidence registry interpretation m root dictionary :=
  dictionary_sound checked covered wanted selected m valid

end Yulang.GeneralDeclarativeMixedFixtureSelection339
