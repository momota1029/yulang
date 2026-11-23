import Yulang.GeneralDeclarativeI65Selection367

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open GeneralDeclarativeWitnessCompiler350 (Context Finished initial preparation whereBatch fixedBatch execute portNames placed)
open GeneralDeclarativeOpaqueCapture328 (choose)
open GeneralDeclarativeStableAssemble329 (firsts tieState merged prepare_grows)
open GeneralDeclarativeStableTies329 (pairOf rows model_batch)
open GeneralDeclarativeOpaqueShared328 (build)
open GeneralDeclarativeOpaqueGroup328 (group)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeCurrentReceipt330 (relays_models)
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeGrowth327 (restrict facts)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralDeclarations (Declaration)
open CommonNominalFullCarrier (Equivalent)

/-- Aggregating binders adds ordinary bounds but literally retains the
postselection equations. No compatibility of the original distinct
centers is assumed before selection. -/
theorem build_keeps_selected_equations (keep keys : List Nat)
    (spans : List (Nat × Capture)) (fallback : Nat → Capture) (s : GeneralDeclarativeHead320.State) :
    (build keep spans fallback s keys).state.equations = s.equations := by
  induction keys generalizing s with
  | nil => rfl
  | cons k ks ih =>
    cases step : group k spans with
    | nil => simpa only [build,step] using (ih s)
    | cons head tail =>
      simp only [build,step]
      exact ih (GeneralDeclarativeAggregate324.ready s keep head tail)

theorem actual_run_retains_initial_model (c : Context) {f : Finished} (ran : execute c = some f)
    (m : GeneralNominalCommonBridge.Assignment) (fits : Models f.state m) :
    Models (initial c).state m := by
  unfold execute at ran
  cases made : preparation c with
  | none => simp [made] at ran
  | some p =>
    obtain ⟨before,ports⟩ := p
    cases clauses : whereBatch c ports with
    | none => simp [made,clauses] at ran
    | some extra =>
      cases fixed : fixedBatch c ports with
      | none => simp [made,clauses,fixed] at ran
      | some written =>
        have shaped : (⟨appendFacts before extra,written,
            GeneralDeclarativeEmissionForest322.children c.decl (portNames c ports) (placed c ports)⟩ : Finished) = f := by
          simpa [made,clauses,fixed] using ran
        cases shaped
        have prepareOnly : GeneralDeclarativeGrowth327.Extends (initial c).state before :=
          prepare_grows made
        exact restrict prepareOnly m (restrict (facts _ _) m (restrict (facts _ _) m fits))

/-- Actual selected compiler span equalities, derived in every fitting
current model from postselection rows in the body, not guessed from
the endpoints used by inspection. -/
theorem receipt_repeated_centers {s : GeneralDeclarativeI65.State} {q : Request}
    {row : Declaration} {kids : List Request} (b : BodyFacts s q row kids)
    (m : Model) (fit : Fits s m) :
    ∀ item ∈ b.spans, Equivalent (m.assignment item.2.center).1
      (m.assignment ((firsts b.spans b.body.fallback item.1).center)).1 := by
  let c := actualContext b
  have initialFit := actual_run_retains_initial_model c b.body.run m.assignment
    (relays_models b.body.retained m.assignment fit.1.1)
  have equality : (initial c).state.equations = (tieState c.named c.spans c.fallback).equations :=
    build_keeps_selected_equations c.keep (c.spans.map Prod.fst) c.spans c.fallback
      (tieState c.named c.spans c.fallback)
  have retained : GeneralDeclarativeStableTies329.Present (initial c).state
      (firsts c.spans c.fallback) (c.spans.map pairOf) := by
    intro r present
    rw [equality]
    exact List.mem_append_right _ present
  intro item listed
  exact GeneralDeclarativeStableTies329.from_use (GeneralDeclarativeStableTies329.present_entails retained)
    (List.mem_map.mpr ⟨item,listed,rfl⟩) m.assignment initialFit

theorem firsts_follow_actual_first_find {spans : List (Nat × Capture)} {fallback : Nat → Capture}
    {key : Nat} {cap : Capture}
    (hits : (spans.find? (fun x => x.1 == key)).map Prod.snd = some cap) :
    firsts spans fallback key = cap := by
  induction spans with
  | nil => simp at hits
  | cons item tail ih =>
    obtain ⟨n,v⟩ := item
    by_cases same : n = key
    · subst n
      have equal : v = cap := by simpa using hits
      simp [firsts,choose,equal]
    · have rest : (tail.find? (fun x => x.1 == key)).map Prod.snd = some cap := by
        simpa [same] using hits
      have different := Ne.symm same
      simpa [firsts,choose,different] using ih rest

theorem actual_ports_share_original_uses {s : State} {q : Request}
    {row : Declaration} {kids : List Request} (b : BodyFacts s q row kids)
    {ports : List GeneralDeclarativeClauseBatch327.Port}
    {item : Nat × Capture} (member : item ∈ b.spans) (input : item.1 ∉ row.outputNames)
    {first : Capture}
    (hits : (b.spans.find? (fun x => x.1 == item.1)).map Prod.snd = some first)
    (m : Model) (fit : Fits s m) :
    Equivalent (m.assignment item.2.center).1
      (m.assignment ((portNames (actualContext b) ports).input item.1).center).1 := by
  have meaning := receipt_repeated_centers b m fit item member
  have earlier : firsts b.spans b.body.fallback item.1 = first :=
    firsts_follow_actual_first_find hits
  have actual : ((portNames (actualContext b) ports).input item.1).center = first.center :=
    actual_port_center (c := actualContext b) (ports := ports) hits input
  rw [earlier] at meaning
  rwa [actual]

end Yulang.GeneralDeclarativeI65
