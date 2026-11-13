import Yulang.GeneralNominalReportPaths
import Yulang.GeneralNominalGroundPacketForest

/-! Missing origins can descend through structural bounds before nominal
inspection introduces an endpoint fallback. Both endpoints retain finite
readbacks throughout that descent; no interior of an interval is chosen. -/
namespace Yulang.GeneralNominalFallbackReadback
open GeneralNominalRecursiveInspection GeneralNominalCanonicalPaths GeneralNominalReportPaths
open GeneralNominalGroundAccessibility GeneralNominalOriginTerms GeneralNominalFiniteMeaning
open GeneralNominalInspection (Query Bounds)
open GeneralNominalSaturationState GeneralNominalStructuralReadback
open GeneralNominalReadbackFunctionality
open CommonNominalFullCarrier

def Bounded (context : GeneralNominalCandidates.Context) (model : GeneralNominalCommonBridge.Assignment)
    (budget : Nat) (origin : Origin) : Prop :=
  ∃ pattern term, ClosedTerm context pattern term ∧ At model .actual origin (denote (fun _ => .bottom) term) ∧
    GeneralNominalPatersonLineage.mass [pattern] ≤ budget

def Endpoints (context : GeneralNominalCandidates.Context) (model : GeneralNominalCommonBridge.Assignment)
    (budget : Nat) (state : GeneralNominalState.State) (bounds : Bounds state) : Prop :=
  Bounded context model budget (.source (state.base.source bounds.1)) ∧
    Bounded context model budget (.source (state.base.source bounds.2))

def Supported (context : GeneralNominalCandidates.Context) (model : GeneralNominalCommonBridge.Assignment)
    (budget : Nat) (report : Report state) : Prop :=
  ∀ capture ∈ report.captures, ∀ origin, capture.origin = some origin →
    ∀ actual, Observes model origin actual → Bounded context model budget origin

variable {model : GeneralNominalCommonBridge.Assignment}

theorem bounded_path (known : Bounded context model budget root) (path : Path root endpoint)
    (observed : Observes model endpoint actual) : Bounded context model budget endpoint := by
  obtain ⟨pattern,term,closed,meaning,bound⟩ := known
  obtain ⟨source,part,_,reified,readback,small⟩ := closed_pattern path closed meaning observed
  exact ⟨source,part,reified,readback,Nat.le_trans small bound⟩

theorem bounded_same (known : Bounded context model budget first) (same : Same model first last) :
    Bounded context model budget last := by
  obtain ⟨pattern,term,closed,meaning,bound⟩ := known
  obtain ⟨value,seen⟩ := meaning.1
  refine ⟨pattern,term,closed,⟨same.2.1,?_⟩,bound⟩
  intro actual observed
  have equal := same.2.2 value actual seen observed
  have finite := meaning.2 value seen
  exact ⟨subtype_trans equal.2 finite.1,subtype_trans finite.2 equal.1⟩

theorem source_child (state : State roles) (valid : Models state model)
    (parent : Fin state.context.state.base.slots) (kind : Fin state.context.state.view.kinds)
    (children : Fin (state.context.state.view.shapes kind).arity → Fin state.context.state.base.slots)
    (recorded : state.context.state.view.heads parent = .structural kind children)
    (known : Bounded context model budget (.source (state.context.state.base.source parent)))
    (index : Fin (state.context.state.view.shapes kind).arity) :
    Bounded context model budget (.source (state.context.state.base.source (children index))) := by
  have same := actual_structural_readback state parent kind children recorded index model valid
  obtain ⟨value,observed⟩ := same.1
  have projected := bounded_path known (.structural (state.context.state.view.canonical kind) .root) observed
  exact bounded_same projected same

theorem rooted_supported (known : Bounded context model budget root) (rooted : Rooted report root) :
    Supported context model budget report := by
  intro capture member origin recorded actual observed
  obtain ⟨endpoint,same,path⟩ := rooted capture member
  have identical : endpoint = origin := Option.some.inj (same.symm.trans recorded)
  subst endpoint
  exact bounded_path known path observed

private theorem append_supported (first : Supported context model budget (one : Report state))
    (last : Supported context model budget two) : Supported context model budget (one.append two) := by
  intro capture member
  rcases List.mem_append.mp member with one | two
  · exact first capture one
  · exact last capture two

mutual
  theorem missing_supported (state : State roles) (valid : Models state model) (query : Query)
      (bounds : Bounds state.context.state) (known : Endpoints context model budget state.context.state bounds) :
      Supported context model budget (inspect state.context.state query bounds none) := by
    cases query with
    | variables names =>
      intro capture member origin recorded
      simp only [inspect] at member
      obtain ⟨name,_,rfl⟩ := List.mem_map.mp member
      cases recorded
    | deferred => simp [Supported,inspect,block]
    | scalar base =>
      simp only [inspect,Report.visit]
      split
      · intro capture member; cases member
      · split
        · split <;> (intro capture member; cases member)
        · intro capture member; cases member
        · intro capture member; cases member
    | node shape children =>
      simp only [inspect,Report.visit]
      split
      · rename_i lower xs upper ys lowerAt upperAt
        split
        · apply many_missing_supported state valid children
          intro interval member
          have entries := List.of_mem_zip member
          obtain ⟨first,firstAt⟩ := List.mem_ofFn.mp entries.1
          obtain ⟨last,lastAt⟩ := List.mem_ofFn.mp entries.2
          exact ⟨firstAt ▸ source_child state valid bounds.1 lower xs lowerAt known.1 first,
            lastAt ▸ source_child state valid bounds.2 upper ys upperAt known.2 last⟩
        · intro capture member; cases member
      · intro capture member; cases member
      · intro capture member; cases member
    | nominal name children =>
      simp only [inspect,Report.visit]
      have origins (root : Origin) : ∀ index, ∃ ref,
          some (.nominal ((none : Option Origin).getD root) name index) = some ref ∧ Path root ref := by
        intro index
        exact ⟨.nominal root name index,rfl,.nominal .root⟩
      split
      · split <;> (intro capture member; cases member)
      · split
        · split
          · intro capture member; cases member
          · split
            · exact rooted_supported known.1 (many_rooted state.context.state children _ _ 0 (origins _))
            · split
              · intro capture member; cases member
              · split
                · split
                  · intro capture member; cases member
                  · exact append_supported
                      (rooted_supported known.1 (many_rooted state.context.state children _ _ 0 (origins _)))
                      (rooted_supported known.2 (many_rooted state.context.state children _ _ 0 (origins _)))
                · intro capture member; cases member
        · intro capture member; cases member
    termination_by sizeOf query

  theorem many_missing_supported (state : State roles) (valid : Models state model) (queries : List Query)
      (bounds : List (Bounds state.context.state))
      (known : ∀ interval ∈ bounds, Endpoints context model budget state.context.state interval) :
      Supported context model budget (inspectMany state.context.state queries bounds (fun _ => none) offset) := by
    cases queries with
    | nil => cases bounds <;> simp [Supported,inspectMany]
    | cons query rest =>
      cases bounds with
      | nil => simp [Supported,inspectMany]
      | cons head tail =>
        simp only [inspectMany]
        exact append_supported (missing_supported state valid query head (known head (List.mem_cons_self ..)))
          (many_missing_supported state valid rest tail (fun interval member => known interval (List.mem_cons_of_mem _ member)))
    termination_by sizeOf queries
end

theorem inspect_supported (state : State roles) (valid : Models state model) (query : Query)
    (bounds : Bounds state.context.state) (origin : Option Origin)
    (retained : ∀ ref, origin = some ref → Bounded context model budget ref)
    (missing : origin = none → GeneralNominalInspectionOrigins.Constructor query →
      Endpoints context model budget state.context.state bounds) :
    Supported context model budget (inspect state.context.state query bounds origin) := by
  cases origin with
  | some origin => exact rooted_supported (retained origin rfl) (inspect_rooted state.context.state query bounds origin)
  | none =>
    cases query with
    | variables names =>
      intro capture member origin recorded
      simp only [inspect] at member
      obtain ⟨name,_,rfl⟩ := List.mem_map.mp member
      cases recorded
    | deferred => simp [Supported,inspect,block]
    | scalar | node | nominal => exact missing_supported state valid _ bounds (missing rfl trivial)

end Yulang.GeneralNominalFallbackReadback
