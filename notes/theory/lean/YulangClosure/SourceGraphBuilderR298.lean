import YulangClosure.SourceGraphRegistrationR297

/-!
R298: the exact remaining second-pass Call closure seam.

The existing raw source inventory is NOT a typed declaration-graph supplier.
The constructive result below registers every edge of the actual `installCall`
root, including every arm, and locates the raw App's original occurrence.
It then characterizes closure of the whole generated graph by exactly the old
and region-internal edges; root-edge obligations are discharged by construction.
The conditional noninterference application exposes these remaining premises.
The final nested-reference obstruction shows why root registration alone cannot
be promoted to graph closure, even though all six regions were installed.
No source typing, complete contract authenticity, recursive target resolution,
whole substitution legality, or full IF theorem is asserted here.
-/
namespace YulangClosure.SourceGraphBuilderR298

open OriginalSource SourceSignatureConstruction SourceContributionConstruction
open SourceDeclarationRetentionR295 SourceDeclarationNoninterferenceR296

variable {Joint : Type}

/-- Every generated phase address denotes the actual retained region node.
This covers all six phases and the entire original finite arm list. -/
theorem phase_target_registered (g : Graph Joint) (context : Context) (mark : Mark)
    (callee argument : Source .expression) (regions : CallRegions Joint)
    (locals : List (Introduction Joint)) (result : Catalogue Joint)
    (phase : Phase) (child : Nat)
    (found : (regions.addresses g.nodes.length).at phase = some child) :
    ∃ target, (installCall g context mark callee argument regions locals result).node child = some target := by
  cases phase with
  | callee | wholeArgument | calleeReturn | receiver | returned | future =>
      simp only [CallRegions.addresses, CallNodes.at, Option.some.injEq] at found
      subst child
      first
      | exact ⟨_, installed_region_node g context mark callee argument regions locals result 0 _ rfl⟩
      | exact ⟨_, installed_region_node g context mark callee argument regions locals result 1 _ rfl⟩
      | exact ⟨_, installed_region_node g context mark callee argument regions locals result 2 _ rfl⟩
      | exact ⟨_, installed_region_node g context mark callee argument regions locals result 3 _ rfl⟩
      | exact ⟨_, installed_region_node g context mark callee argument regions locals result 4 _ rfl⟩
      | exact ⟨_, installed_region_node g context mark callee argument regions locals result 5 _ rfl⟩
  | arm i =>
      simp only [CallRegions.addresses, CallNodes.at, List.getElem?_map] at found
      obtain ⟨pair, pairFound, equal⟩ := Option.map_eq_some_iff.mp found
      have bound := (List.getElem?_eq_some_iff.mp pairFound).1
      have index : pair.2 = i := by
        have mem := List.getElem?_eq_some_iff.mp pairFound
        simpa using congrArg Prod.snd mem.2.symm
      have armFound : regions.arms[i]? = some pair.1 := by
        have h := congrArg (Option.map Prod.fst) pairFound
        simpa using h
      subst child
      rw [index]
      exact ⟨pair.1, installed_call_arm g context mark callee argument regions locals result i pair.1 armFound⟩

/-- Root lookup and all its target lookups are generated, never supplied. -/
theorem call_root_targets (g : Graph Joint) (context : Context) (mark : Mark)
    (callee argument : Source .expression) (regions : CallRegions Joint)
    (locals : List (Introduction Joint)) (result : Catalogue Joint)
    (node : Node Joint) (step : SourceSignatureConstruction.Step) (child : Nat)
    (found : (installCall g context mark callee argument regions locals result).node
      (callIndex g regions) = some node)
    (edge : SourceEdge node step child) :
    ∃ target, (installCall g context mark callee argument regions locals result).node child = some target := by
  rw [installed_call_node] at found
  cases found
  cases edge with
  | call found => exact phase_target_registered g context mark callee argument regions locals result _ _ found

/-- Exact partition of a lookup in the constructed table: an old node, an
original region (including an arm), or the generated Call root. -/
theorem installed_lookup_cases (g : Graph Joint) (context : Context) (mark : Mark)
    (callee argument : Source .expression) (regions : CallRegions Joint)
    (locals : List (Introduction Joint)) (result : Catalogue Joint)
    (i : Nat) (node : Node Joint)
    (found : (installCall g context mark callee argument regions locals result).node i = some node) :
    g.node i = some node ∨
      (∃ offset, i = g.nodes.length + offset ∧ regions.nodes[offset]? = some node) ∨
      i = callIndex g regions := by
  by_cases old : i < g.nodes.length
  · exact Or.inl ((installed_old_node g context mark callee argument regions locals result i old) ▸ found)
  · by_cases region : i < g.nodes.length + regions.nodes.length
    · right; left
      refine ⟨i - g.nodes.length, by omega, ?_⟩
      change ((g.nodes ++ regions.nodes) ++ [_])[i]? = some node at found
      rw [List.getElem?_append_left (by simpa using region), List.getElem?_append_right (by omega)] at found
      exact found
    · right; right
      have bound := (List.getElem?_eq_some_iff.mp found).1
      simp only [installCall, List.length_append, List.length_singleton] at bound
      unfold callIndex
      omega

/-- Exact missing input, as a diagnostic proposition, not a source supplier.
The generated root is deliberately absent: its edges were already solved. -/
def RemainingTargets (g : Graph Joint) (context : Context) (mark : Mark)
    (callee argument : Source .expression) (regions : CallRegions Joint)
    (locals : List (Introduction Joint)) (result : Catalogue Joint) : Prop :=
  let built := installCall g context mark callee argument regions locals result
  (∀ i node step child, g.node i = some node → SourceEdge node step child →
    ∃ target, built.node child = some target) ∧
  (∀ (offset : Nat) node step child, regions.nodes[offset]? = some node → SourceEdge node step child →
    ∃ target, built.node child = some target)

theorem installed_closed_iff (g : Graph Joint) (context : Context) (mark : Mark)
    (callee argument : Source .expression) (regions : CallRegions Joint)
    (locals : List (Introduction Joint)) (result : Catalogue Joint) :
    ClosedPrefix (installCall g context mark callee argument regions locals result)
      (installCall g context mark callee argument regions locals result).nodes.length ↔
    RemainingTargets g context mark callee argument regions locals result := by
  constructor
  · intro closed
    have target (i node step child) (found : (installCall g context mark callee argument regions locals result).node i = some node)
        (edge : SourceEdge node step child) :
        ∃ target, (installCall g context mark callee argument regions locals result).node child = some target := by
      have bound := closed i node step child (List.getElem?_eq_some_iff.mp found).1 found edge
      exact ⟨_, List.getElem?_eq_some_iff.mpr ⟨bound, rfl⟩⟩
    constructor
    · intro i node step child found edge
      apply target i node step child _ edge
      rw [installed_old_node g context mark callee argument regions locals result i (List.getElem?_eq_some_iff.mp found).1]
      exact found
    · intro offset node step child found edge
      exact target _ node step child
        (installed_region_node g context mark callee argument regions locals result offset node found) edge
  · intro remaining
    apply closed_of_registered_targets
    intro i node step child found edge
    rcases installed_lookup_cases g context mark callee argument regions locals result i node found with old | region | root
    · exact remaining.1 i node step child old edge
    · obtain ⟨offset, _, region⟩ := region
      exact remaining.2 offset node step child region edge
    · subst i
      exact call_root_targets g context mark callee argument regions locals result node step child found edge

/-- A closed old graph needs no fresh old-edge premise. Only the original
region-internal edges remain, including references back into the old graph,
forward into any simultaneously allocated region, or to the Call root. -/
theorem remaining_of_closed_old (g : Graph Joint) (context : Context) (mark : Mark)
    (callee argument : Source .expression) (regions : CallRegions Joint)
    (locals : List (Introduction Joint)) (result : Catalogue Joint)
    (closed : ClosedPrefix g g.nodes.length)
    (regionTargets : ∀ (offset : Nat) node step child,
      regions.nodes[offset]? = some node → SourceEdge node step child →
      ∃ target, (installCall g context mark callee argument regions locals result).node child = some target) :
    RemainingTargets g context mark callee argument regions locals result := by
  refine ⟨?_, regionTargets⟩
  intro i node step child found edge
  have bound := closed i node step child (List.getElem?_eq_some_iff.mp found).1 found edge
  refine ⟨g.nodes[child], ?_⟩
  rw [installed_old_node g context mark callee argument regions locals result child bound]
  exact List.getElem?_eq_some_iff.mpr ⟨bound, rfl⟩

/-- Applied R296 parent edge, explicitly CONDITIONAL on old and region-internal
resolution. No authenticity of supplied complete regions is manufactured. -/
theorem installed_original_graph_iff (g : Graph Joint) (context : Context) (mark : Mark)
    (callee argument : Source .expression) (regions : CallRegions Joint)
    (locals : List (Introduction Joint)) (result : Catalogue Joint)
    (remaining : RemainingTargets g context mark callee argument regions locals result)
    (d : DeclarationData Joint)
    (relations : Relations (installCall g context mark callee argument regions locals result))
    (operators : Operators (installCall g context mark callee argument regions locals result))
    {i w n p} (inside : i < (installCall g context mark callee argument regions locals result).nodes.length) :
    Nonempty (Contribution
      (install (installCall g context mark callee argument regions locals result) d)
      (localRelations _ d (lift_relations _ d relations)) (lift_operators _ d operators) i w n p) ↔
    Nonempty (DeclContribution (installCall g context mark callee argument regions locals result)
      relations operators i w n p) :=
  original_graph_iff _ d relations operators
    ((installed_closed_iff g context mark callee argument regions locals result).mpr remaining) inside

/-- The real raw-App inventory supplies the occurrence, and installation
supplies all graph-root outgoing targets. These two facts do NOT authenticate
six region meanings or equate their children with source subderivations. -/
theorem source_application_root_registered (origin : Declaration) (g : Graph Joint)
    (context : Context) (site : Site) (callee argument : Source .expression)
    (regions : CallRegions Joint) (locals : List (Introduction Joint)) (result : Catalogue Joint) :
    (∃ (index : Nat) (row : SourceGraphRegistrationR297.Row),
      (SourceGraphRegistrationR297.sourceInventory origin context (.app ⟨site, none⟩ callee argument))[index]? = some row ∧
      row.callOwner = some (.application site context callee.site argument.site)) ∧
    (∀ node step child,
      (installCall g context ⟨site, none⟩ callee argument regions locals result).node
        (callIndex g regions) = some node → SourceEdge node step child →
      ∃ target, (installCall g context ⟨site, none⟩ callee argument regions locals result).node child = some target) :=
  ⟨SourceGraphRegistrationR297.source_application_registered origin context site callee argument,
    call_root_targets g context ⟨site, none⟩ callee argument regions locals result⟩

/-- A checkable failure certificate at an actual retained reference node.
Merely registering its containing region cannot repair this missing target. -/
theorem unresolved_region_reference (g : Graph Joint) (context : Context) (mark : Mark)
    (callee argument : Source .expression) (regions : CallRegions Joint)
    (locals : List (Introduction Joint)) (result : Catalogue Joint)
    (offset site root substitution : Nat) (referenceResult : Catalogue Joint)
    (found : regions.nodes[offset]? = some (.reference site root substitution referenceResult))
    (outside : (installCall g context mark callee argument regions locals result).nodes.length ≤ root) :
    ¬ ClosedPrefix (installCall g context mark callee argument regions locals result)
      (installCall g context mark callee argument regions locals result).nodes.length := by
  intro closed
  have registered := installed_region_node g context mark callee argument regions locals result
    offset _ found
  have bound := closed _ _ _ _ (List.getElem?_eq_some_iff.mp registered).1 registered SourceEdge.reference
  omega

/-- Countermodel family for the *unqualified API* claim that complete root
allocation implies complete edge closure. No claim these unresolved references
are emitted by authentic source resolution. No catalogue or license is invented. -/
def unresolvedRegions (g : Graph Joint) (site substitution : Nat) (result : Catalogue Joint) : CallRegions Joint :=
  let dangling := Node.reference site (g.nodes.length + 7) substitution result
  ⟨dangling, dangling, dangling, dangling, dangling, dangling, []⟩

theorem root_registration_does_not_close_regions (g : Graph Joint) (context : Context) (mark : Mark)
    (callee argument : Source .expression) (locals : List (Introduction Joint))
    (result : Catalogue Joint) (substitution : Nat) :
    let regions := unresolvedRegions g mark.site substitution result
    (∀ node step child,
      (installCall g context mark callee argument regions locals result).node
        (callIndex g regions) = some node → SourceEdge node step child →
      ∃ target, (installCall g context mark callee argument regions locals result).node child = some target) ∧
    ¬ ClosedPrefix (installCall g context mark callee argument regions locals result)
      (installCall g context mark callee argument regions locals result).nodes.length := by
  dsimp only
  constructor
  · exact call_root_targets g context mark callee argument _ locals result
  · apply unresolved_region_reference g context mark callee argument _ locals result 0
      mark.site (g.nodes.length + 7) substitution result rfl
    simp [installCall, unresolvedRegions, CallRegions.nodes]

end YulangClosure.SourceGraphBuilderR298
