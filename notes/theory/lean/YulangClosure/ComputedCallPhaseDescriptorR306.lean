import YulangClosure.ComputedCallUnionRealizationR293

/-!
R306: constructive registration at the existing R293 contribution consumer.

This constructs a fresh graph node rather than identifying a pre-existing Call
node with an alternative. It preserves the complete old graph, substitutions,
local contracts, licenses and relation witnesses, even at overlapping sites.
Its source/arm catalogues are the ORIGINAL R293 branch clauses, not EI clauses
invented for opaque Sorts.Interface. An authentic source child and independently
licensed arm child remain separate inputs. No caller-image, synthesis endpoint,
Checking proof or logical admission is changed.

LIMIT: EI-Form/EI-All §§2–4 and GR1–GR3 require typed phase operands and an actual
complete-computation descriptor registration. Original Inputs exposes neither
an EI constructor nor a clause-registration operation. This graph addition is
therefore not identified with DefineResultView(c), and does not close R159.
-/
namespace YulangClosure.ComputedCallPhaseDescriptorR306

open OriginalSource OriginalSourceInterpretation OriginalSourceEnvironment
open SourceSignatureConstruction SourceContributionConstruction
open ComputedCallUnionRealizationR293

variable {Joint : Type} {s : Sorts} {View : Type}

/-- A fresh graph position for an existing typed node. The separate root
registration namespace is preserved in FULL; it is not a node-address space.
This does not create a source description record or assume a semantic equation. -/
def appendNode (graph : Graph Joint) (node : Node Joint) : Graph Joint :=
  { graph with nodes := graph.nodes ++ [node] }

theorem appended_node (graph : Graph Joint) (node : Node Joint) :
    (appendNode graph node).node graph.nodes.length = some node := by
  simp [appendNode, Graph.node]

theorem appended_registration (graph : Graph Joint) (node : Node Joint) :
    (appendNode graph node).registration = graph.registration := rfl

theorem original_node_retained (graph : Graph Joint) (added : Node Joint)
    (index : Nat) (node : Node Joint) (found : graph.node index = some node) :
    (appendNode graph added).node index = some node := by
  have bound := (List.getElem?_eq_some_iff.mp found).1
  change (graph.nodes ++ [added])[index]? = some node
  rw [List.getElem?_append_left bound]
  exact found


theorem whole_action_retained (graph : Graph Joint) (added : Node Joint)
    (route : List SourceSignatureConstruction.Step) (whole : Joint) :
    routeAction (appendNode graph added) route whole = routeAction graph route whole := rfl

/-- Existing declaration-local relations are reused verbatim. Graph extension
changes no reference/rename whole action and manufactures no law. -/
def appendRelations (graph : Graph Joint) (added : Node Joint)
    (old : Relations graph) : Relations (appendNode graph added) where
  alternative := old.alternative
  conjunction := old.conjunction
  forward := old.forward

theorem append_provenance (graph : Graph Joint) (added : Node Joint)
    {index : Nat} {intro : Introduction Joint} {route : List SourceSignatureConstruction.Step} :
    PortProv graph index intro route → PortProv (appendNode graph added) index intro route
  | .introduction found introduced =>
      .introduction (original_node_retained graph added _ _ found) introduced
  | .contextual found edge child =>
      .contextual (original_node_retained graph added _ _ found) edge
        (append_provenance graph added child)

/-- The whole original packet and its SAME primitive/license witness survive.
The original route and introduction are never searched or reconstructed. -/
def appendLeaf (graph : Graph Joint) (added : Node Joint)
    {index : Nat} {whole : Joint} (old : LeafLicensedField graph index whole) :
    LeafLicensedField (appendNode graph added) index whole :=
  ⟨⟨old.occurrence.intro, old.occurrence.route,
    append_provenance graph added old.occurrence.provenance⟩,
    old.port, old.packet, old.license⟩

def appendField (graph : Graph Joint) (added : Node Joint)
    {node : Node Joint} {whole : Joint} :
    OperatorField graph node whole → OperatorField (appendNode graph added) node whole
  | .localField intro introduced packet license => .localField intro introduced packet license
  | .antecedent step child edge field => .antecedent step child edge (appendLeaf graph added field)

def appendContract (graph : Graph Joint) (added : Node Joint)
    {node : Node Joint} (old : OperatorContract graph node) :
    OperatorContract (appendNode graph added) node where
  Evidence := old.Evidence
  Field := old.Field
  governed := fun whole packet evidence field =>
    appendField graph added (old.governed whole packet evidence field)

def appendOperators (graph : Graph Joint) (added : Node Joint)
    (old : Operators graph) : Operators (appendNode graph added) where
  image := fun atSite operator operands locals result =>
    appendContract graph added (old.image atSite operator operands locals result)
  call := fun context mark callee argument nodes locals result =>
    appendContract graph added (old.call context mark callee argument nodes locals result)

/-- Total structural preservation, including old alternatives at the SAME site
and operator contracts with arbitrary dependent governed-field families. -/
def appendContribution (graph : Graph Joint) (added : Node Joint)
    (old : Relations graph) (operators : Operators graph)
    {index : Nat} {whole : Joint} {node : Node Joint} {packet : Packet node.catalogue whole} :
    DeclContribution graph old operators index whole node packet →
      DeclContribution (appendNode graph added)
        (appendRelations graph added old) (appendOperators graph added operators)
        index whole node packet
  | .primitive found packet license =>
      .primitive (original_node_retained graph added _ _ found) packet license
  | .alternativeLeft found child output related =>
      .alternativeLeft (original_node_retained graph added _ _ found)
        (appendContribution graph added old operators child) output related
  | .alternativeRight found child output related =>
      .alternativeRight (original_node_retained graph added _ _ found)
        (appendContribution graph added old operators child) output related
  | .conjunction found first second output related =>
      .conjunction (original_node_retained graph added _ _ found)
        (appendContribution graph added old operators first)
        (appendContribution graph added old operators second) output related
  | .image found output evidence =>
      .image (original_node_retained graph added _ _ found) output evidence
  | .call found output evidence =>
      .call (original_node_retained graph added _ _ found) output evidence
  | .forward found step child output related =>
      .forward (original_node_retained graph added _ _ found) step
        (appendContribution graph added old operators child) output related

theorem original_contribution_retained (graph : Graph Joint) (added : Node Joint)
    (old : Relations graph) (operators : Operators graph)
    {index : Nat} {whole : Joint} {node : Node Joint} {packet : Packet node.catalogue whole}
    (proof : DeclContribution graph old operators index whole node packet) :
    Nonempty (DeclContribution (appendNode graph added)
      (appendRelations graph added old) (appendOperators graph added operators)
      index whole node packet) := ⟨appendContribution graph added old operators proof⟩

/-- Existing R293 result catalogue at a genuinely fresh graph address. Source
and original arm endpoints are supplied by their typed owners, not guessed from
callableImage, source execution, row shape, or equal descriptor denotations. -/
def installUnion (inputs : Inputs s) (state : Decoded s View) (scope : List Binder)
    (graph : Graph (RawObservation s)) (site : Site) (left right : Nat)
    (source : Endpoint) (arms : List Endpoint) : Graph (RawObservation s) :=
  appendNode graph (unionNode inputs state scope site left right source arms)

theorem union_readback (inputs : Inputs s) (state : Decoded s View) (scope : List Binder)
    (graph : Graph (RawObservation s)) (site : Site) (left right : Nat)
    (source : Endpoint) (arms : List Endpoint) :
    (installUnion inputs state scope graph site left right source arms).node graph.nodes.length =
      some (unionNode inputs state scope site left right source arms) :=
  appended_node graph _

theorem union_compiled_readback (inputs : Inputs s) (state : Decoded s View) (scope : List Binder)
    (graph : Graph (RawObservation s)) (site : Site) (left right : Nat)
    (source : Endpoint) (arms : List Endpoint) :
    (build (installUnion inputs state scope graph site left right source arms))[graph.nodes.length]? =
      some (compileNode (unionNode inputs state scope site left right source arms)) := by
  rw [build_lookup, union_readback]
  rfl

/-- The same incoming source contribution is passed through actual R293
sourceContribution. Its former desired-node lookup is now computed. The branch
catalogue equation is STILL genuine independent typed input, not inferred from
an original Call constructor or a source-typing success. -/
theorem source_contribution_registered (inputs : Inputs s) (state : Decoded s View)
    (scope : List Binder) (graph : Graph (RawObservation s)) (old : Relations graph)
    (operators : Operators graph) (site : Site) (left right : Nat)
    (source : Endpoint) (arms : List Endpoint) (raw : RawObservation s)
    (childNode : Node (RawObservation s))
    (sameCatalogue : childNode.catalogue = branchCatalogue inputs state scope source)
    (packet : Packet (branchCatalogue inputs state scope source) raw)
    (child : DeclContribution graph old operators left raw childNode (sameCatalogue ▸ packet)) :
    let added := unionNode inputs state scope site left right source arms
    let installed := installUnion inputs state scope graph site left right source arms
    Nonempty (DeclContribution installed
      (relations installed (appendRelations graph added old) inputs state scope site source arms)
      (appendOperators graph added operators) graph.nodes.length raw added
      (injectSource inputs state scope source arms packet)) := by
  dsimp only
  let added := unionNode inputs state scope site left right source arms
  let installed := installUnion inputs state scope graph site left right source arms
  have retained := appendContribution graph added old operators child
  have tagged := retainContribution installed (appendRelations graph added old)
    inputs state scope site source arms (appendOperators graph added operators) retained
  exact ⟨sourceContribution inputs state scope site source arms installed
    (appendRelations graph added old) (appendOperators graph added operators)
    graph.nodes.length left right raw childNode sameCatalogue packet
    (union_readback inputs state scope graph site left right source arms) tagged⟩

/-- An independent arm child uses its OWN packet and law. Source membership
supplies neither this child nor its license. Fin keeps every original duplicate
arm position, and no non-overlap hypothesis is imposed on endpoints or sites. -/
theorem arm_contribution_registered (inputs : Inputs s) (state : Decoded s View)
    (scope : List Binder) (graph : Graph (RawObservation s)) (old : Relations graph)
    (operators : Operators graph) (site : Site) (left right : Nat)
    (source : Endpoint) (arms : List Endpoint) (raw : RawObservation s)
    (childNode : Node (RawObservation s))
    (sameCatalogue : childNode.catalogue = armsCatalogue inputs state scope arms)
    (packet : Packet (armsCatalogue inputs state scope arms) raw)
    (child : DeclContribution graph old operators right raw childNode (sameCatalogue ▸ packet)) :
    let added := unionNode inputs state scope site left right source arms
    let installed := installUnion inputs state scope graph site left right source arms
    Nonempty (DeclContribution installed
      (relations installed (appendRelations graph added old) inputs state scope site source arms)
      (appendOperators graph added operators) graph.nodes.length raw added
      (injectArm inputs state scope source arms packet)) := by
  dsimp only
  let added := unionNode inputs state scope site left right source arms
  let installed := installUnion inputs state scope graph site left right source arms
  have retained := appendContribution graph added old operators child
  have tagged := retainContribution installed (appendRelations graph added old)
    inputs state scope site source arms (appendOperators graph added operators) retained
  exact ⟨armContribution inputs state scope site source arms installed
    (appendRelations graph added old) (appendOperators graph added operators)
    graph.nodes.length left right raw childNode sameCatalogue packet
    (union_readback inputs state scope graph site left right source arms) tagged⟩

end YulangClosure.ComputedCallPhaseDescriptorR306
