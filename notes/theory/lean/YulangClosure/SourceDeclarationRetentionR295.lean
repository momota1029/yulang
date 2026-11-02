import YulangClosure.ComputedCallSourceSupplierR294

/-!
R295: input-qualified IF-Insert/IF-Use retention and R293 consumer application.

Authority: call-source-interface-definition §§2–4 and native-signature-formation
§2. Original typed declarations, scopes, substitutions and local semantic data
are inputs. This file constructs their contextual placement, not their truth or
their extraction from raw source. In particular an opaque decoded interface is
NOT identified with EvalInvoke. The missing EI staged interpretation remains
open at computed-call-result-constructor §§2–5 / GR1–GR4.
-/
namespace YulangClosure.SourceDeclarationRetentionR295

open OriginalSource OriginalSourceInterpretation OriginalSourceEnvironment
open OriginalSourceChecking SourceSignatureConstruction SourceContributionConstruction

variable {Joint : Type} {s : Sorts} {View : Type}

/-- Actual original declaration data, before any observation or desired use.
`clause` can be ANY existing constructor, including a recursive graph reference,
composite declaration, or an operator with independent local semantics. The
complete pre-existing root graph is retained separately by `install`.
Authentication/extraction of these original data is an independent source duty.
-/
structure DeclarationData (Joint : Type) where
  root : Nat
  declaration : Nat
  reference : Site
  substitution : Nat
  clause : Node Joint

/-- Original scope and slot addresses are retained; one whole substitution
acts on all packet fields together. No license or membership is added. -/
def pullback (catalogue : Catalogue Joint) (action : Joint → Joint) : Catalogue Joint where
  Port := catalogue.Port
  Packet := fun whole port => catalogue.Packet (action whole) port
  scope := catalogue.scope
  sharedSlot := catalogue.sharedSlot

def useCatalogue (original : Graph Joint) (data : DeclarationData Joint) : Catalogue Joint :=
  pullback data.clause.catalogue (original.substitution data.substitution)

def usePacket (original : Graph Joint) (data : DeclarationData Joint) (whole : Joint)
    (packet : Packet data.clause.catalogue (original.substitution data.substitution whole)) :
    Packet (useCatalogue original data) whole := ⟨packet.port, packet.value⟩

def insertionNode (original : Graph Joint) (data : DeclarationData Joint) : Node Joint :=
  .insertion data.root data.declaration original.nodes.length data.clause.catalogue

def referenceNode (original : Graph Joint) (data : DeclarationData Joint) : Node Joint :=
  .reference data.reference (original.nodes.length + 1) data.substitution
    (useCatalogue original data)

/-- Registration precedes proof use. Old graph nodes and all their edges,
including cycles and repeated sites, remain verbatim. -/
def install (original : Graph Joint) (data : DeclarationData Joint) : Graph Joint :=
  { original with nodes := original.nodes ++
      [data.clause, insertionNode original data, referenceNode original data] }

theorem original_node_retained (original : Graph Joint) (data : DeclarationData Joint)
    (index : Nat) (bound : index < original.nodes.length) :
    (install original data).node index = original.node index := by
  exact List.getElem?_append_left bound

theorem clause_lookup (original : Graph Joint) (data : DeclarationData Joint) :
    (install original data).node original.nodes.length = some data.clause := by
  simp [install, Graph.node]

theorem insertion_lookup (original : Graph Joint) (data : DeclarationData Joint) :
    (install original data).node (original.nodes.length + 1) =
      some (insertionNode original data) := by
  simp [install, Graph.node]

theorem reference_lookup (original : Graph Joint) (data : DeclarationData Joint) :
    (install original data).node (original.nodes.length + 2) =
      some (referenceNode original data) := by
  simp [install, Graph.node]

theorem scoped_readout (original : Graph Joint) (data : DeclarationData Joint)
    (whole : Joint) (port : (useCatalogue original data).Port) :
    (useCatalogue original data).Packet whole port =
      data.clause.catalogue.Packet (original.substitution data.substitution whole) port := rfl

theorem scope_retained (original : Graph Joint) (data : DeclarationData Joint) :
    (useCatalogue original data).scope = data.clause.catalogue.scope := rfl

theorem whole_substitution_retained (original : Graph Joint) (data : DeclarationData Joint)
    (whole : Joint) :
    (Step.reference data.reference (original.nodes.length + 1) data.substitution).action
      (install original data) whole = original.substitution data.substitution whole := rfl

/-- These two actual contextual injections preserve the complete packet. They
are not arbitrary original primitive licenses or arbitrary reference maps. -/
inductive RetainedForward (original : Graph Joint) (data : DeclarationData Joint) :
    (step : SourceSignatureConstruction.Step) → (whole : Joint) → {child result : Catalogue Joint} →
      Packet child (step.action (install original data) whole) → Packet result whole → Type where
  | insertion (whole : Joint) (packet : Packet data.clause.catalogue whole) :
      RetainedForward original data (.insertion data.root data.declaration) whole packet packet
  | reference (whole : Joint)
      (packet : Packet data.clause.catalogue (original.substitution data.substitution whole)) :
      RetainedForward original data
        (.reference data.reference (original.nodes.length + 1) data.substitution)
        whole packet (usePacket original data whole packet)

def retainedRelations (original : Graph Joint) (data : DeclarationData Joint)
    (old : Relations (install original data)) : Relations (install original data) :=
  { old with forward := fun step whole {_ _} packet output =>
      (Sum (old.forward step whole packet output)
        (RetainedForward original data step whole packet output)) }

/-- Every old derivation survives, even at overlapping source sites. No old
relation witness is overwritten by the two new contextual injections. -/
def retainContribution (original : Graph Joint) (data : DeclarationData Joint)
    (old : Relations (install original data)) (operators : Operators (install original data))
    {index : Nat} {whole : Joint} {node : Node Joint} {packet : Packet node.catalogue whole} :
    DeclContribution (install original data) old operators index whole node packet →
      DeclContribution (install original data) (retainedRelations original data old)
        operators index whole node packet
  | .primitive found packet license => .primitive found packet license
  | .alternativeLeft found child output related =>
      .alternativeLeft found (retainContribution original data old operators child) output related
  | .alternativeRight found child output related =>
      .alternativeRight found (retainContribution original data old operators child) output related
  | .conjunction found first second output related =>
      .conjunction found (retainContribution original data old operators first)
        (retainContribution original data old operators second) output related
  | .image found output evidence => .image found output evidence
  | .call found output evidence => .call found output evidence
  | .forward found step child output related =>
      .forward found step (retainContribution original data old operators child) output (.inl related)

/-- IF-Insert followed by IF-Use. The independent original contribution is
used at the actual substituted whole row, once; all future/provider fields
inside its dependent packet stay together. -/
def contribution_at_use (original : Graph Joint) (data : DeclarationData Joint)
    (old : Relations (install original data)) (operators : Operators (install original data))
    (whole : Joint)
    (packet : Packet data.clause.catalogue (original.substitution data.substitution whole))
    (child : DeclContribution (install original data) (retainedRelations original data old)
      operators original.nodes.length (original.substitution data.substitution whole)
      data.clause packet) :
    DeclContribution (install original data) (retainedRelations original data old) operators
      (original.nodes.length + 2) whole (referenceNode original data)
      (usePacket original data whole packet) := by
  apply DeclContribution.forward (reference_lookup original data) Forward.reference
  · apply DeclContribution.forward (insertion_lookup original data) Forward.insertion child packet
    exact Sum.inr (RetainedForward.insertion _ packet)
  · exact Sum.inr (RetainedForward.reference whole packet)

def original_contribution_at_use (original : Graph Joint) (data : DeclarationData Joint)
    (old : Relations (install original data)) (operators : Operators (install original data))
    (whole : Joint)
    (packet : Packet data.clause.catalogue (original.substitution data.substitution whole))
    (child : DeclContribution (install original data) old operators original.nodes.length
      (original.substitution data.substitution whole) data.clause packet) :
    DeclContribution (install original data) (retainedRelations original data old) operators
      (original.nodes.length + 2) whole (referenceNode original data)
      (usePacket original data whole packet) :=
  contribution_at_use original data old operators whole packet
    (retainContribution original data old operators child)

theorem use_keeps_owner (original : Graph Joint) (data : DeclarationData Joint)
    (old : Relations (install original data)) (operators : Operators (install original data))
    (whole : Joint)
    (packet : Packet data.clause.catalogue (original.substitution data.substitution whole))
    (child : DeclContribution (install original data) (retainedRelations original data old)
      operators original.nodes.length (original.substitution data.substitution whole) data.clause packet)
    (field : child.Projection) :
    ((contribution_at_use original data old operators whole packet child).project field).occurrence.owner =
      (child.project field).occurrence.owner := rfl

theorem use_keeps_license (original : Graph Joint) (data : DeclarationData Joint)
    (old : Relations (install original data)) (operators : Operators (install original data))
    (whole : Joint)
    (packet : Packet data.clause.catalogue (original.substitution data.substitution whole))
    (child : DeclContribution (install original data) (retainedRelations original data old)
      operators original.nodes.length (original.substitution data.substitution whole) data.clause packet)
    (field : child.Projection) :
    ((contribution_at_use original data old operators whole packet child).project field).license =
      (child.project field).license := rfl

/-- Concrete primitive instance: lookup and both contextual transports are
constructed from the independently supplied original license. No final
DeclContribution, source typing, or desired enclosing applicability is assumed.
-/
def primitive_at_use (original : Graph Joint) (root declaration : Nat) (reference : Site)
    (substitution : Nat) (intro : Introduction Joint)
    (old : Relations (install original ⟨root, declaration, reference, substitution, .primitive intro⟩))
    (operators : Operators (install original ⟨root, declaration, reference, substitution, .primitive intro⟩))
    (whole : Joint) (packet : Packet intro.catalogue (original.substitution substitution whole))
    (license : intro.License (original.substitution substitution whole) packet.port packet.value) :
    let data : DeclarationData Joint := ⟨root, declaration, reference, substitution, .primitive intro⟩
    DeclContribution (install original data) (retainedRelations original data old) operators
      (original.nodes.length + 2) whole (referenceNode original data)
      (usePacket original data whole packet) :=
  contribution_at_use original _ old operators whole packet
    (.primitive (clause_lookup original _) packet license)

/-- The GENERAL original Call constructor, with complete six-region and arm
inputs. All local operator semantic Evidence remains independently required.
There is no successful source execution, endpoint inclusion, or q-c truth here.
-/
structure CallData (Joint : Type) where
  context : Context
  mark : Mark
  callee : Source .expression
  argument : Source .expression
  regions : CallRegions Joint
  locals : List (Introduction Joint)
  result : Catalogue Joint

def callGraph (original : Graph Joint) (data : CallData Joint) : Graph Joint :=
  installCall original data.context data.mark data.callee data.argument data.regions data.locals data.result

def owner (data : CallData Joint) : CallOwner :=
  .application data.mark.site data.context data.callee.site data.argument.site

/-- q-c is a source-address label. It carries no descriptor interpretation. -/
def resultLabel (data : CallData Joint) : Site × Unit := (data.mark.site, ())

theorem call_lookup (original : Graph Joint) (data : CallData Joint) :
    (callGraph original data).node (callIndex original data.regions) =
      some (.call data.context data.mark data.callee data.argument
        (data.regions.addresses original.nodes.length) data.locals data.result) :=
  installed_call_node original data.context data.mark data.callee data.argument data.regions data.locals data.result

theorem every_phase_retained (original : Graph Joint) (data : CallData Joint)
    (phase : Phase) (child : Nat)
    (found : (data.regions.addresses original.nodes.length).at phase = some child) :
    (Step.call data.mark.site phase, child) ∈
      (compileNode (.call data.context data.mark data.callee data.argument
        (data.regions.addresses original.nodes.length) data.locals data.result)).edges :=
  source_edge_exact.mp (.call found)

theorem every_arm_retained (original : Graph Joint) (data : CallData Joint)
    (index : Nat) (arm : Node Joint) (found : data.regions.arms[index]? = some arm) :
    (callGraph original data).node (original.nodes.length + 6 + index) = some arm :=
  installed_call_arm original data.context data.mark data.callee data.argument data.regions
    data.locals data.result index arm found

/-- The same general constructor also accepts R294's nested computed source.
The source registry, rather than an assumed owner relation, supplies its owner.
This example is not used to restrict any preceding quantifier. -/
def computedInstance (data : CallData Joint) (context : Context) (f x y : Name) : CallData Joint :=
  { data with
    context := context
    mark := ⟨4, none⟩
    callee := .app ⟨2, none⟩ (.name ⟨0, none⟩ f) (.name ⟨1, none⟩ x)
    argument := .name ⟨3, none⟩ y }

theorem computed_owner_authentic (data : CallData Joint) (context : Context) (f x y : Name) :
    owner (computedInstance data context f x y) ∈
      sourceCallOwners context (ComputedCallSourceSupplierR294.computedSource f x y) :=
  ComputedCallSourceSupplierR294.computed_outer_call_registered context f x y

namespace Selected

open ComputedCallUnionRealizationR293

/-- The selected R293 union is appended to the unchanged original graph.
Source/arm indices refer to their actual registered declarations. The original
result target is not written by this construction. -/
def graph (original : Graph (RawObservation s)) (inputs : Inputs s) (state : Decoded s View)
    (scope : List Binder) (site : Site) (source : Endpoint) (arms : List Endpoint)
    (left right : Nat) : Graph (RawObservation s) :=
  { original with nodes := original.nodes ++ [unionNode inputs state scope site left right source arms] }

theorem union_lookup (original : Graph (RawObservation s)) (inputs : Inputs s) (state : Decoded s View)
    (scope : List Binder) (site : Site) (source : Endpoint) (arms : List Endpoint) (left right : Nat) :
    (graph original inputs state scope site source arms left right).node original.nodes.length =
      some (unionNode inputs state scope site left right source arms) := by
  simp [graph, Graph.node]

/-- Consumes the genuine scoped source declaration's contribution. The exact
catalogue readout remains explicit: IF incidence alone cannot justify it. -/
def from_source (original : Graph (RawObservation s)) (inputs : Inputs s) (state : Decoded s View)
    (scope : List Binder) (site : Site) (source : Endpoint) (arms : List Endpoint) (left right : Nat)
    (old : Relations (graph original inputs state scope site source arms left right))
    (operators : Operators (graph original inputs state scope site source arms left right))
    (raw : RawObservation s) (node : Node (RawObservation s))
    (readout : node.catalogue = branchCatalogue inputs state scope source)
    (packet : Packet (branchCatalogue inputs state scope source) raw)
    (child : DeclContribution (graph original inputs state scope site source arms left right)
      (relations _ old inputs state scope site source arms) operators left raw node (readout ▸ packet)) :
    DeclContribution (graph original inputs state scope site source arms left right)
      (relations _ old inputs state scope site source arms) operators original.nodes.length raw
      (unionNode inputs state scope site left right source arms)
      (injectSource inputs state scope source arms packet) :=
  sourceContribution inputs state scope site source arms _ old operators original.nodes.length left right
    raw node readout packet (union_lookup original inputs state scope site source arms left right) child

def from_arm (original : Graph (RawObservation s)) (inputs : Inputs s) (state : Decoded s View)
    (scope : List Binder) (site : Site) (source : Endpoint) (arms : List Endpoint) (left right : Nat)
    (old : Relations (graph original inputs state scope site source arms left right))
    (operators : Operators (graph original inputs state scope site source arms left right))
    (raw : RawObservation s) (node : Node (RawObservation s))
    (readout : node.catalogue = armsCatalogue inputs state scope arms)
    (packet : Packet (armsCatalogue inputs state scope arms) raw)
    (child : DeclContribution (graph original inputs state scope site source arms left right)
      (relations _ old inputs state scope site source arms) operators right raw node (readout ▸ packet)) :
    DeclContribution (graph original inputs state scope site source arms left right)
      (relations _ old inputs state scope site source arms) operators original.nodes.length raw
      (unionNode inputs state scope site left right source arms)
      (injectArm inputs state scope source arms packet) :=
  armContribution inputs state scope site source arms _ old operators original.nodes.length left right
    raw node readout packet (union_lookup original inputs state scope site source arms left right) child

/-- Actual R159/GR5 application from the retained complete source packet.
The SAME original finite checking derivation and independent admission A are
still required at their owners. Nothing concludes EI is below the old target.
-/
theorem original_target_pair (inputs : Inputs s) (registry : GuardRegistry inputs)
    (readout : RuntimeReadout s View) (ports : PortReadout s View)
    (declarations : Declarations inputs registry) (original : Kernel (Payload s View))
    (environment : Environment (Payload s View)) (context : Context) (mark : Mark)
    (occurrence : Nat) (data : Logical s View) (state : Decoded s View)
    (decoded : decode readout environment = some state) (arms : List Endpoint)
    (scope : List Binder) (raw : RawObservation s)
    (packet : Packet (branchCatalogue inputs (state.logical data) scope ⟨mark.site, .callableImage⟩) raw)
    (checked : Checking (OriginalSourceChecking.kernel inputs registry declarations
      (environmentReading inputs readout ports) original)
      (environment.extend ⟨mark.site, .viewLogic, 0⟩
        (scopeCandidate environment occurrence (.logical .viewLogic data)))
      ⟨.computation, mark.site, context, ⟨mark.site, .callableImage⟩, ⟨mark.site, .synthesis⟩⟩) :
    (unionBody inputs (state.logical data) ⟨mark.site, .callableImage⟩ arms raw).Holds (Meaning inputs) ∧
      Meaning inputs (.trace (raw.atInterface ((state.logical data).interfaces ⟨mark.site, .synthesis⟩))) :=
  app_result_pair inputs registry readout ports declarations original environment context mark occurrence
    data state decoded arms raw checked
    (source_packet_meaning inputs (state.logical data) scope ⟨mark.site, .callableImage⟩ raw packet)

end Selected
end YulangClosure.SourceDeclarationRetentionR295
