import YulangClosure.SourceSignatureConstruction

/-!
Composite result/phase contribution derivations and actual governed fields.
Authority: the adopted source-signature-incidence-construction (2026-10-08)
§3.4, §§4–5 and the finite-development part of §7.

Independent original primitive licenses, original branch/result relations,
local operator/C0 evidence and local governed-field interfaces are inputs.
No field assumes DeclContribution, native L/A, attachment, source typing or
inference soundness. The global projection selector is constructed below.
Authentic source/descriptor/world interpretation remains separate.
This slice excludes standalone contextual operand-port contributions: their
typed slot injection is distinct from an image result/phase port. It also
constructs only the declared-port fragment of outer native L/A, not the upper,
reference, annotation or certified whole-family outer rules.
-/
namespace YulangClosure.SourceContributionConstruction

open OriginalSource SourceSignatureConstruction

variable {Joint : Type}

/-- One actual complete port packet, at one original joint row. -/
structure Packet (catalogue : Catalogue Joint) (whole : Joint) where
  port : catalogue.Port
  value : catalogue.Packet whole port

/-- The genuine original local relation witnesses. These are declaration-local
whole-packet relations, not a global applicability or source-typing oracle.
In particular an Alt witness keeps the selected original branch/result map.
Forward witnesses keep the original substitution/annotation rule. -/
structure Relations (graph : Graph Joint) where
  alternative : (site : Site) → (right : Bool) → (whole : Joint) →
    {child result : Catalogue Joint} → Packet child whole → Packet result whole → Type
  conjunction : (site : Site) → (whole : Joint) →
    {left right result : Catalogue Joint} →
    Packet left whole → Packet right whole → Packet result whole → Type
  forward : (step : Step) → (whole : Joint) →
    {child result : Catalogue Joint} →
    Packet child (step.action graph whole) → Packet result whole → Type

/-- The leaf/antecedent field interface of ONE independently typed local
operator. There is no receiving root or desired enclosing attachment here.
Each selected field already contains its genuine original primitive/local
license. A support schema alone cannot construct either constructor. -/
inductive OperatorField (graph : Graph Joint) (node : Node Joint) (whole : Joint) : Type 1 where
  | localField (intro : Introduction Joint) (introduced : intro ∈ node.introductions)
      (packet : Packet intro.catalogue whole)
      (license : intro.License whole packet.port packet.value) : OperatorField graph node whole
  | antecedent (step : Step) (child : Nat) (edge : SourceEdge node step child)
      (field : LeafLicensedField graph child (step.action graph whole)) :
      OperatorField graph node whole

/-- An authentic local operator/C0 contract, including its original complete
governed-field family. Evidence and its fields can have arbitrary dependent
domains. Their semantic validity is the original local owner's obligation;
this interface does not assert that any evidence exists. -/
structure OperatorContract (graph : Graph Joint) (node : Node Joint) where
  Evidence : (whole : Joint) → Packet node.catalogue whole → Type
  Field : (whole : Joint) → (packet : Packet node.catalogue whole) → Evidence whole packet → Type
  governed : (whole : Joint) → (packet : Packet node.catalogue whole) →
    (evidence : Evidence whole packet) → Field whole packet evidence → OperatorField graph node whole

/-- Contracts are attached to the actual local operator constructor. They
contain no final DeclContribution/L/A or original-soundness conclusion. -/
structure Operators (graph : Graph Joint) where
  image : (site : Site) → (operator : Rule) → (operands : List Nat) →
    (locals : List (Introduction Joint)) → (result : Catalogue Joint) →
      OperatorContract graph (.image site operator operands locals result)
  call : (context : Context) → (mark : Mark) → (callee argument : Source .expression) →
    (nodes : CallNodes) → (locals : List (Introduction Joint)) → (result : Catalogue Joint) →
      OperatorContract graph (.call context mark callee argument nodes locals result)

/-- Actual transport of a whole leaf field through its source constructor.
The row action, entire packet and original license are the same objects. -/
def liftField {graph : Graph Joint} {index child : Nat} {node : Node Joint} {whole : Joint}
    {step : Step} (found : graph.node index = some node) (edge : SourceEdge node step child)
    (field : LeafLicensedField graph child (step.action graph whole)) :
    LeafLicensedField graph index whole :=
  ⟨contextual found edge field.occurrence, field.port, field.packet, field.license⟩

theorem lift_field_owner {graph : Graph Joint} {index child : Nat} {node : Node Joint}
    {whole : Joint} {step : Step} (found : graph.node index = some node)
    (edge : SourceEdge node step child)
    (field : LeafLicensedField graph child (step.action graph whole)) :
    (liftField found edge field).occurrence.owner = field.occurrence.owner := rfl

theorem lift_field_packet {graph : Graph Joint} {index child : Nat} {node : Node Joint}
    {whole : Joint} {step : Step} (found : graph.node index = some node)
    (edge : SourceEdge node step child)
    (field : LeafLicensedField graph child (step.action graph whole)) :
    (liftField found edge field).packet = field.packet := rfl

theorem lift_field_license {graph : Graph Joint} {index child : Nat} {node : Node Joint}
    {whole : Joint} {step : Step} (found : graph.node index = some node)
    (edge : SourceEdge node step child)
    (field : LeafLicensedField graph child (step.action graph whole)) :
    (liftField found edge field).license = field.license := rfl

def OperatorField.place {graph : Graph Joint} {index : Nat} {node : Node Joint} {whole : Joint}
    (found : graph.node index = some node) : OperatorField graph node whole → LeafLicensedField graph index whole
  | .localField intro introduced packet license =>
      ⟨⟨intro, [], .introduction found introduced⟩, packet.port, packet.value, license⟩
  | .antecedent _ _ edge field => liftField found edge field

/-- Independent original forwarding constructors. Alternative and conjunction
are deliberately absent: their contributions need actual selected/paired
evidence in the separate constructors below. Image operands are also absent:
this result-port grammar cannot treat a contextual operand port as an image
result. Image/Call results require their actual local operator Evidence.
Standalone operand-port packaging needs its distinct typed slot injection. -/
inductive Forward : Node Joint → Step → Nat → Prop where
  | reference : Forward (.reference site target substitution result)
      (.reference site target substitution) target
  | scope : Forward (.scope binder child result) (.scope binder) child
  | rename : Forward (.rename site substitution child result) (.rename site substitution) child
  | insertion : Forward (.insertion root clause child result) (.insertion root clause) child
  | annotation : Forward (.annotation site annotation child result) (.annotation site annotation) child

theorem Forward.edge {node : Node Joint} {step : Step} {child : Nat}
    (forward : Forward node step child) : SourceEdge node step child := by
  cases forward with
  | reference => exact .reference
  | scope => exact .scope
  | rename => exact .rename
  | insertion => exact .insertion
  | annotation => exact .annotation

/-- Original composite result/phase contribution grammar. Its constructors mention
neither the compiler relation nor native L/A. Same-row pair indexing prevents
independently chosen worlds; Alt keeps the actual selected branch witness. -/
inductive DeclContribution (graph : Graph Joint) (relations : Relations graph) (operators : Operators graph) :
    (index : Nat) → (whole : Joint) → (node : Node Joint) → Packet node.catalogue whole → Type 1 where
  | primitive (found : graph.node index = some (.primitive intro))
      (packet : Packet intro.catalogue whole)
      (license : intro.License whole packet.port packet.value) :
      DeclContribution graph relations operators index whole (.primitive intro) packet
  | alternativeLeft (found : graph.node index = some (.alternative site left right result))
      (child : DeclContribution graph relations operators left whole childNode childPacket)
      (output : Packet result whole)
      (related : relations.alternative site false whole childPacket output) :
      DeclContribution graph relations operators index whole (.alternative site left right result) output
  | alternativeRight (found : graph.node index = some (.alternative site left right result))
      (child : DeclContribution graph relations operators right whole childNode childPacket)
      (output : Packet result whole)
      (related : relations.alternative site true whole childPacket output) :
      DeclContribution graph relations operators index whole (.alternative site left right result) output
  | conjunction (found : graph.node index = some (.conjunction site left right result))
      (first : DeclContribution graph relations operators left whole firstNode firstPacket)
      (second : DeclContribution graph relations operators right whole secondNode secondPacket)
      (output : Packet result whole)
      (related : relations.conjunction site whole firstPacket secondPacket output) :
      DeclContribution graph relations operators index whole (.conjunction site left right result) output
  | image (found : graph.node index = some (.image site operator operands locals result))
      (output : Packet result whole)
      (evidence : (operators.image site operator operands locals result).Evidence whole output) :
      DeclContribution graph relations operators index whole (.image site operator operands locals result) output
  | call (found : graph.node index = some (.call context mark callee argument nodes locals result))
      (output : Packet result whole)
      (evidence : (operators.call context mark callee argument nodes locals result).Evidence whole output) :
      DeclContribution graph relations operators index whole (.call context mark callee argument nodes locals result) output
  | forward (found : graph.node index = some node) (source : Forward node step target)
      (child : DeclContribution graph relations operators target (step.action graph whole) childNode childPacket)
      (output : Packet node.catalogue whole)
      (related : relations.forward step whole childPacket output) :
      DeclContribution graph relations operators index whole node output

/-- The original licensed-projection index is computed by the finite rule
tree, independently of the complete origin schema. No unselected Alt field
is added; pair retains both field families on its SAME whole row. -/
def DeclContribution.Projection {graph : Graph Joint} {relations : Relations graph} {operators : Operators graph}
    {index : Nat} {whole : Joint} {node : Node Joint} {packet : Packet node.catalogue whole} :
    DeclContribution graph relations operators index whole node packet → Type
  | .primitive .. => Unit
  | .alternativeLeft _ child _ _ | .alternativeRight _ child _ _ => child.Projection
  | .conjunction _ first second _ _ => Sum first.Projection second.Projection
  | .image (site := site) (operator := operator) (operands := operands) (locals := locals)
      (result := result) _ output evidence =>
      (operators.image site operator operands locals result).Field _ output evidence
  | .call (context := context) (mark := mark) (callee := callee) (argument := argument)
      (nodes := nodes) (locals := locals) (result := result) _ output evidence =>
      (operators.call context mark callee argument nodes locals result).Field _ output evidence
  | .forward _ _ child _ _ => child.Projection

/-- The global governed-field map is the constructed output of the original
rule induction. Only the genuine local primitive/operator cases supply leaf
licenses. Every structural step creates its actual contextual source route. -/
def DeclContribution.project {graph : Graph Joint} {relations : Relations graph} {operators : Operators graph}
    {index : Nat} {whole : Joint} {node : Node Joint} {packet : Packet node.catalogue whole}
    (derivation : DeclContribution graph relations operators index whole node packet) :
    derivation.Projection → LeafLicensedField graph index whole :=
  match derivation with
  | .primitive found packet license => fun _ =>
      ⟨⟨_, [], .introduction found (by simp [Node.introductions])⟩,
        packet.port, packet.value, license⟩
  | .alternativeLeft found child _ _ => fun field =>
      liftField found SourceEdge.alternativeLeft (child.project field)
  | .alternativeRight found child _ _ => fun field =>
      liftField found SourceEdge.alternativeRight (child.project field)
  | .conjunction found first second _ _ => fun field =>
      match field with
      | .inl left => liftField found SourceEdge.conjunctionLeft (first.project left)
      | .inr right => liftField found SourceEdge.conjunctionRight (second.project right)
  | .image (site := site) (operator := operator) (operands := operands) (locals := locals)
      (result := result) found output evidence => fun field =>
      ((operators.image site operator operands locals result).governed _ output evidence field).place found
  | .call (context := context) (mark := mark) (callee := callee) (argument := argument)
      (nodes := nodes) (locals := locals) (result := result) found output evidence => fun field =>
      ((operators.call context mark callee argument nodes locals result).governed _ output evidence field).place found
  | .forward found source child _ _ => fun field => liftField found source.edge (child.project field)

theorem projection_has_original_provenance {graph : Graph Joint} {relations : Relations graph}
    {operators : Operators graph} {index : Nat} {whole : Joint} {node : Node Joint}
    {packet : Packet node.catalogue whole}
    (derivation : DeclContribution graph relations operators index whole node packet)
    (field : derivation.Projection) :
    PortProv graph index (derivation.project field).occurrence.intro
      (derivation.project field).occurrence.route := (derivation.project field).occurrence.provenance

theorem projection_compiles_provenance {graph : Graph Joint} {relations : Relations graph}
    {operators : Operators graph} {index : Nat} {whole : Joint} {node : Node Joint}
    {packet : Packet node.catalogue whole}
    (derivation : DeclContribution graph relations operators index whole node packet)
    (field : derivation.Projection) :
    Developed (build graph) index (derivation.project field).occurrence.intro
      (derivation.project field).occurrence.route :=
  compile_provenance (projection_has_original_provenance derivation field)


/-- Lookup in the actual built frame, at the exact original retained node. -/
def compiledLookup (graph : Graph Joint) (index : Nat) (node : Node Joint) : Prop :=
  (build graph)[index]? = some (compileNode node)

theorem compiled_lookup_iff (graph : Graph Joint) (index : Nat) (node : Node Joint) :
    compiledLookup graph index node ↔ graph.node index = some node := by
  unfold compiledLookup
  rw [build_lookup]
  constructor
  · intro found
    simp only [Option.map_eq_some_iff] at found
    rcases found with ⟨original, looked, same⟩
    have sourceSame := congrArg CompiledNode.source same
    change original = node at sourceSame
    subst original
    exact looked
  · intro found
    rw [found]
    rfl

/-- Independent compiler-entry grammar. Its registrations are checked in the
actual built graph; all independent local semantic witnesses remain intact.
It is not defined by existential projection of DeclContribution. -/
inductive CompiledContribution (graph : Graph Joint) (relations : Relations graph) (operators : Operators graph) :
    (index : Nat) → (whole : Joint) → (node : Node Joint) → Packet node.catalogue whole → Type 1 where
  | primitive (found : compiledLookup graph index (.primitive intro))
      (packet : Packet intro.catalogue whole)
      (license : intro.License whole packet.port packet.value) :
      CompiledContribution graph relations operators index whole (.primitive intro) packet
  | alternativeLeft (found : compiledLookup graph index (.alternative site left right result))
      (child : CompiledContribution graph relations operators left whole childNode childPacket)
      (output : Packet result whole)
      (related : relations.alternative site false whole childPacket output) :
      CompiledContribution graph relations operators index whole (.alternative site left right result) output
  | alternativeRight (found : compiledLookup graph index (.alternative site left right result))
      (child : CompiledContribution graph relations operators right whole childNode childPacket)
      (output : Packet result whole)
      (related : relations.alternative site true whole childPacket output) :
      CompiledContribution graph relations operators index whole (.alternative site left right result) output
  | conjunction (found : compiledLookup graph index (.conjunction site left right result))
      (first : CompiledContribution graph relations operators left whole firstNode firstPacket)
      (second : CompiledContribution graph relations operators right whole secondNode secondPacket)
      (output : Packet result whole)
      (related : relations.conjunction site whole firstPacket secondPacket output) :
      CompiledContribution graph relations operators index whole (.conjunction site left right result) output
  | image (found : compiledLookup graph index (.image site operator operands locals result))
      (output : Packet result whole)
      (evidence : (operators.image site operator operands locals result).Evidence whole output) :
      CompiledContribution graph relations operators index whole (.image site operator operands locals result) output
  | call (found : compiledLookup graph index (.call context mark callee argument nodes locals result))
      (output : Packet result whole)
      (evidence : (operators.call context mark callee argument nodes locals result).Evidence whole output) :
      CompiledContribution graph relations operators index whole (.call context mark callee argument nodes locals result) output
  | forward (found : compiledLookup graph index node) (source : Forward node step target)
      (child : CompiledContribution graph relations operators target (step.action graph whole) childNode childPacket)
      (output : Packet node.catalogue whole)
      (related : relations.forward step whole childPacket output) :
      CompiledContribution graph relations operators index whole node output

def DeclContribution.compile {graph : Graph Joint} {relations : Relations graph} {operators : Operators graph}
    {index : Nat} {whole : Joint} {node : Node Joint} {packet : Packet node.catalogue whole} :
    DeclContribution graph relations operators index whole node packet →
      CompiledContribution graph relations operators index whole node packet
  | .primitive found packet license => .primitive ((compiled_lookup_iff _ _ _).mpr found) packet license
  | .alternativeLeft found child output related =>
      .alternativeLeft ((compiled_lookup_iff _ _ _).mpr found) child.compile output related
  | .alternativeRight found child output related =>
      .alternativeRight ((compiled_lookup_iff _ _ _).mpr found) child.compile output related
  | .conjunction found first second output related =>
      .conjunction ((compiled_lookup_iff _ _ _).mpr found) first.compile second.compile output related
  | .image found output evidence => .image ((compiled_lookup_iff _ _ _).mpr found) output evidence
  | .call found output evidence => .call ((compiled_lookup_iff _ _ _).mpr found) output evidence
  | .forward found source child output related =>
      .forward ((compiled_lookup_iff _ _ _).mpr found) source child.compile output related

def CompiledContribution.read {graph : Graph Joint} {relations : Relations graph} {operators : Operators graph}
    {index : Nat} {whole : Joint} {node : Node Joint} {packet : Packet node.catalogue whole} :
    CompiledContribution graph relations operators index whole node packet →
      DeclContribution graph relations operators index whole node packet
  | .primitive found packet license => .primitive ((compiled_lookup_iff _ _ _).mp found) packet license
  | .alternativeLeft found child output related =>
      .alternativeLeft ((compiled_lookup_iff _ _ _).mp found) child.read output related
  | .alternativeRight found child output related =>
      .alternativeRight ((compiled_lookup_iff _ _ _).mp found) child.read output related
  | .conjunction found first second output related =>
      .conjunction ((compiled_lookup_iff _ _ _).mp found) first.read second.read output related
  | .image found output evidence => .image ((compiled_lookup_iff _ _ _).mp found) output evidence
  | .call found output evidence => .call ((compiled_lookup_iff _ _ _).mp found) output evidence
  | .forward found source child output related =>
      .forward ((compiled_lookup_iff _ _ _).mp found) source child.read output related

theorem read_compile {graph : Graph Joint} {relations : Relations graph} {operators : Operators graph}
    {index : Nat} {whole : Joint} {node : Node Joint} {packet : Packet node.catalogue whole}
    (derivation : DeclContribution graph relations operators index whole node packet) :
    derivation.compile.read = derivation := by
  induction derivation <;> simp_all [DeclContribution.compile, CompiledContribution.read]

theorem compile_read {graph : Graph Joint} {relations : Relations graph} {operators : Operators graph}
    {index : Nat} {whole : Joint} {node : Node Joint} {packet : Packet node.catalogue whole}
    (entry : CompiledContribution graph relations operators index whole node packet) :
    entry.read.compile = entry := by
  induction entry <;> simp_all [DeclContribution.compile, CompiledContribution.read]

/-- Proof-record bijection, including all actual original branch/result law
witnesses and complete local operator evidence, not just equal endpoints. -/
theorem compilation_injective {graph : Graph Joint} {relations : Relations graph} {operators : Operators graph}
    {index : Nat} {whole : Joint} {node : Node Joint} {packet : Packet node.catalogue whole}
    (first second : DeclContribution graph relations operators index whole node packet)
    (same : first.compile = second.compile) : first = second := by
  have readSame := congrArg CompiledContribution.read same
  simpa only [read_compile] using readSame

/-- The complete independently built origin partition remains available even
when the actual contribution selected only one branch's licensed projections. -/
abbrev CompletePartition (graph : Graph Joint) (index : Nat) := Occurrence graph index

theorem selected_left_projection_domain {graph : Graph Joint} {relations : Relations graph}
    {operators : Operators graph} {index left right : Nat} {site : Site} {whole : Joint}
    {result : Catalogue Joint} {childNode : Node Joint} {childPacket : Packet childNode.catalogue whole}
    (found : graph.node index = some (.alternative site left right result))
    (child : DeclContribution graph relations operators left whole childNode childPacket)
    (output : Packet result whole)
    (related : relations.alternative site false whole childPacket output) :
    (DeclContribution.alternativeLeft found child output related).Projection = child.Projection := rfl

theorem selected_right_projection_domain {graph : Graph Joint} {relations : Relations graph}
    {operators : Operators graph} {index left right : Nat} {site : Site} {whole : Joint}
    {result : Catalogue Joint} {childNode : Node Joint} {childPacket : Packet childNode.catalogue whole}
    (found : graph.node index = some (.alternative site left right result))
    (child : DeclContribution graph relations operators right whole childNode childPacket)
    (output : Packet result whole)
    (related : relations.alternative site true whole childPacket output) :
    (DeclContribution.alternativeRight found child output related).Projection = child.Projection := rfl

/-- The other alternative's complete origin schema is retained. No license
for that alternative follows from the selected branch or this constructor. -/
theorem alternative_keeps_other_partition {graph : Graph Joint} {index left right : Nat}
    {site : Site} {result : Catalogue Joint}
    (found : graph.node index = some (.alternative site left right result))
    (other : CompletePartition graph right) :
    ∃ occurrence : CompletePartition graph index,
      occurrence.intro = other.intro ∧
      occurrence.route = Step.alternative site true :: other.route :=
  ⟨contextual found SourceEdge.alternativeRight other, rfl, rfl⟩

theorem reference_contribution_stays_inherited {graph : Graph Joint} {relations : Relations graph}
    {operators : Operators graph} {index target substitution : Nat} {site : Site} {whole : Joint}
    {result : Catalogue Joint} {childNode : Node Joint}
    {childPacket : Packet childNode.catalogue (graph.substitution substitution whole)}
    (found : graph.node index = some (.reference site target substitution result))
    (child : DeclContribution graph relations operators target
      (graph.substitution substitution whole) childNode childPacket)
    (output : Packet result whole)
    (related : relations.forward (.reference site target substitution) whole childPacket output)
    (field : child.Projection) :
    let contribution := DeclContribution.forward found Forward.reference child output related
    (contribution.project field).occurrence.inherited = true ∧
      (contribution.project field).occurrence.owner = (child.project field).occurrence.owner := by
  refine ⟨?_, rfl⟩
  exact contextual_imported found SourceEdge.reference (child.project field).occurrence rfl

/-- All original result and witness indices of one declared contribution.
The packet is at the original child row; insertion changes no semantic field. -/
structure DeclaredKey (graph : Graph Joint) where
  insertion : Nat
  root : Nat
  clause : Nat
  source : Nat
  whole : Joint
  node : Node Joint
  packet : Packet node.catalogue whole

def DeclaredKey.receiver (key : DeclaredKey graph) : Site := graph.registration key.root

/-- The declared-port fragment of L. It uses an actual root-insertion node and
the WHOLE composite contribution, rather than a primitive leaf license. -/
inductive DeclaredLicense (graph : Graph Joint) (relations : Relations graph) (operators : Operators graph) :
    DeclaredKey graph → Type 1 where
  | declared (key : DeclaredKey graph) (result : Catalogue Joint)
      (inserted : graph.node key.insertion = some (.insertion key.root key.clause key.source result))
      (contribution : DeclContribution graph relations operators key.source key.whole key.node key.packet) :
      DeclaredLicense graph relations operators key

/-- Independent declared-port A. This constructor consumes no L. Its whole
diagram is constructed below from the complete contribution's actual fields. -/
inductive DeclaredAttachment (graph : Graph Joint) (relations : Relations graph) (operators : Operators graph) :
    DeclaredKey graph → Type 1 where
  | declared (key : DeclaredKey graph) (result : Catalogue Joint)
      (inserted : graph.node key.insertion = some (.insertion key.root key.clause key.source result))
      (contribution : DeclContribution graph relations operators key.source key.whole key.node key.packet) :
      DeclaredAttachment graph relations operators key

def DeclaredLicense.attach {graph : Graph Joint} {relations : Relations graph} {operators : Operators graph}
    {key : DeclaredKey graph} (license : DeclaredLicense graph relations operators key) :
      DeclaredAttachment graph relations operators key := by
  cases license with
  | declared result inserted contribution =>
      exact .declared key result inserted contribution

def DeclaredAttachment.license {graph : Graph Joint} {relations : Relations graph} {operators : Operators graph}
    {key : DeclaredKey graph} (attachment : DeclaredAttachment graph relations operators key) :
      DeclaredLicense graph relations operators key := by
  cases attachment with
  | declared result inserted contribution =>
      exact .declared key result inserted contribution

theorem declared_license_roundtrip {graph : Graph Joint} {relations : Relations graph} {operators : Operators graph}
    {key : DeclaredKey graph} (license : DeclaredLicense graph relations operators key) :
    license.attach.license = license := by cases license; rfl

theorem declared_attachment_roundtrip {graph : Graph Joint} {relations : Relations graph} {operators : Operators graph}
    {key : DeclaredKey graph} (attachment : DeclaredAttachment graph relations operators key) :
    attachment.license.attach = attachment := by cases attachment; rfl

def DeclaredAttachment.contribution {graph : Graph Joint} {relations : Relations graph} {operators : Operators graph}
    {key : DeclaredKey graph} : DeclaredAttachment graph relations operators key →
      DeclContribution graph relations operators key.source key.whole key.node key.packet
  | .declared _ _ _ contribution => contribution

/-- The attachment's entire governed-field diagram, with every original
packet/license intact. No per-port hidden row or owner reselection is used. -/
def DeclaredAttachment.place {graph : Graph Joint} {relations : Relations graph} {operators : Operators graph}
    {key : DeclaredKey graph} (attachment : DeclaredAttachment graph relations operators key)
    (field : attachment.contribution.Projection) :
    InsertedField graph key.root key.clause key.source key.whole :=
  insertField graph key.root key.clause (attachment.contribution.project field)

theorem attachment_preserves_owner {graph : Graph Joint} {relations : Relations graph} {operators : Operators graph}
    {key : DeclaredKey graph} (attachment : DeclaredAttachment graph relations operators key)
    (field : attachment.contribution.Projection) :
    (attachment.place field).placement.owner =
      (attachment.contribution.project field).occurrence.owner := rfl

theorem attachment_receiver {graph : Graph Joint} {relations : Relations graph} {operators : Operators graph}
    {key : DeclaredKey graph} (attachment : DeclaredAttachment graph relations operators key)
    (field : attachment.contribution.Projection) :
    (attachment.place field).placement.receiver = key.receiver := rfl

theorem attachment_preserves_complete_field {graph : Graph Joint} {relations : Relations graph}
    {operators : Operators graph} {key : DeclaredKey graph}
    (attachment : DeclaredAttachment graph relations operators key)
    (field : attachment.contribution.Projection) :
    (attachment.place field).original = attachment.contribution.project field := rfl

theorem attachment_preserves_import_classification {graph : Graph Joint} {relations : Relations graph}
    {operators : Operators graph} {key : DeclaredKey graph}
    (attachment : DeclaredAttachment graph relations operators key)
    (field : attachment.contribution.Projection) :
    (attachment.place field).placement.inherited =
      (attachment.contribution.project field).occurrence.inherited := rfl

/-- Independently represented compiler declared-port entry. Its registration
and entire composite contribution are checked against the built graph. -/
inductive CompiledDeclared (graph : Graph Joint) (relations : Relations graph) (operators : Operators graph) :
    DeclaredKey graph → Type 1 where
  | declared (key : DeclaredKey graph) (result : Catalogue Joint)
      (inserted : compiledLookup graph key.insertion (.insertion key.root key.clause key.source result))
      (contribution : CompiledContribution graph relations operators key.source key.whole key.node key.packet) :
      CompiledDeclared graph relations operators key

def DeclaredLicense.compile {graph : Graph Joint} {relations : Relations graph} {operators : Operators graph}
    {key : DeclaredKey graph} (license : DeclaredLicense graph relations operators key) :
      CompiledDeclared graph relations operators key := by
  cases license with
  | declared result inserted contribution =>
      exact .declared key result ((compiled_lookup_iff _ _ _).mpr inserted) contribution.compile

def CompiledDeclared.read {graph : Graph Joint} {relations : Relations graph} {operators : Operators graph}
    {key : DeclaredKey graph} (entry : CompiledDeclared graph relations operators key) :
      DeclaredLicense graph relations operators key := by
  cases entry with
  | declared result inserted contribution =>
      exact .declared key result ((compiled_lookup_iff _ _ _).mp inserted) contribution.read

theorem declared_read_compile {graph : Graph Joint} {relations : Relations graph} {operators : Operators graph}
    {key : DeclaredKey graph} (license : DeclaredLicense graph relations operators key) :
    license.compile.read = license := by
  cases license
  simp only [DeclaredLicense.compile, CompiledDeclared.read, read_compile]

theorem declared_compile_read {graph : Graph Joint} {relations : Relations graph} {operators : Operators graph}
    {key : DeclaredKey graph} (entry : CompiledDeclared graph relations operators key) :
    entry.read.compile = entry := by
  cases entry
  simp only [DeclaredLicense.compile, CompiledDeclared.read, compile_read]

/-- The declared-port attach_F map has no attachment premise. It reconstructs
the original whole contribution first, then builds the independent A rule. -/
def CompiledDeclared.attach {graph : Graph Joint} {relations : Relations graph} {operators : Operators graph}
    {key : DeclaredKey graph} (entry : CompiledDeclared graph relations operators key) :
    DeclaredAttachment graph relations operators key := entry.read.attach

theorem compiled_declared_attachment_readback {graph : Graph Joint} {relations : Relations graph}
    {operators : Operators graph} {key : DeclaredKey graph}
    (entry : CompiledDeclared graph relations operators key) :
    entry.attach.license.compile = entry := by
  simp only [CompiledDeclared.attach, declared_license_roundtrip, declared_compile_read]

end YulangClosure.SourceContributionConstruction
