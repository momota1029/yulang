import YulangClosure.SourceContributionConstruction
import YulangClosure.OriginalSourceChecking
import YulangClosure.SourceAppAdmissionR159

/-!
R293: constructive EI-All OUTER tagged composition and exact R159 target retention.

Authority: computed-call-result-constructor (2026-10-24) §4; generated-computed-
result-correspondence GR1/GR5. The complete branch clauses below are the ACTUAL
OriginalSourceChecking.clause at original Decoded.interfaces, not arbitrary
Catalogue or Positive parameters. Independent domains, guards, return/world,
and hereditary fields are reified without truncation.

LIMIT: the original arm endpoint list and identification of the source endpoint
with GR1's EvalInvoke registration are not constructed by the present Lean source
builder. Therefore this is a conditional outer-composition construction, NOT an
actual DefineResultView realization. In particular callableImage is not relabeled
EvalInvoke, and the original synthesis endpoint is never replaced by this union.
-/
namespace YulangClosure.ComputedCallUnionRealizationR293

open OriginalSource OriginalSourceInterpretation OriginalSourceEnvironment
open OriginalSourceChecking SourceSignatureConstruction SourceContributionConstruction

variable {s : Sorts} {View : Type}

/-- Typed evidence preserves existential choices and all independent universal
indices, rather than replacing the whole dependent packet with endpoint IDs. -/
def Evidence (Z : Family s) : Positive s → Type
  | .guard fact => PLift fact
  | .field query => PLift (Z query)
  | .both left right => Evidence Z left × Evidence Z right
  | .either left right => Sum (Evidence Z left) (Evidence Z right)
  | .all D body => (d : D) → Evidence Z (body d)
  | .existsE D body => (d : D) × Evidence Z (body d)

theorem evidence_sound (Z : Family s) (body : Positive s) :
    Evidence Z body → body.Holds Z := by
  induction body with
  | guard fact => exact fun e => e.down
  | field query => exact fun e => e.down
  | both left right ihl ihr => exact fun e => ⟨ihl e.1, ihr e.2⟩
  | either left right ihl ihr =>
      intro e
      cases e with
      | inl e => exact Or.inl (ihl e)
      | inr e => exact Or.inr (ihr e)
  | all D body ih => exact fun e d => ih d (e d)
  | existsE D body ih => exact fun e => ⟨e.1, ih e.1 e.2⟩

/-- Original complete computation clause, at the SAME whole observation/event.
The opaque Interface input is read from the original decoded environment. -/
def branchBody (inputs : Inputs s) (state : Decoded s View)
    (endpoint : Endpoint) (raw : RawObservation s) : Positive s :=
  clause inputs (.trace (raw.atInterface (state.interfaces endpoint)))

/-- An injective code for original endpoint slots; different ports at one
source occurrence are never collapsed to the occurrence ID alone. -/
def portCode : OriginalSource.Port → Nat
  | .synthesis => 0 | .finalRoot => 1 | .writtenTarget => 2 | .descriptor => 3
  | .callableImage => 4 | .returnedValue => 5 | .formalCarrier => 6
  | .bodyConsumer => 7 | .invocationReturn => 8 | .branchJoin => 9
  | .patternInput => 10 | .referenceContent => 11

def endpointCode (endpoint : Endpoint) : Nat := 12 * endpoint.site + portCode endpoint.port

theorem endpoint_code_injective (a b : Endpoint) (same : endpointCode a = endpointCode b) : a = b := by
  rcases a with ⟨a, ap⟩
  rcases b with ⟨b, bp⟩
  cases ap <;> cases bp <;> simp_all [endpointCode, portCode] <;> first | exact Nat.mul_left_cancel (by decide) same | omega

/-- No arbitrary catalogue is accepted. Slot labels and complete packet types
are computed from the actual original interface endpoint readout. -/
def branchCatalogue (inputs : Inputs s) (state : Decoded s View)
    (scope : List Binder) (endpoint : Endpoint) : Catalogue (RawObservation s) where
  Port := Unit
  Packet := fun raw _ => Evidence (Meaning inputs) (branchBody inputs state endpoint raw)
  scope := scope
  sharedSlot := fun _ => endpointCode endpoint

/-- Finite ORIGINAL arm declarations; semantic challenge/future families inside
each branchBody remain unbounded. This list is NOT synthesized from source typing. -/
def armsCatalogue (inputs : Inputs s) (state : Decoded s View)
    (scope : List Binder) (arms : List Endpoint) : Catalogue (RawObservation s) where
  Port := Fin arms.length
  Packet := fun raw i => Evidence (Meaning inputs) (branchBody inputs state arms[i] raw)
  scope := scope
  sharedSlot := fun i => endpointCode arms[i]

/-- EI-All's source tag and original arm tags are distinct, even when their
shared slot addresses or descriptor interpretations happen to coincide. -/
def unionCatalogue (inputs : Inputs s) (state : Decoded s View)
    (scope : List Binder) (source : Endpoint) (arms : List Endpoint) : Catalogue (RawObservation s) where
  Port := Sum Unit (Fin arms.length)
  Packet := fun raw tag => match tag with
    | .inl _ => Evidence (Meaning inputs) (branchBody inputs state source raw)
    | .inr i => Evidence (Meaning inputs) (branchBody inputs state arms[i] raw)
  scope := scope
  sharedSlot := fun tag => match tag with
    | .inl _ => endpointCode source
    | .inr i => endpointCode arms[i]

def injectSource (inputs : Inputs s) (state : Decoded s View)
    (scope : List Binder) (source : Endpoint) (arms : List Endpoint)
    {raw : RawObservation s} (packet : Packet (branchCatalogue inputs state scope source) raw) :
    Packet (unionCatalogue inputs state scope source arms) raw :=
  ⟨.inl packet.port, packet.value⟩

def injectArm (inputs : Inputs s) (state : Decoded s View)
    (scope : List Binder) (source : Endpoint) (arms : List Endpoint)
    {raw : RawObservation s} (packet : Packet (armsCatalogue inputs state scope arms) raw) :
    Packet (unionCatalogue inputs state scope source arms) raw :=
  ⟨.inr packet.port, packet.value⟩

/-- The selected relation is CONSTRUCTED by the tagged injection. There is no
hypothesis that an arbitrary desired packet map commutes. Other constructors
in Relations are left as the original independent relations. -/
inductive TaggedAlternative (inputs : Inputs s) (state : Decoded s View)
    (scope : List Binder) (site : Site) (source : Endpoint) (arms : List Endpoint) :
    Site → Bool → (raw : RawObservation s) →
      {child result : Catalogue (RawObservation s)} → Packet child raw → Packet result raw → Type where
  | source (raw : RawObservation s) (packet : Packet (branchCatalogue inputs state scope source) raw) :
      TaggedAlternative inputs state scope site source arms site false raw packet
        (injectSource inputs state scope source arms packet)
  | arm (raw : RawObservation s) (packet : Packet (armsCatalogue inputs state scope arms) raw) :
      TaggedAlternative inputs state scope site source arms site true raw packet
        (injectArm inputs state scope source arms packet)

def sourceRelationCast (inputs : Inputs s) (state : Decoded s View)
    (scope : List Binder) (site : Site) (source : Endpoint) (arms : List Endpoint)
    (raw : RawObservation s) (child : Catalogue (RawObservation s))
    (same : child = branchCatalogue inputs state scope source)
    (packet : Packet (branchCatalogue inputs state scope source) raw) :
    TaggedAlternative inputs state scope site source arms site false raw (same ▸ packet)
      (injectSource inputs state scope source arms packet) := by
  subst child
  exact TaggedAlternative.source raw packet

/-- Conservative extension: every old alternative witness survives, INCLUDING
at the selected site. The new tagged case is a separate sum injection; no site
uniqueness or absence of earlier alternative nodes is assumed. -/
def relations (graph : Graph (RawObservation s)) (original : Relations graph)
    (inputs : Inputs s) (state : Decoded s View) (scope : List Binder)
    (site : Site) (source : Endpoint) (arms : List Endpoint) : Relations graph :=
  { original with alternative := fun atSite right raw {_ _} packet output =>
      (Sum (original.alternative atSite right raw packet output)
        (TaggedAlternative inputs state scope site source arms atSite right raw packet output)) }

/-- Canonical inclusion of each existing relation witness, with every index
and packet unchanged. It applies at all sites without a disequality premise. -/
def retainAlternative (graph : Graph (RawObservation s)) (original : Relations graph)
    (inputs : Inputs s) (state : Decoded s View) (scope : List Binder)
    (site : Site) (source : Endpoint) (arms : List Endpoint)
    (atSite : Site) (right : Bool) (raw : RawObservation s)
    {child result : Catalogue (RawObservation s)} (packet : Packet child raw) (output : Packet result raw)
    (old : original.alternative atSite right raw packet output) :
    (relations graph original inputs state scope site source arms).alternative atSite right raw packet output :=
  .inl old

/-- The old witness can be recovered verbatim; preservation is stronger than
mere existence, including when atSite is exactly the selected site. -/
theorem retained_alternative_exact (graph : Graph (RawObservation s)) (original : Relations graph)
    (inputs : Inputs s) (state : Decoded s View) (scope : List Binder)
    (site : Site) (source : Endpoint) (arms : List Endpoint)
    (atSite : Site) (right : Bool) (raw : RawObservation s)
    {child result : Catalogue (RawObservation s)} (packet : Packet child raw) (output : Packet result raw)
    (old : original.alternative atSite right raw packet output) :
    (retainAlternative graph original inputs state scope site source arms atSite right raw packet output old).getLeft? =
      some old := rfl

/-- Every OLD complete contribution remains constructible under the extension.
The induction retains original relation witnesses at all alternative nodes,
including any number of distinct nodes sharing the selected source site. -/
def retainContribution (graph : Graph (RawObservation s)) (original : Relations graph)
    (inputs : Inputs s) (state : Decoded s View) (scope : List Binder)
    (site : Site) (source : Endpoint) (arms : List Endpoint) (operators : Operators graph)
    {index : Nat} {raw : RawObservation s} {node : Node (RawObservation s)}
    {packet : Packet node.catalogue raw} :
    DeclContribution graph original operators index raw node packet →
      DeclContribution graph (relations graph original inputs state scope site source arms)
        operators index raw node packet
  | .primitive found packet license => .primitive found packet license
  | .alternativeLeft found child output related =>
      .alternativeLeft found (retainContribution graph original inputs state scope site source arms operators child)
        output (.inl related)
  | .alternativeRight found child output related =>
      .alternativeRight found (retainContribution graph original inputs state scope site source arms operators child)
        output (.inl related)
  | .conjunction found first second output related =>
      .conjunction found (retainContribution graph original inputs state scope site source arms operators first)
        (retainContribution graph original inputs state scope site source arms operators second) output related
  | .image found output evidence => .image found output evidence
  | .call found output evidence => .call found output evidence
  | .forward found step child output related =>
      .forward found step (retainContribution graph original inputs state scope site source arms operators child) output related

/-- The actual Node.alternative has the constructed complete result catalogue. -/
def unionNode (inputs : Inputs s) (state : Decoded s View) (scope : List Binder)
    (site : Site) (left right : Nat) (source : Endpoint) (arms : List Endpoint) : Node (RawObservation s) :=
  .alternative site left right (unionCatalogue inputs state scope source arms)

theorem source_packet_unchanged (inputs : Inputs s) (state : Decoded s View)
    (scope : List Binder) (source : Endpoint) (arms : List Endpoint)
    (raw : RawObservation s) (packet : Packet (branchCatalogue inputs state scope source) raw) :
    (injectSource inputs state scope source arms packet).value = packet.value := rfl

theorem arm_packet_unchanged (inputs : Inputs s) (state : Decoded s View)
    (scope : List Binder) (source : Endpoint) (arms : List Endpoint)
    (raw : RawObservation s) (packet : Packet (armsCatalogue inputs state scope arms) raw) :
    (injectArm inputs state scope source arms packet).value = packet.value := rfl

/-- Full trace meaning, including all original guards, world, optional result,
and future obligations, follows from the constructed selected packet. -/
theorem source_packet_meaning (inputs : Inputs s) (state : Decoded s View)
    (scope : List Binder) (source : Endpoint) (raw : RawObservation s)
    (packet : Packet (branchCatalogue inputs state scope source) raw) :
    Meaning inputs (.trace (raw.atInterface (state.interfaces source))) :=
  (meaning_clause inputs _).mpr (evidence_sound _ _ packet.value)

/-- Applies the genuine relation to the existing finite contribution constructor.
Only the independent child contribution/license remains input. -/
def sourceContribution (inputs : Inputs s) (state : Decoded s View)
    (scope : List Binder) (site : Site) (source : Endpoint) (arms : List Endpoint)
    (graph : Graph (RawObservation s)) (original : Relations graph) (operators : Operators graph)
    (index left right : Nat) (raw : RawObservation s)
    (childNode : Node (RawObservation s))
    (sameCatalogue : childNode.catalogue = branchCatalogue inputs state scope source)
    (packet : Packet (branchCatalogue inputs state scope source) raw)
    (found : graph.node index = some (unionNode inputs state scope site left right source arms))
    (child : DeclContribution graph (relations graph original inputs state scope site source arms)
      operators left raw childNode (sameCatalogue ▸ packet)) :
    DeclContribution graph (relations graph original inputs state scope site source arms)
      operators index raw (unionNode inputs state scope site left right source arms)
      (injectSource inputs state scope source arms packet) := by
  apply DeclContribution.alternativeLeft found child
  exact Sum.inr
    (sourceRelationCast inputs state scope site source arms raw childNode.catalogue sameCatalogue packet)

/-- Every original arm has its own injection and independently supplied child
contribution. A source contribution never licenses a different arm. -/
def armContribution (inputs : Inputs s) (state : Decoded s View)
    (scope : List Binder) (site : Site) (source : Endpoint) (arms : List Endpoint)
    (graph : Graph (RawObservation s)) (original : Relations graph) (operators : Operators graph)
    (index left right : Nat) (raw : RawObservation s)
    (childNode : Node (RawObservation s))
    (sameCatalogue : childNode.catalogue = armsCatalogue inputs state scope arms)
    (packet : Packet (armsCatalogue inputs state scope arms) raw)
    (found : graph.node index = some (unionNode inputs state scope site left right source arms))
    (child : DeclContribution graph (relations graph original inputs state scope site source arms)
      operators right raw childNode (sameCatalogue ▸ packet)) :
    DeclContribution graph (relations graph original inputs state scope site source arms)
      operators index raw (unionNode inputs state scope site left right source arms)
      (injectArm inputs state scope source arms packet) := by
  apply DeclContribution.alternativeRight found child
  have castArm (cat : Catalogue (RawObservation s))
      (same : cat = armsCatalogue inputs state scope arms) :
      TaggedAlternative inputs state scope site source arms site true raw (same ▸ packet)
        (injectArm inputs state scope source arms packet) := by
    subst cat
    exact TaggedAlternative.arm raw packet
  exact Sum.inr (castArm childNode.catalogue sameCatalogue)

/-- Positive finite proof data for the outer tagged constructor. It does not
claim registration of the generated union as an existing interface. -/
def unionBody (inputs : Inputs s) (state : Decoded s View)
    (source : Endpoint) (arms : List Endpoint) (raw : RawObservation s) : Positive s :=
  .either (branchBody inputs state source raw)
    (.existsE (Fin arms.length) (fun i => branchBody inputs state arms[i] raw))

theorem union_introduction (inputs : Inputs s) (registry : GuardRegistry inputs)
    (leaves : Positive s → Positive s → Prop) (state : Decoded s View)
    (source : Endpoint) (arms : List Endpoint) (raw : RawObservation s) :
    Proof inputs registry leaves (.field (.trace (raw.atInterface (state.interfaces source))))
      (unionBody inputs state source arms raw) :=
  .compose (.unfold _) (.inLeft _ _)

/-- GR5 is applied at R159's exact ViewLogic extension and original target.
The source membership is independently checked by the original finite syntax;
this theorem never demands or concludes EI ⊆ original target. -/
theorem app_result_pair (inputs : Inputs s) (registry : GuardRegistry inputs)
    (readout : RuntimeReadout s View) (ports : PortReadout s View)
    (declarations : Declarations inputs registry) (original : Kernel (Payload s View))
    (environment : Environment (Payload s View)) (context : Context) (mark : Mark)
    (occurrence : Nat) (data : Logical s View) (state : Decoded s View)
    (decoded : decode readout environment = some state) (arms : List Endpoint)
    (raw : RawObservation s)
    (checked : Checking (OriginalSourceChecking.kernel inputs registry declarations
      (environmentReading inputs readout ports) original)
      (environment.extend ⟨mark.site, .viewLogic, 0⟩
        (scopeCandidate environment occurrence (.logical .viewLogic data)))
      ⟨.computation, mark.site, context, ⟨mark.site, .callableImage⟩, ⟨mark.site, .synthesis⟩⟩)
    (member : Meaning inputs (.trace (raw.atInterface
      ((state.logical data).interfaces ⟨mark.site, .callableImage⟩)))) :
    (unionBody inputs (state.logical data) ⟨mark.site, .callableImage⟩ arms raw).Holds (Meaning inputs) ∧
    Meaning inputs (.trace (raw.atInterface ((state.logical data).interfaces ⟨mark.site, .synthesis⟩))) := by
  have extended := decode_extend readout environment ⟨mark.site, .viewLogic, 0⟩
    (scopeCandidate environment occurrence (.logical .viewLogic data)) state decoded
  constructor
  · exact Or.inl ((meaning_clause inputs _).mp member)
  · have sound := checking_sound inputs registry declarations (environmentReading inputs readout ports)
      original checked (.computation raw)
    simp only [lower, upper, environmentReading, extended, stateClause] at sound
    exact sound member

end YulangClosure.ComputedCallUnionRealizationR293
