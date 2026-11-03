import YulangClosure.OriginalClauseCompilerR318
import YulangClosure.ComputedCallTypedFormationR310
import YulangClosure.OriginalUnionOwnerR292

/-!
R338: the raw licensed-leaf edge of the existing original Union consumer.

Sources: adopted source-signature-incidence-construction §§3.2, 3.4, 4–5;
EI-All §4 and GR1/GR5. An independently typed R318 primitive clause supplies
its ORIGINAL license, complete packet and computed source-table lookup.
These construct the missing R306 child rather than assuming that child.
The original primitive license is never replaced by trace membership.

This is a conditional fragment theorem, not extraction of an authentic table
from source/native code. In particular `arms` below is universally quantified
legacy R293 consumer data, NOT a constructed independent source arm family.
The scoped-key/endpoint interpretation and source-owned whole-Call inventory
remain open. The last theorem applies original finite checking at the unchanged
R159 parent, for all source children and both annotation alternatives; it is
an inversion consequence, not construction of that parent.
-/
namespace YulangClosure.OriginalSourceUnionConsumerR338

open OriginalSource OriginalSourceInterpretation OriginalSourceEnvironment
open OriginalSourceChecking SourceSignatureConstruction SourceContributionConstruction
open ComputedCallUnionRealizationR293 ComputedCallPhaseDescriptorR306
open ComputedCallTypedFormationR310

variable {s : Sorts} {View : Type} {Joint : Type}

/-- The actual registered result has the original primitive's exact licensed
projection. Owner, whole dependent packet, and license are preserved together;
the result adds only the real alternative edge to the provenance route.
There is no supplied child contribution and no license is inferred from a
semantic trace packet. The lookup identifies an existing original introduction.
-/
theorem primitive_result_fields (inputs : Inputs s) (state : Decoded s View)
    (scope : List Binder) (graph : Graph (RawObservation s)) (old : Relations graph)
    (ops : Operators graph) (site : Site) (left right : Nat)
    (source : Endpoint) (arms : List Endpoint) (intro : Introduction (RawObservation s))
    (found : graph.node left = some (.primitive intro))
    (catalogueAgreement : intro.catalogue = branchCatalogue inputs state scope source)
    (raw : RawObservation s) (packet : Packet intro.catalogue raw)
    (licensed : intro.License raw packet.port packet.value) :
    let added := unionNode inputs state scope site left right source arms
    let installed := installUnion inputs state scope graph site left right source arms
    ∃ (result : DeclContribution installed
      (relations installed (appendRelations graph added old) inputs state scope site source arms)
      (appendOperators graph added ops) graph.nodes.length raw added
      (injectSource inputs state scope source arms (catalogueAgreement ▸ packet))),
      ∃ field : result.Projection,
        (result.project field).occurrence.owner = intro.owner ∧
        (result.project field).occurrence.route = [.alternative site false] ∧
        HEq (result.project field).packet packet.value ∧
        HEq (result.project field).license licensed := by
  rcases intro with ⟨owner, occurrence, kind, catalogue, License⟩
  dsimp only at catalogueAgreement
  subst catalogue
  let intro : Introduction (RawObservation s) :=
    ⟨owner, occurrence, kind, branchCatalogue inputs state scope source, License⟩
  let added := unionNode inputs state scope site left right source arms
  let installed := installUnion inputs state scope graph site left right source arms
  let rel := relations installed (appendRelations graph added old)
    inputs state scope site source arms
  let operators := appendOperators graph added ops
  have originalFound : installed.node left = some (.primitive intro) :=
    original_node_retained graph added left (.primitive intro) found
  let child : DeclContribution installed rel operators left raw (.primitive intro) packet :=
    .primitive originalFound packet licensed
  let result := sourceContribution inputs state scope site source arms installed
    (appendRelations graph added old) operators graph.nodes.length left right raw
    (.primitive intro) rfl packet
    (union_readback inputs state scope graph site left right source arms) child
  exact ⟨result, (), rfl, rfl, HEq.rfl, HEq.rfl⟩

/-- Actual application to R306: its completed child and its graph lookup
are constructed from the primitive's own raw license and table clause.
The complete catalogue equation remains explicit: source ownership alone
does not identify a primitive packet with an opaque trace interpretation.
The result retains the exact original license and all dependent fields. -/
theorem table_primitive_registered (inputs : Inputs s) (state : Decoded s View)
    (scope : List Binder) {n : Nat}
    (table : OriginalClauseCompilerR318.Local.Table (RawObservation s) n)
    (key : Fin n) (kind : OriginKind)
    (license : (whole : RawObservation s) → (port : (table.interfaces key).Port) →
      (table.interfaces key).Packet whole port → Type)
    (formed : table.clauses key = .primitive kind license)
    (site : Site) (right : Nat) (source : Endpoint) (arms : List Endpoint)
    (catalogueAgreement : table.interfaces key = branchCatalogue inputs state scope source)
    (raw : RawObservation s) (packet : Packet (table.interfaces key) raw)
    (licensed : license raw packet.port packet.value) :
    let graph := OriginalClauseCompilerR318.Local.graph table
    let old := OriginalClauseCompilerR318.Local.legacyRelations table
    let ops := OriginalClauseCompilerR318.Local.operators table
    let added := unionNode inputs state scope site key.val right source arms
    let installed := installUnion inputs state scope graph site key.val right source arms
    ∃ (result : DeclContribution installed
      (relations installed (appendRelations graph added old) inputs state scope site source arms)
      (appendOperators graph added ops) graph.nodes.length raw added
      (injectSource inputs state scope source arms (catalogueAgreement ▸ packet))),
      ∃ field : result.Projection,
        (result.project field).occurrence.owner = (table.identity key).operationOwner ∧
        (result.project field).occurrence.route = [.alternative site false] ∧
        HEq (result.project field).packet packet.value ∧
        HEq (result.project field).license licensed := by
  have found := OriginalClauseCompilerR318.Local.lookup table key
  simp only [OriginalClauseCompilerR318.Local.node, formed] at found
  exact primitive_result_fields inputs state scope
    (OriginalClauseCompilerR318.Local.graph table)
    (OriginalClauseCompilerR318.Local.legacyRelations table)
    (OriginalClauseCompilerR318.Local.operators table) site key.val right source arms
    (OriginalClauseCompilerR318.Local.introduction table key kind license)
    found catalogueAgreement raw packet licensed

/-- Apply the ORIGINAL R159 parent to original finite checking, with the
SAME admitted ViewLogic candidate. Its genuine computation Checking is an
output, rather than an additional assumed result check. Every remaining App
local and both children still belong to that unchanged parent derivation.

This theorem is deliberately a consequence of a parent derivation. It does
not claim that the raw primitive license constructs the whole source Call.
For every original finite arm inventory, original caller-image membership
then has R293's complete source-tag packet and the independently fixed target.
-/
theorem app_parent_result (inputs : Inputs s) (registry : GuardRegistry inputs)
    (readout : RuntimeReadout s View) (ports : PortReadout s View)
    (declarations : Declarations inputs registry) (admissions : LocalAdmissions s View)
    (original : Kernel (Payload s View)) (environment : Environment (Payload s View))
    (context : Context) (mark : Mark) (callee argument : Source .expression)
    (parent : SourceJudgment
      (OriginalSourceChecking.kernel inputs registry declarations
        (environmentReading inputs readout ports)
        (admissionKernel inputs readout admissions original))
      environment context (.app mark callee argument)) :
    ∃ occurrence data state,
      decode readout environment = some state ∧
      admissions.logical state ⟨mark.site, .viewLogic, 0⟩ .viewLogic data ∧
      let after := environment.extend ⟨mark.site, .viewLogic, 0⟩
        (scopeCandidate environment occurrence (.logical .viewLogic data))
      Checking (OriginalSourceChecking.kernel inputs registry declarations
        (environmentReading inputs readout ports)
        (admissionKernel inputs readout admissions original)) after
        ⟨.computation, mark.site, context,
          ⟨mark.site, .callableImage⟩, ⟨mark.site, .synthesis⟩⟩ ∧
      ∀ (arms : List Endpoint) (raw : RawObservation s),
        Meaning inputs (.trace (raw.atInterface
          ((state.logical data).interfaces ⟨mark.site, .callableImage⟩))) →
        (unionBody inputs (state.logical data) ⟨mark.site, .callableImage⟩ arms raw).Holds
          (Meaning inputs) ∧
        Meaning inputs (.trace (raw.atInterface
          ((state.logical data).interfaces ⟨mark.site, .synthesis⟩))) := by
  obtain ⟨_, candidate, admitted, body⟩ :=
    (SourceAppAdmissionR159.app_source_iff _ _ _ _ _ _).mp parent
  obtain ⟨occurrence, data, state, rfl, decoded, accepted⟩ :=
    (SourceAppAdmissionR159.admitted_view_iff inputs readout admissions environment
      mark.site candidate).mp admitted
  have locals := (SourceAppAdmissionR159.app_continuation_iff _ _ _ _ _ _).mp body
  have localCheck := locals.1 _
    (OriginalUnionOwnerR292.app_computation_premise context mark callee argument)
  cases localCheck with
  | checking checked =>
    refine ⟨occurrence, data, state, decoded, accepted, checked, ?_⟩
    intro arms raw member
    exact app_result_pair inputs registry readout ports declarations
      (admissionKernel inputs readout admissions original) environment context mark
      occurrence data state decoded arms raw checked member

end YulangClosure.OriginalSourceUnionConsumerR338
