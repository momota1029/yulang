import YulangClosure.OriginalInterfacePreservationR328
import YulangClosure.ComputedCallPhaseDescriptorR306

/-!
R329: witness-preserving transport of original R293 evidence through the R328
interface extension. No Holds-to-Evidence reification is used. Original trace
coherence, guards, world, Return/unfinished and observation fields are explicit.
This is transport of genuine existing packets, not an EI interpretation or a
construction of a licensed source child. R159 admission remains independent.
-/
namespace YulangClosure.OriginalEvidenceTransportR329
open OriginalSource OriginalSourceInterpretation OriginalSourceEnvironment
open SourceSignatureConstruction SourceContributionConstruction
open OriginalSourceChecking ComputedCallUnionRealizationR293
open OriginalInterfacePreservationR328
variable {s : Sorts} {G View : Type}

def upEvidence (base : Inputs s) (gen : Generated s G) :
    (body : Positive s) → Evidence (Meaning base) body →
      Evidence (Meaning (inputs base gen)) (upPositive body)
  | .guard _, e => e
  | .field q, e => ⟨meaning_preserve base gen q e.down⟩
  | .both a b, e => (upEvidence base gen a e.1, upEvidence base gen b e.2)
  | .either a _, .inl e => .inl (upEvidence base gen a e)
  | .either _ b, .inr e => .inr (upEvidence base gen b e)
  | .all _ body, e => fun d => upEvidence base gen (body d) (e d)
  | .existsE _ body, e => ⟨e.1, upEvidence base gen (body e.1) e.2⟩

def downEvidence (base : Inputs s) (gen : Generated s G) :
    (body : Positive s) → Evidence (Meaning (inputs base gen)) (upPositive body) →
      Evidence (Meaning base) body
  | .guard _, e => e
  | .field q, e => ⟨meaning_reflect base gen q e.down⟩
  | .both a b, e => (downEvidence base gen a e.1, downEvidence base gen b e.2)
  | .either a _, .inl e => .inl (downEvidence base gen a e)
  | .either _ b, .inr e => .inr (downEvidence base gen b e)
  | .all _ body, e => fun d => downEvidence base gen (body d) (e d)
  | .existsE _ body, e => ⟨e.1, downEvidence base gen (body e.1) e.2⟩

theorem down_up_evidence (base : Inputs s) (gen : Generated s G) (body : Positive s)
    (e : Evidence (Meaning base) body) :
    downEvidence base gen body (upEvidence base gen body e) = e := by
  induction body with
  | guard fact => rfl
  | field q => cases e; rfl
  | both a b ia ib => exact Prod.ext (ia e.1) (ib e.2)
  | either a b ia ib => cases e with
    | inl e => exact congrArg Sum.inl (ia e)
    | inr e => exact congrArg Sum.inr (ib e)
  | all D body ih => exact funext fun d => ih d (e d)
  | existsE D body ih => exact Sigma.ext rfl (heq_of_eq (ih e.1 e.2))

theorem up_down_evidence (base : Inputs s) (gen : Generated s G) (body : Positive s)
    (e : Evidence (Meaning (inputs base gen)) (upPositive body)) :
    upEvidence base gen body (downEvidence base gen body e) = e := by
  induction body with
  | guard fact => rfl
  | field q => cases e; rfl
  | both a b ia ib => exact Prod.ext (ia e.1) (ib e.2)
  | either a b ia ib => cases e with
    | inl e => exact congrArg Sum.inl (ia e)
    | inr e => exact congrArg Sum.inr (ib e)
  | all D body ih => exact funext fun d => ih d (e d)
  | existsE D body ih => exact Sigma.ext rfl (heq_of_eq (ih e.1 e.2))

/-- Right stays right even when both disjuncts hold. -/
theorem up_right (base : Inputs s) (gen : Generated s G) (a b : Positive s)
    (e : Evidence (Meaning base) b) :
    upEvidence base gen (.either a b) (.inr e) = .inr (upEvidence base gen b e) := rfl

/-- The original witness survives even when other witnesses are also valid. -/
theorem up_exists_witness (base : Inputs s) (gen : Generated s G)
    (D : Type) (body : D → Positive s) (e : Evidence (Meaning base) (.existsE D body)) :
    (upEvidence base gen (.existsE D body) e).1 = e.1 := rfl

theorem up_all_index (base : Inputs s) (gen : Generated s G)
    (D : Type) (body : D → Positive s) (e : Evidence (Meaning base) (.all D body)) (d : D) :
    upEvidence base gen (.all D body) e d = upEvidence base gen (body d) (e d) := rfl

/-- The original optional result, including its equality to the current event. -/
def returnBody (form : TraceForm s) (event : Event s) : Positive s :=
  match form with
  | .pureReturn value => .both (.guard (value.event = event)) (.field (.value value))
  | .unfinished => .guard True

def upReturnEvidence (base : Inputs s) (gen : Generated s G) (event : Event s) :
    (form : TraceForm s) → Evidence (Meaning base) (returnBody form event) →
      Evidence (Meaning (inputs base gen)) (returnBody (upForm form) (upEvent event))
  | .pureReturn value, e =>
      (⟨congrArg upEvent e.1.down⟩, ⟨meaning_preserve base gen (.value value) e.2.down⟩)
  | .unfinished, e => e

def downReturnEvidence (base : Inputs s) (gen : Generated s G) (event : Event s) :
    (form : TraceForm s) →
      Evidence (Meaning (inputs base gen)) (returnBody (upForm form) (upEvent event)) →
      Evidence (Meaning base) (returnBody form event)
  | .pureReturn value, e =>
      (⟨congrArg downEvent e.1.down⟩, ⟨meaning_reflect base gen (.value value) e.2.down⟩)
  | .unfinished, e => e

theorem down_up_return (base : Inputs s) (gen : Generated s G) (event : Event s)
    (form : TraceForm s) (e : Evidence (Meaning base) (returnBody form event)) :
    downReturnEvidence base gen event form (upReturnEvidence base gen event form e) = e := by
  cases form with
  | pureReturn value => exact Prod.ext rfl rfl
  | unfinished => rfl

theorem up_down_return (base : Inputs s) (gen : Generated s G) (event : Event s)
    (form : TraceForm s)
    (e : Evidence (Meaning (inputs base gen)) (returnBody (upForm form) (upEvent event))) :
    upReturnEvidence base gen event form (downReturnEvidence base gen event form e) = e := by
  cases form with
  | pureReturn value => exact Prod.ext rfl rfl
  | unfinished => rfl

/-- Transport the ACTUAL full trace clause, with no reification. The independent
outer coherence/observation guards are retained verbatim. -/
def upTraceEvidence (base : Inputs s) (gen : Generated s G) (row : TraceRow s)
    (e : Evidence (Meaning base) (clause base (.trace row))) :
    Evidence (Meaning (inputs base gen)) (clause (inputs base gen) (.trace (upTrace row))) :=
  (e.1, ⟨meaning_preserve base gen (.world row.event) e.2.1.down⟩,
    upReturnEvidence base gen row.event (base.traceForm row) e.2.2.1,
    upEvidence base gen (base.observationFields row) e.2.2.2)

def downTraceEvidence (base : Inputs s) (gen : Generated s G) (row : TraceRow s)
    (e : Evidence (Meaning (inputs base gen)) (clause (inputs base gen) (.trace (upTrace row)))) :
    Evidence (Meaning base) (clause base (.trace row)) :=
  (e.1, ⟨meaning_reflect base gen (.world row.event) e.2.1.down⟩,
    downReturnEvidence base gen row.event (base.traceForm row) e.2.2.1,
    downEvidence base gen (base.observationFields row) e.2.2.2)

theorem down_up_trace_evidence (base : Inputs s) (gen : Generated s G) (row : TraceRow s)
    (e : Evidence (Meaning base) (clause base (.trace row))) :
    downTraceEvidence base gen row (upTraceEvidence base gen row e) = e :=
  Prod.ext rfl (Prod.ext rfl (Prod.ext (down_up_return base gen _ _ _) (down_up_evidence base gen _ _)))

theorem up_down_trace_evidence (base : Inputs s) (gen : Generated s G) (row : TraceRow s)
    (e : Evidence (Meaning (inputs base gen)) (clause (inputs base gen) (.trace (upTrace row)))) :
    upTraceEvidence base gen row (downTraceEvidence base gen row e) = e :=
  Prod.ext rfl (Prod.ext rfl (Prod.ext (up_down_return base gen _ _ _) (up_down_evidence base gen _ _)))

/-- Every original endpoint is read from the same Decoded environment. -/
def upBranch (base : Inputs s) (gen : Generated s G) (state : Decoded s View)
    (scope : List Binder) (endpoint : Endpoint) {raw : RawObservation s}
    (p : Packet (branchCatalogue base state scope endpoint) raw) :
    Packet (branchCatalogue (inputs base gen) (upDecoded state) scope endpoint) (upRaw raw) :=
  ⟨p.port, upTraceEvidence base gen (raw.atInterface (state.interfaces endpoint)) p.value⟩

def downBranch (base : Inputs s) (gen : Generated s G) (state : Decoded s View)
    (scope : List Binder) (endpoint : Endpoint) {raw : RawObservation s}
    (p : Packet (branchCatalogue (inputs base gen) (upDecoded state) scope endpoint) (upRaw raw)) :
    Packet (branchCatalogue base state scope endpoint) raw :=
  ⟨p.port, downTraceEvidence base gen (raw.atInterface (state.interfaces endpoint)) p.value⟩

def upArms (base : Inputs s) (gen : Generated s G) (state : Decoded s View)
    (scope : List Binder) (arms : List Endpoint) {raw : RawObservation s}
    (p : Packet (armsCatalogue base state scope arms) raw) :
    Packet (armsCatalogue (inputs base gen) (upDecoded state) scope arms) (upRaw raw) :=
  ⟨p.port, upTraceEvidence base gen (raw.atInterface (state.interfaces (arms.get (p.port : Fin arms.length)))) p.value⟩

def downArms (base : Inputs s) (gen : Generated s G) (state : Decoded s View)
    (scope : List Binder) (arms : List Endpoint) {raw : RawObservation s}
    (p : Packet (armsCatalogue (inputs base gen) (upDecoded state) scope arms) (upRaw raw)) :
    Packet (armsCatalogue base state scope arms) raw :=
  ⟨p.port, downTraceEvidence base gen (raw.atInterface (state.interfaces (arms.get (p.port : Fin arms.length)))) p.value⟩

def upUnion (base : Inputs s) (gen : Generated s G) (state : Decoded s View)
    (scope : List Binder) (source : Endpoint) (arms : List Endpoint) {raw : RawObservation s}
    (p : Packet (unionCatalogue base state scope source arms) raw) :
    Packet (unionCatalogue (inputs base gen) (upDecoded state) scope source arms) (upRaw raw) :=
  match p with
  | ⟨.inl u, value⟩ => ⟨.inl u, upTraceEvidence base gen (raw.atInterface (state.interfaces source)) value⟩
  | ⟨.inr i, value⟩ => ⟨.inr i, upTraceEvidence base gen (raw.atInterface (state.interfaces arms[i])) value⟩

def downUnion (base : Inputs s) (gen : Generated s G) (state : Decoded s View)
    (scope : List Binder) (source : Endpoint) (arms : List Endpoint) {raw : RawObservation s}
    (p : Packet (unionCatalogue (inputs base gen) (upDecoded state) scope source arms) (upRaw raw)) :
    Packet (unionCatalogue base state scope source arms) raw :=
  match p with
  | ⟨.inl u, value⟩ => ⟨.inl u, downTraceEvidence base gen (raw.atInterface (state.interfaces source)) value⟩
  | ⟨.inr i, value⟩ => ⟨.inr i, downTraceEvidence base gen (raw.atInterface (state.interfaces arms[i])) value⟩

theorem down_up_branch (base : Inputs s) (gen : Generated s G) (state : Decoded s View)
    (scope : List Binder) (endpoint : Endpoint) {raw : RawObservation s}
    (p : Packet (branchCatalogue base state scope endpoint) raw) :
    downBranch base gen state scope endpoint (upBranch base gen state scope endpoint p) = p := by
  cases p with
  | mk port value => exact congrArg (Packet.mk port) (down_up_trace_evidence base gen _ value)

theorem up_down_branch (base : Inputs s) (gen : Generated s G) (state : Decoded s View)
    (scope : List Binder) (endpoint : Endpoint) {raw : RawObservation s}
    (p : Packet (branchCatalogue (inputs base gen) (upDecoded state) scope endpoint) (upRaw raw)) :
    upBranch base gen state scope endpoint (downBranch base gen state scope endpoint p) = p := by
  cases p with
  | mk port value => exact congrArg (Packet.mk port) (up_down_trace_evidence base gen (raw.atInterface (state.interfaces endpoint)) value)

theorem down_up_arms (base : Inputs s) (gen : Generated s G) (state : Decoded s View)
    (scope : List Binder) (arms : List Endpoint) {raw : RawObservation s}
    (p : Packet (armsCatalogue base state scope arms) raw) :
    downArms base gen state scope arms (upArms base gen state scope arms p) = p := by
  cases p with
  | mk port value => exact congrArg (Packet.mk port) (down_up_trace_evidence base gen _ value)

theorem up_down_arms (base : Inputs s) (gen : Generated s G) (state : Decoded s View)
    (scope : List Binder) (arms : List Endpoint) {raw : RawObservation s}
    (p : Packet (armsCatalogue (inputs base gen) (upDecoded state) scope arms) (upRaw raw)) :
    upArms base gen state scope arms (downArms base gen state scope arms p) = p := by
  cases p with
  | mk port value => exact congrArg (Packet.mk port) (up_down_trace_evidence base gen (raw.atInterface (state.interfaces (arms.get port))) value)

theorem down_up_union (base : Inputs s) (gen : Generated s G) (state : Decoded s View)
    (scope : List Binder) (source : Endpoint) (arms : List Endpoint) {raw : RawObservation s}
    (p : Packet (unionCatalogue base state scope source arms) raw) :
    downUnion base gen state scope source arms (upUnion base gen state scope source arms p) = p := by
  cases p with
  | mk port value =>
    cases port with
    | inl u => exact congrArg (Packet.mk (catalogue := unionCatalogue base state scope source arms) (whole := raw) (Sum.inl u)) (down_up_trace_evidence base gen _ value)
    | inr i => exact congrArg (Packet.mk (catalogue := unionCatalogue base state scope source arms) (whole := raw) (Sum.inr i)) (down_up_trace_evidence base gen _ value)

theorem up_down_union (base : Inputs s) (gen : Generated s G) (state : Decoded s View)
    (scope : List Binder) (source : Endpoint) (arms : List Endpoint) {raw : RawObservation s}
    (p : Packet (unionCatalogue (inputs base gen) (upDecoded state) scope source arms) (upRaw raw)) :
    upUnion base gen state scope source arms (downUnion base gen state scope source arms p) = p := by
  cases p with
  | mk port value =>
    cases port with
    | inl u => exact congrArg (Packet.mk (catalogue := unionCatalogue (inputs base gen) (upDecoded state) scope source arms) (whole := upRaw raw) (Sum.inl u)) (up_down_trace_evidence base gen (raw.atInterface (state.interfaces source)) value)
    | inr i => exact congrArg (Packet.mk (catalogue := unionCatalogue (inputs base gen) (upDecoded state) scope source arms) (whole := upRaw raw) (Sum.inr i)) (up_down_trace_evidence base gen (raw.atInterface (state.interfaces arms[i])) value)

theorem up_inject_source (base : Inputs s) (gen : Generated s G) (state : Decoded s View)
    (scope : List Binder) (source : Endpoint) (arms : List Endpoint) {raw : RawObservation s}
    (p : Packet (branchCatalogue base state scope source) raw) :
    upUnion base gen state scope source arms (injectSource base state scope source arms p) =
      injectSource (inputs base gen) (upDecoded state) scope source arms
        (upBranch base gen state scope source p) := rfl

theorem up_inject_arm (base : Inputs s) (gen : Generated s G) (state : Decoded s View)
    (scope : List Binder) (source : Endpoint) (arms : List Endpoint) {raw : RawObservation s}
    (p : Packet (armsCatalogue base state scope arms) raw) :
    upUnion base gen state scope source arms (injectArm base state scope source arms p) =
      injectArm (inputs base gen) (upDecoded state) scope source arms
        (upArms base gen state scope arms p) := rfl

/-- Duplicate endpoints do not merge the independent Fin positions. -/
theorem arm_slot_preserved (base : Inputs s) (gen : Generated s G) (state : Decoded s View)
    (scope : List Binder) (arms : List Endpoint) {raw : RawObservation s}
    (p : Packet (armsCatalogue base state scope arms) raw) :
    (upArms base gen state scope arms p).port = p.port := rfl


theorem trace_guards_preserved (base : Inputs s) (gen : Generated s G) (row : TraceRow s)
    (e : Evidence (Meaning base) (clause base (.trace row))) :
    (upTraceEvidence base gen row e).1 = e.1 := rfl

theorem trace_world_preserved (base : Inputs s) (gen : Generated s G) (row : TraceRow s)
    (e : Evidence (Meaning base) (clause base (.trace row))) :
    (upTraceEvidence base gen row e).2.1 =
      PLift.up (meaning_preserve base gen (.world row.event) e.2.1.down) := rfl

theorem trace_return_preserved (base : Inputs s) (gen : Generated s G) (row : TraceRow s)
    (e : Evidence (Meaning base) (clause base (.trace row))) :
    (upTraceEvidence base gen row e).2.2.1 =
      upReturnEvidence base gen row.event (base.traceForm row) e.2.2.1 := rfl

theorem trace_fields_preserved (base : Inputs s) (gen : Generated s G) (row : TraceRow s)
    (e : Evidence (Meaning base) (clause base (.trace row))) :
    (upTraceEvidence base gen row e).2.2.2 =
      upEvidence base gen (base.observationFields row) e.2.2.2 := rfl

/-- Adversarial nested case: the left branch also holds, every Bool witness
is valid, and each independent Nat index carries its own chosen witness. -/
def ambiguousBody : Positive s :=
  .either (.guard True) (.existsE Bool fun _ => .all Nat fun _ => .existsE Bool fun _ => .guard True)

theorem ambiguous_right_nested (base : Inputs s) (gen : Generated s G)
    (chosen : Bool) (atIndex : Nat → Bool) :
    upEvidence base gen ambiguousBody
        (Sum.inr ⟨chosen, fun n => ⟨atIndex n, ⟨True.intro⟩⟩⟩) =
      Sum.inr ⟨chosen, fun n => ⟨atIndex n, ⟨True.intro⟩⟩⟩ := rfl

theorem multiple_witnesses_distinct (base : Inputs s) (gen : Generated s G) :
    upEvidence base gen (.existsE Bool fun _ => .guard True) ⟨true, ⟨True.intro⟩⟩ ≠
      upEvidence base gen (.existsE Bool fun _ => .guard True) ⟨false, ⟨True.intro⟩⟩ := by
  intro same
  have impossible := congrArg Sigma.fst same
  exact Bool.noConfusion impossible

theorem transported_source_meaning (base : Inputs s) (gen : Generated s G)
    (state : Decoded s View) (scope : List Binder) (source : Endpoint) {raw : RawObservation s}
    (packet : Packet (branchCatalogue base state scope source) raw) :
    Meaning (inputs base gen) (.trace ((upRaw raw).atInterface ((upDecoded state).interfaces source))) :=
  source_packet_meaning (inputs base gen) (upDecoded state) scope source (upRaw raw)
    (upBranch base gen state scope source packet)

open ComputedCallPhaseDescriptorR306

/-- Apply the original R306 consumer to its genuine original licensed child.
Transport the resulting tagged packet separately; no old graph is asserted to
be a graph over the extended raw sort. The genuine child remains explicit. -/
theorem source_registered_with_transport (base : Inputs s) (gen : Generated s G)
    (state : Decoded s View) (scope : List Binder)
    (graph : Graph (RawObservation s)) (old : Relations graph) (operators : Operators graph)
    (site : Site) (left right : Nat) (source : Endpoint) (arms : List Endpoint)
    (raw : RawObservation s) (childNode : Node (RawObservation s))
    (sameCatalogue : childNode.catalogue = branchCatalogue base state scope source)
    (packet : Packet (branchCatalogue base state scope source) raw)
    (child : DeclContribution graph old operators left raw childNode (sameCatalogue ▸ packet)) :
    (let added := unionNode base state scope site left right source arms
     let installed := installUnion base state scope graph site left right source arms
     Nonempty (DeclContribution installed
       (relations installed (appendRelations graph added old) base state scope site source arms)
       (appendOperators graph added operators) graph.nodes.length raw added
       (injectSource base state scope source arms packet))) ∧
    upUnion base gen state scope source arms (injectSource base state scope source arms packet) =
      injectSource (inputs base gen) (upDecoded state) scope source arms
        (upBranch base gen state scope source packet) ∧
    Meaning (inputs base gen) (.trace ((upRaw raw).atInterface ((upDecoded state).interfaces source))) :=
  ⟨source_contribution_registered base state scope graph old operators site left right source arms raw
      childNode sameCatalogue packet child,
    up_inject_source base gen state scope source arms packet,
    transported_source_meaning base gen state scope source packet⟩

/-- The original independent arm license is consumed by R306, with its exact
Fin slot and complete recursively transported evidence in the injection. -/
theorem arm_registered_with_transport (base : Inputs s) (gen : Generated s G)
    (state : Decoded s View) (scope : List Binder)
    (graph : Graph (RawObservation s)) (old : Relations graph) (operators : Operators graph)
    (site : Site) (left right : Nat) (source : Endpoint) (arms : List Endpoint)
    (raw : RawObservation s) (childNode : Node (RawObservation s))
    (sameCatalogue : childNode.catalogue = armsCatalogue base state scope arms)
    (packet : Packet (armsCatalogue base state scope arms) raw)
    (child : DeclContribution graph old operators right raw childNode (sameCatalogue ▸ packet)) :
    (let added := unionNode base state scope site left right source arms
     let installed := installUnion base state scope graph site left right source arms
     Nonempty (DeclContribution installed
       (relations installed (appendRelations graph added old) base state scope site source arms)
       (appendOperators graph added operators) graph.nodes.length raw added
       (injectArm base state scope source arms packet))) ∧
    upUnion base gen state scope source arms (injectArm base state scope source arms packet) =
      injectArm (inputs base gen) (upDecoded state) scope source arms
        (upArms base gen state scope arms packet) :=
  ⟨arm_contribution_registered base state scope graph old operators site left right source arms raw
      childNode sameCatalogue packet child,
    up_inject_arm base gen state scope source arms packet⟩

end YulangClosure.OriginalEvidenceTransportR329
