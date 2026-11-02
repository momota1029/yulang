# R241 frozen assignment handoff

Sprint-ID: original-literal-carrier-realization-r241  
Contract revision: admitted 2026-11-02  
Contract SHA-256: e986f1ce74646e819f2be16a2b4554c76d8e839a2189b3bc62e4796b2b955a2e  
Assignment-ID: sol-r241-literal-carrier  
Handoff revision: 1  
Author/worker: /root/sol_r241_literal_carrier; no descendants or other contributors  
Session: 01a1873a-a93b-7dc3-a8ce-028a7b543a80 (primary snapshot identifier)  
Requested model/effort: gpt-6.1-sol / high. Observed effective model/effort: UNKNOWN / UNKNOWN.

## Outcome and parent application

Outcome class: candidate; exact original-consumer/frame audit with an explicit
semantic construction boundary. Not a completed carrier realization, passing
file check, independent review, source/native correspondence, or production authority.

Unchanged parent:
`YulangClosure.SourceProblem.InferenceSoundness p` in
`notes/theory/lean/YulangClosure/Contracts.lean:128`:

```text
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

Parent-premise delta: **zero**. The local Build equivalence was applied to the
existing original `source_reconstruction` consumer, yielding
`folded_literal_source_rule_exact`. This exposes the precise original source
leaf obligations; it does not discharge them or instantiate the parent.
There is no assumed `LiteralAtom`, source judgment, ground law, selected solver
result or source/native success in place of the missing construction.

The universal `literal : OriginalSource.Literal` in all constructor equations
covers **unit, bool, int, floatBits, string, bytes, path, character**, including
their complete payloads. The analyzed source leaf is the unannotated literal
base introduction. Annotated literals and enclosing contextual/checking,
method and adapter alternatives remain supported but unproved; none is
excluded or reset.

## First missing original equation and owners

The first missing data construction is an original representation of the
adopted `Value(τ(l))` and `v(l)`. `Sorts.Descriptor` and `Sorts.Value`
are independent opaque types, not Paper types. The frozen inputs supply no
canonical original descriptor/value constructors or Paper-to-original maps.
Required map signatures can be described as
`valueDescriptor : PaperTypes.Ty → s.Descriptor` and
`literalValue : PaperTypes.Literal → s.Value`; these are **requirements,
not definitions or assumed maps introduced by this packet**.

After such independently justified representations exist, the first required
commuting equation at the actual decoded assignment is:

```text
state.assignment.row q =
  ⟨valueDescriptor (PaperTypes.literalType (toPaperLiteral l)),
    literalValue (toPaperLiteral l), r, e₀⟩
```

Owners: `OriginalSourceInterpretation.Sorts.Descriptor/Value`,
`SourceAssignment.row` (finalRoot endpoint), and the independently fixed
original model interpreting those sorts. R240's Paper-valued
`LiteralAssignment`/`sourceLiteralRow` does not define these original carriers.

Even if that equality is established, the **exact existing original consumer**
requires the following, not R240's surrogate `originalLiteralDeclaration`:

```text
∃ state, OriginalSourceEnvironment.decode readout environment = some state ∧
  declarations l (state.assignment.row q) ∧
  inputs.valueForm (state.assignment.descriptor ⟨q, .finalRoot⟩) = .ground ∧
  inputs.ground (state.assignment.row q)
```

This is the RHS of both delivered `folded_literal_build_exact` and
`folded_literal_source_rule_exact`. Owners:
`OriginalSourceInterpretation.LiteralDeclaration`,
`Inputs.valueForm`, `Inputs.ground`, and
`OriginalSourceEnvironment.foldedLiteralKernel`.
The adopted canonical generator has no field constraining those independent
relations; no fact about them follows merely from its Paper equalities.
No new law supplying this RHS was introduced.

The original pure-Return bridge additionally needs an original interface and
observation representation for `Comp(empty,τ(l))`, then the exact equation

```text
inputs.traceForm returned = .pureReturn (state.assignment.row q)
```

at the original event, plus the *existing* Return consumer's event coherence,
observation guards, world meaning, same-event equation, value meaning and
observation fields. Owners: `Sorts.Interface/Observation`,
`Inputs.traceForm/observationGuards/observationFields`,
`OriginalSourceInterpretation.return_observation_iff`.
There is no original interface/effect grammar or trace-form realization in
the frozen generator model that proves this equation. L1 fixes intrinsic
purity but does not discharge contextual effects or these independent inputs.
The existing membership consumer also retains `GroundLaw inputs`; it was
inspected and audited, not assumed as a new theorem.

These are genuine definition/model boundaries. Choosing sorts, populating
input relations or defining satisfaction to force these facts would make a
semantic/model choice beyond this trial. No such choice was made.

## Independently derived original equations

The source file contains eight declarations; their full types are preserved in
the attempted-check output below.

- `canonical_data_at_original_coordinates`: adopted Paper descriptor/value
  equality at arbitrary original root, complete Event, scope and shared witness.
  This deliberately does not identify Paper data with original carriers.
- `original_literal_atom_exact`: actual payload-bearing original atom iff the
  original declaration, ground classification and ground relation hold.
- `folded_literal_build_exact`: actual original Build iff the decoded-prefix
  assignment satisfies those three local facts.
- `folded_literal_source_rule_exact`: the preceding equivalence applied to the
  existing original source reconstruction consumer.
- `original_assignment_frame_commutes`: decode equals the actual full stored
  frame fold from the original root.
- `logical_literal_row_commutes`: descriptor update and η/witness update,
  preserving original value, root and all other event components.
- `shared_literal_row_commutes`: Shared frames preserve the whole literal row;
  Shared.witness is not substituted for Event.witness.
- `runtime_literal_row_commutes`: endpoint object fold and runtime event readout
  using the complete fixed prefix and complete incoming event.

Synthesis, writtenTarget and finalRoot remain distinct original ports. All row
equations use the actual finalRoot consumer and make no endpoint identification.
No event fields, ambient effects, scope or witness are discarded.

Source path:
raw `Source.literal` → `sourceRules` literal atom → symbolic `Build` →
`foldedLiteralKernel` → complete `decode` frame fold → original
`LiteralAtom` → existing `source_reconstruction`.
Native/Rust correspondence was not inspected or claimed in this packet.

Prior work reused: R236 direct payload generator and exact Build equation;
original source reconstruction, folded literal consumer, original frame
decoder and Return interface. R240 was read at its actual Paper-valued premises
and retained as BLOCKED/model-incomplete. Its surrogate consumer was not
promoted, imported or reused as an original-carrier theorem.

## Artifact, direct dependency hashes and authors

Frozen artifact:
`notes/theory/lean/YulangClosure/OriginalLiteralCarrierRealizationR241.lean`  
SHA-256: **49bbe56ee5525f1a7a5b3db2d5c2b04737468cdaa864c761fd6465e1af914d8a**  
Size: 9,286 bytes. Sole author: /root/sol_r241_literal_carrier.

Frozen inputs (actual bytes checked at assignment execution):

| Input | SHA-256 |
| --- | --- |
| R240 sprint contract | 55fd70f4574dff2cbb91f32f880b5b24fa37f100d1352fb0a4fc96e3312468a6 |
| OriginalLiteralSolutionModelR240.lean | 64171c0998e9f593589988fbade579ce0f3b342d8cd1194b88a7857ba9f8deff |
| 2026-11-02-literal-l1-adoption.md | f69a11121b0bade01586293fbda5500c4264424c3ac568fd1336ebb1b2eec9b8 |
| 2026-11-02-canonical-literal-generation-adoption.md | dcea2c3e10f06f34c895bdbf9ab59aaeb2c2629648db71aa1a8a834d034a0c48 |
| OriginalSourceInterpretation.lean | feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef |
| OriginalSourceEnvironment.lean | 0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132 |
| Contracts.lean | 2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e |
| CanonicalLiteralGeneratorR236.lean | 9564501e59b8f595a4630e812728412efc0e213c1281e4a899a16fe8efef235c |
| OriginalSourceGeneration.lean | 126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef |
| CanonicalSourceInferenceModelR196.lean | 69d551760efc1b40f9235e749c4d2edde3e439b2cb91655495bf1c22d7d55c7c |

The two direct imports already had cached .olean files. R240 had no .olean and
was not imported or compiled. Input authors remain their existing repository
provenance; this worker did not modify or coauthor those inputs.

## Check and complete axiom receipt

Native executables resolved read-only with `elan which lake`:
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/`.
The lookup emitted a latest-release query warning and selected the existing
installation; no installation was attempted.

Observed versions:

```text
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
Lean (version 4.35.0, x86_64-unknown-linux-gnu,
commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
```

Exactly one targeted check was run from `notes/theory/lean`:

```sh
env LEAN_PATH=.lake/build/lib/lean LEAN_NUM_THREADS=1 timeout 240 /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean -j1 -M1024 YulangClosure/OriginalLiteralCarrierRealizationR241.lean
```

**Exit 1.** A separate helper `original_literal_ports_distinct` had a tactic
punctuation/parser error and consequently printed a `sorryAx` dependency.
That helper and its two audit lines were removed after the check.
No proof-hole declaration was retained and no unchecked replacement was added.
All eight substantive declarations below were elaborated and had full types
and axiom lists printed during that same run. Their proof bytes are unchanged.
**The final post-removal file bytes were NOT_RECHECKED. A passing file is not
claimed.** No second check was run.

Axiom results for the eight retained declarations:

| Declaration | Complete printed dependencies |
| --- | --- |
| canonical_data_at_original_coordinates | propext |
| original_literal_atom_exact | propext, Quot.sound |
| folded_literal_build_exact | propext, Classical.choice, Quot.sound |
| folded_literal_source_rule_exact | propext, Classical.choice, Quot.sound |
| original_assignment_frame_commutes | propext |
| logical_literal_row_commutes | none |
| shared_literal_row_commutes | none |
| runtime_literal_row_commutes | propext |

Reused consumers: `return_observation_iff` uses propext;
`folded_generated_literal_membership` uses propext, Classical.choice, Quot.sound.
Final-source search found only `#print axioms` command matches, no holes,
project axioms, admits, native-decide assumptions or kernel bypass.
This search does not substitute for the missing post-removal file check.

Complete attempted-check stdout/stderr (including the removed helper failure):

```text
YulangClosure/OriginalLiteralCarrierRealizationR241.lean:49:6: error: unexpected identifier; expected '⟩'
YulangClosure/OriginalLiteralCarrierRealizationR241.lean:48:8: error: Insufficient number of fields for `⟨...⟩` constructor: Constructor `And.intro` has 2 explicit field, but only 1 was provided
YulangClosure/OriginalLiteralCarrierRealizationR241.lean:49:4: error: unsolved goals
site : Site
same : { site := site, port := Port.synthesis } = { site := site, port := Port.writtenTarget }
⊢ ?m.18
YulangClosure/OriginalLiteralCarrierRealizationR241.lean:48:24: error: Missing eliminator: An eliminator must be provided when multiple induction targets are specified and no default eliminator has been registered

Hint: Write `using <eliminator-name>` to specify an eliminator, or register a default eliminator with the attribute `[cases_eliminator]`
canonical_data_at_original_coordinates : ∀ (s : Sorts) (site : Site) (literal : Literal) (root : s.Root)
  (event : Event s) (scope : s.Scope) (witness : s.JointWitness),
  have result := CanonicalLiteralGeneratorR236.generate site literal root event scope witness;
  result.site = site ∧
    result.literal = literal ∧
      result.descriptor = PaperTypes.literalType (CanonicalLiteralGeneratorR236.toPaperLiteral literal) ∧
        result.value = PaperTypes.Value.literal (CanonicalLiteralGeneratorR236.toPaperLiteral literal) ∧
          result.root = root ∧ result.event = event ∧ result.scope = scope ∧ result.witness = witness
'YulangClosure.OriginalLiteralCarrierRealizationR241.canonical_data_at_original_coordinates' depends on axioms: [propext]
original_literal_ports_distinct : ∀ (site : Site),
  { site := site, port := Port.synthesis } ≠ { site := site, port := Port.writtenTarget } ∧
    { site := site, port := Port.synthesis } ≠ { site := site, port := Port.finalRoot } ∧
      { site := site, port := Port.writtenTarget } ≠ { site := site, port := Port.finalRoot }
'YulangClosure.OriginalLiteralCarrierRealizationR241.original_literal_ports_distinct' depends on axioms: [sorryAx]
@original_literal_atom_exact : ∀ {s : Sorts} (inputs : Inputs s) (declarations : LiteralDeclaration s)
  (assignment : SourceAssignment s) (context : Context) (site : Site) (literal : Literal),
  LiteralAtom inputs declarations assignment
      (CanonicalSourceInferenceModelR196.literalObligation context site literal) ↔
    declarations literal (assignment.row site) ∧
      inputs.valueForm (assignment.descriptor { site := site, port := Port.finalRoot }) = ValueForm.ground ∧
        inputs.ground (assignment.row site)
'YulangClosure.OriginalLiteralCarrierRealizationR241.original_literal_atom_exact' depends on axioms: [propext,
 Quot.sound]
@folded_literal_build_exact : ∀ {s : Sorts} {View : Type} (inputs : Inputs s) (readout : RuntimeReadout s View)
  (declarations : LiteralDeclaration s) (original : Kernel (Payload s View))
  (environment : Environment (Payload s View)) (context : Context) (site : Site) (literal : Literal),
  Satisfies (foldedLiteralKernel inputs readout declarations original site literal) environment
      (Build context (Source.literal { site := site } literal)) ↔
    ∃ state,
      decode readout environment = some state ∧
        declarations literal (state.assignment.row site) ∧
          inputs.valueForm (state.assignment.descriptor { site := site, port := Port.finalRoot }) = ValueForm.ground ∧
            inputs.ground (state.assignment.row site)
'YulangClosure.OriginalLiteralCarrierRealizationR241.folded_literal_build_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
@folded_literal_source_rule_exact : ∀ {s : Sorts} {View : Type} (inputs : Inputs s) (readout : RuntimeReadout s View)
  (declarations : LiteralDeclaration s) (original : Kernel (Payload s View))
  (environment : Environment (Payload s View)) (context : Context) (site : Site) (literal : Literal),
  SourceJudgment (foldedLiteralKernel inputs readout declarations original site literal) environment context
      (Source.literal { site := site } literal) ↔
    ∃ state,
      decode readout environment = some state ∧
        declarations literal (state.assignment.row site) ∧
          inputs.valueForm (state.assignment.descriptor { site := site, port := Port.finalRoot }) = ValueForm.ground ∧
            inputs.ground (state.assignment.row site)
'YulangClosure.OriginalLiteralCarrierRealizationR241.folded_literal_source_rule_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
@original_assignment_frame_commutes : ∀ {s : Sorts} {View : Type} (readout : RuntimeReadout s View)
  (environment : Environment (Payload s View)) (root : Root s View),
  environment.root = Payload.root root →
    decode readout environment = some (List.foldl (decodeFrame readout) root.decoded environment.frames)
'YulangClosure.OriginalLiteralCarrierRealizationR241.original_assignment_frame_commutes' depends on axioms: [propext]
@logical_literal_row_commutes : ∀ {s : Sorts} {View : Type} (state : Decoded s View) (data : Logical s View)
  (site : Site),
  (state.logical data).assignment.row site =
    { descriptor := put state.assignment.descriptor data.descriptors { site := site, port := Port.finalRoot },
      value := state.assignment.value { site := site, port := Port.finalRoot },
      root := state.assignment.root { site := site, port := Port.finalRoot },
      event :=
        have __src := state.assignment.event;
        { fiber := __src.fiber, eta0 := __src.eta0, eta := data.eta, history := __src.history, current := __src.current,
          witness := data.witness, scope := __src.scope, authority := __src.authority, incidence := __src.incidence,
          dictionary := __src.dictionary } }
'YulangClosure.OriginalLiteralCarrierRealizationR241.logical_literal_row_commutes' does not depend on any axioms
@shared_literal_row_commutes : ∀ {s : Sorts} {View : Type} (state : Decoded s View) (data : Shared s) (site : Site),
  (state.shared data).assignment.row site = state.assignment.row site
'YulangClosure.OriginalLiteralCarrierRealizationR241.shared_literal_row_commutes' does not depend on any axioms
@runtime_literal_row_commutes : ∀ {s : Sorts} {View : Type} (readout : RuntimeReadout s View) (state : Decoded s View)
  (binder : Binder) (data : Runtime s View) (site : Site),
  (Decoded.runtime readout state binder data).assignment.row site =
    have __src := (List.foldl Decoded.object state data.endpoints).assignment.row site;
    { descriptor := __src.descriptor, value := __src.value, root := __src.root,
      event := readout.event state.fixedFrames state.assignment.event binder data }
'YulangClosure.OriginalLiteralCarrierRealizationR241.runtime_literal_row_commutes' depends on axioms: [propext]
@return_observation_iff : ∀ {s : Sorts} (inputs : Inputs s) (row : TraceRow s) (value : ValueRow s),
  inputs.traceForm row = TraceForm.pureReturn value →
    (Meaning inputs (Query.trace row) ↔
      inputs.eventCoherent row.event ∧
        (inputs.observationGuards row).Valid ∧
          Meaning inputs (Query.world row.event) ∧
            (value.event = row.event ∧ Meaning inputs (Query.value value)) ∧
              (inputs.observationFields row).Holds (Meaning inputs))
'YulangClosure.OriginalSourceInterpretation.return_observation_iff' depends on axioms: [propext]
@folded_generated_literal_membership : ∀ {s : Sorts} {View : Type} (inputs : Inputs s),
  GroundLaw inputs →
    ∀ (readout : RuntimeReadout s View) (declarations : LiteralDeclaration s) (original : Kernel (Payload s View))
      (environment : Environment (Payload s View)) (state : Decoded s View),
      decode readout environment = some state →
        ∀ (context : Context) (site : Site) (literal : Literal),
          Satisfies (foldedLiteralKernel inputs readout declarations original site literal) environment
              (Build context (Source.literal { site := site } literal)) →
            Meaning inputs (Query.value (state.assignment.row site))
'YulangClosure.OriginalSourceEnvironment.folded_generated_literal_membership' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
def YulangClosure.SourceProblem.InferenceSoundness : {S C X E D A N : Type} → SourceProblem S C X E D A N → Prop :=
fun {S C X E D A N} p =>
  ∀ (s : S) (x : X) (d : D) (a : A),
    p.supported s → p.generates s x d → p.solves d a → ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a

```

## Resources, next step and stopped-writing receipt

Maximum allocation: 2,400 active seconds; no Astra, descendants, Cargo/tests,
Rust, Git, new dependencies, cache expansion or scratch outputs.
One 240-second-bounded native check was used; it finished before the first
followup poll, with initial wait 1.001 seconds. Exact total process/active time
was not supplied by runtime metadata and is UNKNOWN; the allocation was not
exhausted. UTC observations during work: 2026-11-02 02:17:28 and 02:19:40.
No build or -o output was requested; existing cache only, no new cache paths.

Next in-scope construction: none without independently supplied original
carrier/input realization evidence. Luna owns the next admission, fresh
nonproducer review and the post-review targeted check. This packet is ready
for that review as an explicit obstruction/preservation artifact, not parent
closure or production promotion.

Mutual TODO R241-CARRIER-1: under the unchanged InferenceSoundness parent,
locate or establish the original Value-descriptor/literal-value representations
and the decoded assignment commuting equation above. Required input: adopted
original carrier definitions, not Paper aliases. Proposed next output must
derive the actual three original local facts. Falsifier: the same adopted
generated Paper data with an original descriptor/ground interpretation that
does not satisfy the consumer. A test of R240's surrogate relation cannot
satisfy this TODO.

Mutual TODO R241-RETURN-1: supply the original Comp(empty,τ) interface and
raw Return observation representation, prove the exact traceForm equation,
then retain all original Return/world/guard/field obligations. Owner:
original semantic model and its trace/effect consumers. Falsifier: a traceForm
or observation interface that does not denote that same-event pure Return.

Exact new/scratch paths: only the two leased output files; no scratch paths.
Worker state: STOPPED at this handoff. Writes stopped after this revision;
no descendants, outstanding subprocesses, or unresolved descendant leases.
Both paths are frozen for Luna intake. No central state, rules, compiler,
tests, questions, Git state or another worker's output was written.

