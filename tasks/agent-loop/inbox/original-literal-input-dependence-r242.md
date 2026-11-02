# R242 frozen assignment handoff

Sprint-ID: original-literal-input-dependence-r242  
Contract revision: admitted 2026-11-02  
Contract SHA-256: 3f45a9f03aaadbe1c2c65b43c93c39aa13da804c411c8c3a89ad5baf8b6dd9b9  
Assignment-ID: sol-r242-input-dependence  
Handoff revision: 1  
Author / actual worker: /root/sol_r242_input_dependence; no descendants or coauthors  
Session: 01a1873a-a93b-7dc3-a8ce-028a7b543a80 (primary snapshot identifier)  
Requested model/effort: gpt-6.1-sol / high. Observed effective model/effort: UNKNOWN / UNKNOWN.

## Outcome and unchanged parent

Outcome class: candidate parameter-sensitivity result, with individually
elaborated substantive declarations. **The one file check exited 1; final
post-removal file bytes are NOT_RECHECKED.** No independent review or passing
final-file check is claimed. This is not a source-qualified counterexample,
a Yulang semantic choice, a completed source model, or production authority.

The unchanged parent at `YulangClosure.SourceProblem.InferenceSoundness`,
`Contracts.lean:128`, is:

```text
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

Parent-premise delta: **zero**. The paired Build result is applied through
the actual `OriginalSource.source_reconstruction` equivalence in
`ground_variation_changes_original_source_rule`. The resulting source
judgments are relative to two diagnostic input records and their actual
original folded kernels. Neither is identified with the intended fixed
Yulang interpretation. No original arbitrary-solution premise or sameScoped
witness has been discharged, and no SourceProblem was instantiated.

## Actual Build dependence

For arbitrary original Sorts and View, fix all of:

- inputs, RuntimeReadout, LiteralDeclaration, supplied original Kernel;
- the complete Environment (root and stored frame prefix), decoded state,
  source Context, Site and payload-bearing Literal;
- the explicit premises
  `decode readout environment = some state`,
  `declarations literal (state.assignment.row site)`, and
  `inputs.valueForm (state.assignment.descriptor ⟨site, .finalRoot⟩) = .ground`.

Then `build_at_fixed_decode` proves that the actual folded original Build
consumer is equivalent to
`inputs.ground (state.assignment.row site)`.
Decode uniqueness rules out satisfying its existential by choosing a different
assignment from the same environment/prefix.

`ground_variation_changes_original_build` applies this equation to the
explicit pair:

```lean
{inputs with ground := fun _ => True}
{inputs with ground := fun _ => False}
```

The first actual Build is satisfied and the second is not. The source-rule
theorem applies that pair to the existing reconstruction consumer.

Every non-ground Inputs field is definitionally the same original projection.
The checked `ground_update_preserves_other_fields` states that restoring the
original ground projection restores the entire original record. The raw
printed types below expand every projection, including dependent challenge
fields, making this invariant explicit. There is no replacement of declaration,
valueForm, readout or source generation. The explicit declaration and
classification premises remain hypotheses; neither is derived from canonical
Paper generation here.

All statements quantify over the full original Literal type: unit, bool, int,
floatBits, string, bytes, path and character with complete payloads. The same
site and finalRoot endpoint are used; synthesis/writtenTarget/finalRoot are
not identified. Root, complete event/fiber, scope and shared witness remain
those of the same decoded row and generator arguments. No supported source
form or checking alternative is removed.

## TraceForm, generator and decoder

The adopted generator and actual decoder do not take Inputs. The two
`*_inputs_noninterference` declarations record this as constant-function
equalities at arbitrary fixed root/event/scope/witness and fixed stored
environment/readout. They are auxiliary definitional facts, not independent
soundness bridges.

`trace_update_preserves_literal_kernel` proves equality of the actual
foldedLiteralKernel after any traceForm-only update. This gives literal Build
noninterference as an immediate application of equality, while the same update
can change the branch inspected by the original Return consumer.
`trace_update_preserves_other_fields` establishes the whole-record restoration
invariant, including unchanged ground.

`diagnostic_pure_return_consumer` applies the existing
`OriginalSourceInterpretation.return_observation_iff` to the explicit
trace-only record update `{inputs with traceForm := fun _ => .pureReturn value}`.
`diagnostic_unfinished_consumer` applies the existing unfinished consumer to
`{inputs with traceForm := fun _ => .unfinished}`.
Their full types retain event coherence, observation guards, world Meaning,
the Return branch's same-event and value Meaning, and all observation fields.
Each RHS uses its own varied record's Meaning. **No Meaning invariance across
trace updates is asserted.** These applications do not prove that the intended
original trace input equals either diagnostic update.

At the unchanged original literal coordinates, specialize the universally
quantified value to `state.assignment.row site`. The still-missing original
Return equation is exactly:

```lean
inputs.traceForm returned = .pureReturn (state.assignment.row site)
```

It must be justified for the independently represented original
Comp(empty, τ(l)) observation, with
`returned.event = state.assignment.event`, coherent event, guards, world
Meaning, value Meaning and positive observation fields. Generator/decoder
noninterference supplies none of these laws. The existing
`folded_generated_literal_membership` additionally requires its original
`GroundLaw inputs`; it is inspected/audited below, not assumed by this packet.
The OriginalReturnWorld source remains unchanged: actual raw Return and its
world/registry/readout prerequisites are separate operational obligations.

## Remaining equations, owners and next step

The first source-model boundary remains the independently justified original
descriptor/value representation and its decoded-row commuting equation:

```text
state.assignment.row q =
  ⟨valueDescriptor (PaperTypes.literalType (toPaperLiteral l)),
    literalValue (toPaperLiteral l), originalRoot, originalEvent⟩
```

The map names above describe required signatures, not definitions introduced
by this packet. OriginalSourceInterpretation.Sorts.Descriptor/Value and the
original interpretation owner must supply these representations.

The actual consumer still needs original declaration, valueForm and ground
facts at that decoded row, plus the exact original decode/readout bridge.
Owners: LiteralDeclaration, Inputs.valueForm/ground,
OriginalSourceEnvironment.decode/foldedLiteralKernel. The same pure-Return
equation above is owned by Inputs.traceForm and the original observation/
interface interpretation. Full source coverage, sameScoped and native/Rust
correspondence remain open.

Stable mutual TODO R242-ORIGINAL-INPUT-EQUATIONS:
Luna owns admission of independently justified original carrier/readout/
declaration/ground/Return equations. Required inputs are the original accepted
source interpretation and arbitrary satisfying-assignment bridge. Proposed
output is an application at the unchanged parent edge, with the exact
falsifier: at one fixed decoded row satisfying declaration and ground
classification, a ground-only True/False update changes actual Build while
generator and decode stay identical. Therefore canonical generator equations
alone cannot force that consumer independently of the missing input law.
This TODO grants no semantics, writes or resources.

No additional in-envelope construction remains after the one-check stop.
Next is Luna-assigned fresh independent review, then Luna's one permitted
targeted pinned check of the frozen final bytes and full axiom audit. A new
original-semantic construction requires Luna's authority before writing.

## Prior work, source/native evidence and authors

Reused: R241's exact Build proof, copied with attribution because R241 has no
cached olean; the original source reconstruction consumer; R236's actual
payload-preserving generator; actual OriginalSourceEnvironment decoder and
folded kernel; original Return and unfinished consumer theorems.
No R240 surrogate carrier/declaration/consumer is imported or promoted.
Historical proofs are used only at their actual premises.

Source path: OriginalSource.literal → original literalObligation/Build →
foldedLiteralKernel → actual decode frame fold → original LiteralAtom →
source_reconstruction. This is formal-source evidence only. No Rust/native
constructor emission, arbitrary satisfying-solution readout, actual native
Return or production result is claimed. OriginalReturnWorld was read as a
boundary dependency, not imported or rebuilt.

## Frozen artifact and dependencies

Artifact: `notes/theory/lean/YulangClosure/OriginalLiteralInputDependenceR242.lean`  
SHA-256: **b5a5ac8580d71ee15dd595fd2712316451df28a68398a524d558f72a12cee649**  
Size: 12,233 bytes. Sole new author: /root/sol_r242_input_dependence.
The reproduced exact Build proof retains R241 worker authorship attribution.
Other dependency authors remain their existing repository provenance.

Hashes were checked before construction and rechecked after the sole check:

| Dependency | SHA-256 |
| --- | --- |
| R242 sprint contract | 3f45a9f03aaadbe1c2c65b43c93c39aa13da804c411c8c3a89ad5baf8b6dd9b9 |
| OriginalLiteralCarrierRealizationR241.lean | 49bbe56ee5525f1a7a5b3db2d5c2b04737468cdaa864c761fd6465e1af914d8a |
| R241 handoff | c6e8774cb44b9bfb02a4dd865ec9156b10c4ecbaaca8933c9c8ae2d5678207e3 |
| L1 adoption | f69a11121b0bade01586293fbda5500c4264424c3ac568fd1336ebb1b2eec9b8 |
| canonical generation adoption | dcea2c3e10f06f34c895bdbf9ab59aaeb2c2629648db71aa1a8a834d034a0c48 |
| OriginalSourceInterpretation.lean | feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef |
| OriginalSourceEnvironment.lean | 0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132 |
| OriginalReturnWorld.lean | 0710f5d969af927c8f42b42f4972ba4f53ddce4ddb082e9d3d360e90c9ccf12b |
| Contracts.lean | 2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e |
| CanonicalLiteralGeneratorR236.lean | 9564501e59b8f595a4630e812728412efc0e213c1281e4a899a16fe8efef235c |
| OriginalSourceGeneration.lean | 126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef |
| CanonicalSourceInferenceModelR196.lean | 69d551760efc1b40f9235e749c4d2edde3e439b2cb91655495bf1c22d7d55c7c |

## One-check receipt and complete axiom results

Resolved installed native Lake read-only using `elan which lake`:
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`.
Observed versions:

```text
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
Lean (version 4.35.0, x86_64-unknown-linux-gnu,
commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
```

One native file check from notes/theory/lean:

```sh
env LEAN_PATH=.lake/build/lib/lean LEAN_NUM_THREADS=1 timeout 240 /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean -j1 -M1024 YulangClosure/OriginalLiteralInputDependenceR242.lean
```

Exit **1**. Auxiliary `trace_discriminator_can_vary` failed at
`TraceForm.noConfusion impossible` because the pinned noConfusion interface
expected further heterogeneous equality arguments. Its attempted theorem
printed [sorryAx]. That unused helper, its comment and its two audit lines
were removed; no replacement or hole remains. All eleven delivered theorem
bodies are unchanged from the run. No second Sol check was run. The final
12,233-byte source is therefore **NOT_RECHECKED**, although all eleven
retained declarations individually elaborated and printed the complete
types/axioms in that run. The full unedited output below preserves the failure.

| Retained theorem, under YulangClosure.OriginalLiteralInputDependenceR242 | Complete axioms |
| --- | --- |
| folded_literal_build_exact | propext, Classical.choice, Quot.sound |
| build_at_fixed_decode | propext, Classical.choice, Quot.sound |
| ground_update_preserves_other_fields | none |
| ground_variation_changes_original_build | propext, Classical.choice, Quot.sound |
| ground_variation_changes_original_source_rule | propext, Classical.choice, Quot.sound |
| canonical_generator_inputs_noninterference | none |
| decoder_inputs_noninterference | propext |
| trace_update_preserves_other_fields | none |
| trace_update_preserves_literal_kernel | propext |
| diagnostic_pure_return_consumer | propext |
| diagnostic_unfinished_consumer | propext |

Reused theorem audits: return_observation_iff has [propext];
folded_generated_literal_membership has
[propext, Classical.choice, Quot.sound]. Full theorem types are in the raw
output below; the source retains all exact signatures and audit commands.
A source search of the final artifact found only `#print axioms` commands,
no retained proof holes, project axioms or checker bypasses.

Resources: one check used of one; 240-second external timeout, -j1, -M1024,
LEAN_NUM_THREADS=1. Native command returned after the first 1.001-second
yield and a later immediate completion poll; exact process elapsed and peak
RSS are UNKNOWN. Version commands are metadata checks, not proof rechecks.
No Lake build, -o output, dependency installation, cache growth command,
tests, Cargo, Astra, descendants, Git or Rust writes. Existing import cache
only. Whole assignment active duration is UNKNOWN; observed work clock
samples include 2026-11-02 02:28:03 UTC and 02:31:12 UTC, well inside the
1,800-second cap for that observed interval. No budget renewal is requested.

## Stop receipt

Only the two exact leased paths were written. No scratch files, generated
oleans, logs outside this handoff, or descendant leases were created.
Worker state at submission: **STOPPED; writes stopped after freezing this
revision**. All other paths, unknown writers and quarantined leases remain
untouched. Luna owns review, remaining targeted check, state changes and Git.
The result is pending independent review/integration, not parent closure.

## Full sole-check output, including the removed failed helper

```text
YulangClosure/OriginalLiteralInputDependenceR242.lean:164:32: error: Type mismatch
  TraceForm.noConfusion ?m.29
has type
  ?m.26 ≍ ?m.28 → TraceForm.noConfusionType ?m.24 ?m.26 ?m.28
but is expected to have type
  False
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
'YulangClosure.OriginalLiteralInputDependenceR242.folded_literal_build_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
@build_at_fixed_decode : ∀ {s : Sorts} {View : Type} (inputs : Inputs s) (readout : RuntimeReadout s View)
  (declarations : LiteralDeclaration s) (original : Kernel (Payload s View))
  (environment : Environment (Payload s View)) (state : Decoded s View),
  decode readout environment = some state →
    ∀ (context : Context) (site : Site) (literal : Literal),
      declarations literal (state.assignment.row site) →
        inputs.valueForm (state.assignment.descriptor { site := site, port := Port.finalRoot }) = ValueForm.ground →
          (Satisfies (foldedLiteralKernel inputs readout declarations original site literal) environment
              (Build context (Source.literal { site := site } literal)) ↔
            inputs.ground (state.assignment.row site))
'YulangClosure.OriginalLiteralInputDependenceR242.build_at_fixed_decode' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
@ground_update_preserves_other_fields : ∀ {s : Sorts} (inputs : Inputs s) (ground : ValueRow s → Prop),
  (have __src :=
      { compatible := inputs.compatible, eventCoherent := inputs.eventCoherent, valueForm := inputs.valueForm,
        ground := ground, fixedExternal := inputs.fixedExternal, structuralGuard := inputs.structuralGuard,
        structuralFields := inputs.structuralFields, actual := inputs.actual, functionGuards := inputs.functionGuards,
        capturedFields := inputs.capturedFields, checkedInlet := inputs.checkedInlet, actualInlet := inputs.actualInlet,
        carrierAccepted := inputs.carrierAccepted, puncturedContext := @Inputs.puncturedContext s inputs,
        otherValues := @Inputs.otherValues s inputs, registeredHoles := @Inputs.registeredHoles s inputs,
        checkedIncidences := @Inputs.checkedIncidences s inputs, receiptPrecondition := inputs.receiptPrecondition,
        actualTypedPath := inputs.actualTypedPath, actualContext := inputs.actualContext, execute := inputs.execute,
        observationGuards := inputs.observationGuards, traceForm := inputs.traceForm,
        observationFields := inputs.observationFields, checkedObservation := @Inputs.checkedObservation s inputs,
        worldGuards := inputs.worldGuards, installedCount := inputs.installedCount, installed := inputs.installed,
        alias := inputs.alias, capture := inputs.capture, captureValue := inputs.captureValue,
        sharedPosition := inputs.sharedPosition, witnessAt := inputs.witnessAt, carrierGuards := inputs.carrierGuards,
        carrierCaptures := inputs.carrierCaptures, demand := inputs.demand, force := inputs.force,
        forceIncidence := inputs.forceIncidence };
    { compatible := __src.compatible, eventCoherent := __src.eventCoherent, valueForm := __src.valueForm,
      ground := inputs.ground, fixedExternal := __src.fixedExternal, structuralGuard := __src.structuralGuard,
      structuralFields := __src.structuralFields, actual := __src.actual, functionGuards := __src.functionGuards,
      capturedFields := __src.capturedFields, checkedInlet := __src.checkedInlet, actualInlet := __src.actualInlet,
      carrierAccepted := __src.carrierAccepted, puncturedContext := @Inputs.puncturedContext s __src,
      otherValues := @Inputs.otherValues s __src, registeredHoles := @Inputs.registeredHoles s __src,
      checkedIncidences := @Inputs.checkedIncidences s __src, receiptPrecondition := __src.receiptPrecondition,
      actualTypedPath := __src.actualTypedPath, actualContext := __src.actualContext, execute := __src.execute,
      observationGuards := __src.observationGuards, traceForm := __src.traceForm,
      observationFields := __src.observationFields, checkedObservation := @Inputs.checkedObservation s __src,
      worldGuards := __src.worldGuards, installedCount := __src.installedCount, installed := __src.installed,
      alias := __src.alias, capture := __src.capture, captureValue := __src.captureValue,
      sharedPosition := __src.sharedPosition, witnessAt := __src.witnessAt, carrierGuards := __src.carrierGuards,
      carrierCaptures := __src.carrierCaptures, demand := __src.demand, force := __src.force,
      forceIncidence := __src.forceIncidence }) =
    inputs
'YulangClosure.OriginalLiteralInputDependenceR242.ground_update_preserves_other_fields' does not depend on any axioms
@ground_variation_changes_original_build : ∀ {s : Sorts} {View : Type} (inputs : Inputs s)
  (readout : RuntimeReadout s View) (declarations : LiteralDeclaration s) (original : Kernel (Payload s View))
  (environment : Environment (Payload s View)) (state : Decoded s View),
  decode readout environment = some state →
    ∀ (context : Context) (site : Site) (literal : Literal),
      declarations literal (state.assignment.row site) →
        inputs.valueForm (state.assignment.descriptor { site := site, port := Port.finalRoot }) = ValueForm.ground →
          Satisfies
              (foldedLiteralKernel
                { compatible := inputs.compatible, eventCoherent := inputs.eventCoherent, valueForm := inputs.valueForm,
                  ground := fun x => True, fixedExternal := inputs.fixedExternal,
                  structuralGuard := inputs.structuralGuard, structuralFields := inputs.structuralFields,
                  actual := inputs.actual, functionGuards := inputs.functionGuards,
                  capturedFields := inputs.capturedFields, checkedInlet := inputs.checkedInlet,
                  actualInlet := inputs.actualInlet, carrierAccepted := inputs.carrierAccepted,
                  puncturedContext := @Inputs.puncturedContext s inputs, otherValues := @Inputs.otherValues s inputs,
                  registeredHoles := @Inputs.registeredHoles s inputs,
                  checkedIncidences := @Inputs.checkedIncidences s inputs,
                  receiptPrecondition := inputs.receiptPrecondition, actualTypedPath := inputs.actualTypedPath,
                  actualContext := inputs.actualContext, execute := inputs.execute,
                  observationGuards := inputs.observationGuards, traceForm := inputs.traceForm,
                  observationFields := inputs.observationFields,
                  checkedObservation := @Inputs.checkedObservation s inputs, worldGuards := inputs.worldGuards,
                  installedCount := inputs.installedCount, installed := inputs.installed, alias := inputs.alias,
                  capture := inputs.capture, captureValue := inputs.captureValue,
                  sharedPosition := inputs.sharedPosition, witnessAt := inputs.witnessAt,
                  carrierGuards := inputs.carrierGuards, carrierCaptures := inputs.carrierCaptures,
                  demand := inputs.demand, force := inputs.force, forceIncidence := inputs.forceIncidence }
                readout declarations original site literal)
              environment (Build context (Source.literal { site := site } literal)) ∧
            ¬Satisfies
                (foldedLiteralKernel
                  { compatible := inputs.compatible, eventCoherent := inputs.eventCoherent,
                    valueForm := inputs.valueForm, ground := fun x => False, fixedExternal := inputs.fixedExternal,
                    structuralGuard := inputs.structuralGuard, structuralFields := inputs.structuralFields,
                    actual := inputs.actual, functionGuards := inputs.functionGuards,
                    capturedFields := inputs.capturedFields, checkedInlet := inputs.checkedInlet,
                    actualInlet := inputs.actualInlet, carrierAccepted := inputs.carrierAccepted,
                    puncturedContext := @Inputs.puncturedContext s inputs, otherValues := @Inputs.otherValues s inputs,
                    registeredHoles := @Inputs.registeredHoles s inputs,
                    checkedIncidences := @Inputs.checkedIncidences s inputs,
                    receiptPrecondition := inputs.receiptPrecondition, actualTypedPath := inputs.actualTypedPath,
                    actualContext := inputs.actualContext, execute := inputs.execute,
                    observationGuards := inputs.observationGuards, traceForm := inputs.traceForm,
                    observationFields := inputs.observationFields,
                    checkedObservation := @Inputs.checkedObservation s inputs, worldGuards := inputs.worldGuards,
                    installedCount := inputs.installedCount, installed := inputs.installed, alias := inputs.alias,
                    capture := inputs.capture, captureValue := inputs.captureValue,
                    sharedPosition := inputs.sharedPosition, witnessAt := inputs.witnessAt,
                    carrierGuards := inputs.carrierGuards, carrierCaptures := inputs.carrierCaptures,
                    demand := inputs.demand, force := inputs.force, forceIncidence := inputs.forceIncidence }
                  readout declarations original site literal)
                environment (Build context (Source.literal { site := site } literal))
'YulangClosure.OriginalLiteralInputDependenceR242.ground_variation_changes_original_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
@ground_variation_changes_original_source_rule : ∀ {s : Sorts} {View : Type} (inputs : Inputs s)
  (readout : RuntimeReadout s View) (declarations : LiteralDeclaration s) (original : Kernel (Payload s View))
  (environment : Environment (Payload s View)) (state : Decoded s View),
  decode readout environment = some state →
    ∀ (context : Context) (site : Site) (literal : Literal),
      declarations literal (state.assignment.row site) →
        inputs.valueForm (state.assignment.descriptor { site := site, port := Port.finalRoot }) = ValueForm.ground →
          SourceJudgment
              (foldedLiteralKernel
                { compatible := inputs.compatible, eventCoherent := inputs.eventCoherent, valueForm := inputs.valueForm,
                  ground := fun x => True, fixedExternal := inputs.fixedExternal,
                  structuralGuard := inputs.structuralGuard, structuralFields := inputs.structuralFields,
                  actual := inputs.actual, functionGuards := inputs.functionGuards,
                  capturedFields := inputs.capturedFields, checkedInlet := inputs.checkedInlet,
                  actualInlet := inputs.actualInlet, carrierAccepted := inputs.carrierAccepted,
                  puncturedContext := @Inputs.puncturedContext s inputs, otherValues := @Inputs.otherValues s inputs,
                  registeredHoles := @Inputs.registeredHoles s inputs,
                  checkedIncidences := @Inputs.checkedIncidences s inputs,
                  receiptPrecondition := inputs.receiptPrecondition, actualTypedPath := inputs.actualTypedPath,
                  actualContext := inputs.actualContext, execute := inputs.execute,
                  observationGuards := inputs.observationGuards, traceForm := inputs.traceForm,
                  observationFields := inputs.observationFields,
                  checkedObservation := @Inputs.checkedObservation s inputs, worldGuards := inputs.worldGuards,
                  installedCount := inputs.installedCount, installed := inputs.installed, alias := inputs.alias,
                  capture := inputs.capture, captureValue := inputs.captureValue,
                  sharedPosition := inputs.sharedPosition, witnessAt := inputs.witnessAt,
                  carrierGuards := inputs.carrierGuards, carrierCaptures := inputs.carrierCaptures,
                  demand := inputs.demand, force := inputs.force, forceIncidence := inputs.forceIncidence }
                readout declarations original site literal)
              environment context (Source.literal { site := site } literal) ∧
            ¬SourceJudgment
                (foldedLiteralKernel
                  { compatible := inputs.compatible, eventCoherent := inputs.eventCoherent,
                    valueForm := inputs.valueForm, ground := fun x => False, fixedExternal := inputs.fixedExternal,
                    structuralGuard := inputs.structuralGuard, structuralFields := inputs.structuralFields,
                    actual := inputs.actual, functionGuards := inputs.functionGuards,
                    capturedFields := inputs.capturedFields, checkedInlet := inputs.checkedInlet,
                    actualInlet := inputs.actualInlet, carrierAccepted := inputs.carrierAccepted,
                    puncturedContext := @Inputs.puncturedContext s inputs, otherValues := @Inputs.otherValues s inputs,
                    registeredHoles := @Inputs.registeredHoles s inputs,
                    checkedIncidences := @Inputs.checkedIncidences s inputs,
                    receiptPrecondition := inputs.receiptPrecondition, actualTypedPath := inputs.actualTypedPath,
                    actualContext := inputs.actualContext, execute := inputs.execute,
                    observationGuards := inputs.observationGuards, traceForm := inputs.traceForm,
                    observationFields := inputs.observationFields,
                    checkedObservation := @Inputs.checkedObservation s inputs, worldGuards := inputs.worldGuards,
                    installedCount := inputs.installedCount, installed := inputs.installed, alias := inputs.alias,
                    capture := inputs.capture, captureValue := inputs.captureValue,
                    sharedPosition := inputs.sharedPosition, witnessAt := inputs.witnessAt,
                    carrierGuards := inputs.carrierGuards, carrierCaptures := inputs.carrierCaptures,
                    demand := inputs.demand, force := inputs.force, forceIncidence := inputs.forceIncidence }
                  readout declarations original site literal)
                environment context (Source.literal { site := site } literal)
'YulangClosure.OriginalLiteralInputDependenceR242.ground_variation_changes_original_source_rule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
@canonical_generator_inputs_noninterference : ∀ {s : Sorts} (first second : Inputs s) (site : Site) (literal : Literal)
  (root : s.Root) (event : Event s) (scope : s.Scope) (witness : s.JointWitness),
  (fun x => CanonicalLiteralGeneratorR236.generate site literal root event scope witness) first =
    (fun x => CanonicalLiteralGeneratorR236.generate site literal root event scope witness) second
'YulangClosure.OriginalLiteralInputDependenceR242.canonical_generator_inputs_noninterference' does not depend on any axioms
@decoder_inputs_noninterference : ∀ {s : Sorts} {View : Type} (first second : Inputs s)
  (readout : RuntimeReadout s View) (environment : Environment (Payload s View)),
  (fun x => decode readout environment) first = (fun x => decode readout environment) second
'YulangClosure.OriginalLiteralInputDependenceR242.decoder_inputs_noninterference' depends on axioms: [propext]
@trace_update_preserves_other_fields : ∀ {s : Sorts} (inputs : Inputs s) (trace : TraceRow s → TraceForm s),
  (have __src :=
      { compatible := inputs.compatible, eventCoherent := inputs.eventCoherent, valueForm := inputs.valueForm,
        ground := inputs.ground, fixedExternal := inputs.fixedExternal, structuralGuard := inputs.structuralGuard,
        structuralFields := inputs.structuralFields, actual := inputs.actual, functionGuards := inputs.functionGuards,
        capturedFields := inputs.capturedFields, checkedInlet := inputs.checkedInlet, actualInlet := inputs.actualInlet,
        carrierAccepted := inputs.carrierAccepted, puncturedContext := @Inputs.puncturedContext s inputs,
        otherValues := @Inputs.otherValues s inputs, registeredHoles := @Inputs.registeredHoles s inputs,
        checkedIncidences := @Inputs.checkedIncidences s inputs, receiptPrecondition := inputs.receiptPrecondition,
        actualTypedPath := inputs.actualTypedPath, actualContext := inputs.actualContext, execute := inputs.execute,
        observationGuards := inputs.observationGuards, traceForm := trace,
        observationFields := inputs.observationFields, checkedObservation := @Inputs.checkedObservation s inputs,
        worldGuards := inputs.worldGuards, installedCount := inputs.installedCount, installed := inputs.installed,
        alias := inputs.alias, capture := inputs.capture, captureValue := inputs.captureValue,
        sharedPosition := inputs.sharedPosition, witnessAt := inputs.witnessAt, carrierGuards := inputs.carrierGuards,
        carrierCaptures := inputs.carrierCaptures, demand := inputs.demand, force := inputs.force,
        forceIncidence := inputs.forceIncidence };
    { compatible := __src.compatible, eventCoherent := __src.eventCoherent, valueForm := __src.valueForm,
      ground := __src.ground, fixedExternal := __src.fixedExternal, structuralGuard := __src.structuralGuard,
      structuralFields := __src.structuralFields, actual := __src.actual, functionGuards := __src.functionGuards,
      capturedFields := __src.capturedFields, checkedInlet := __src.checkedInlet, actualInlet := __src.actualInlet,
      carrierAccepted := __src.carrierAccepted, puncturedContext := @Inputs.puncturedContext s __src,
      otherValues := @Inputs.otherValues s __src, registeredHoles := @Inputs.registeredHoles s __src,
      checkedIncidences := @Inputs.checkedIncidences s __src, receiptPrecondition := __src.receiptPrecondition,
      actualTypedPath := __src.actualTypedPath, actualContext := __src.actualContext, execute := __src.execute,
      observationGuards := __src.observationGuards, traceForm := inputs.traceForm,
      observationFields := __src.observationFields, checkedObservation := @Inputs.checkedObservation s __src,
      worldGuards := __src.worldGuards, installedCount := __src.installedCount, installed := __src.installed,
      alias := __src.alias, capture := __src.capture, captureValue := __src.captureValue,
      sharedPosition := __src.sharedPosition, witnessAt := __src.witnessAt, carrierGuards := __src.carrierGuards,
      carrierCaptures := __src.carrierCaptures, demand := __src.demand, force := __src.force,
      forceIncidence := __src.forceIncidence }) =
    inputs
'YulangClosure.OriginalLiteralInputDependenceR242.trace_update_preserves_other_fields' does not depend on any axioms
@trace_update_preserves_literal_kernel : ∀ {s : Sorts} {View : Type} (inputs : Inputs s)
  (trace : TraceRow s → TraceForm s) (readout : RuntimeReadout s View) (declarations : LiteralDeclaration s)
  (original : Kernel (Payload s View)) (site : Site) (literal : Literal),
  foldedLiteralKernel
      { compatible := inputs.compatible, eventCoherent := inputs.eventCoherent, valueForm := inputs.valueForm,
        ground := inputs.ground, fixedExternal := inputs.fixedExternal, structuralGuard := inputs.structuralGuard,
        structuralFields := inputs.structuralFields, actual := inputs.actual, functionGuards := inputs.functionGuards,
        capturedFields := inputs.capturedFields, checkedInlet := inputs.checkedInlet, actualInlet := inputs.actualInlet,
        carrierAccepted := inputs.carrierAccepted, puncturedContext := @Inputs.puncturedContext s inputs,
        otherValues := @Inputs.otherValues s inputs, registeredHoles := @Inputs.registeredHoles s inputs,
        checkedIncidences := @Inputs.checkedIncidences s inputs, receiptPrecondition := inputs.receiptPrecondition,
        actualTypedPath := inputs.actualTypedPath, actualContext := inputs.actualContext, execute := inputs.execute,
        observationGuards := inputs.observationGuards, traceForm := trace,
        observationFields := inputs.observationFields, checkedObservation := @Inputs.checkedObservation s inputs,
        worldGuards := inputs.worldGuards, installedCount := inputs.installedCount, installed := inputs.installed,
        alias := inputs.alias, capture := inputs.capture, captureValue := inputs.captureValue,
        sharedPosition := inputs.sharedPosition, witnessAt := inputs.witnessAt, carrierGuards := inputs.carrierGuards,
        carrierCaptures := inputs.carrierCaptures, demand := inputs.demand, force := inputs.force,
        forceIncidence := inputs.forceIncidence }
      readout declarations original site literal =
    foldedLiteralKernel inputs readout declarations original site literal
'YulangClosure.OriginalLiteralInputDependenceR242.trace_update_preserves_literal_kernel' depends on axioms: [propext]
@trace_discriminator_can_vary : ∀ {s : Sorts} (inputs : Inputs s) (returned : TraceRow s) (value : ValueRow s),
  { compatible := inputs.compatible, eventCoherent := inputs.eventCoherent, valueForm := inputs.valueForm,
            ground := inputs.ground, fixedExternal := inputs.fixedExternal, structuralGuard := inputs.structuralGuard,
            structuralFields := inputs.structuralFields, actual := inputs.actual,
            functionGuards := inputs.functionGuards, capturedFields := inputs.capturedFields,
            checkedInlet := inputs.checkedInlet, actualInlet := inputs.actualInlet,
            carrierAccepted := inputs.carrierAccepted, puncturedContext := @Inputs.puncturedContext s inputs,
            otherValues := @Inputs.otherValues s inputs, registeredHoles := @Inputs.registeredHoles s inputs,
            checkedIncidences := @Inputs.checkedIncidences s inputs, receiptPrecondition := inputs.receiptPrecondition,
            actualTypedPath := inputs.actualTypedPath, actualContext := inputs.actualContext, execute := inputs.execute,
            observationGuards := inputs.observationGuards, traceForm := fun x => TraceForm.pureReturn value,
            observationFields := inputs.observationFields, checkedObservation := @Inputs.checkedObservation s inputs,
            worldGuards := inputs.worldGuards, installedCount := inputs.installedCount, installed := inputs.installed,
            alias := inputs.alias, capture := inputs.capture, captureValue := inputs.captureValue,
            sharedPosition := inputs.sharedPosition, witnessAt := inputs.witnessAt,
            carrierGuards := inputs.carrierGuards, carrierCaptures := inputs.carrierCaptures, demand := inputs.demand,
            force := inputs.force, forceIncidence := inputs.forceIncidence }.traceForm
        returned =
      TraceForm.pureReturn value ∧
    { compatible := inputs.compatible, eventCoherent := inputs.eventCoherent, valueForm := inputs.valueForm,
            ground := inputs.ground, fixedExternal := inputs.fixedExternal, structuralGuard := inputs.structuralGuard,
            structuralFields := inputs.structuralFields, actual := inputs.actual,
            functionGuards := inputs.functionGuards, capturedFields := inputs.capturedFields,
            checkedInlet := inputs.checkedInlet, actualInlet := inputs.actualInlet,
            carrierAccepted := inputs.carrierAccepted, puncturedContext := @Inputs.puncturedContext s inputs,
            otherValues := @Inputs.otherValues s inputs, registeredHoles := @Inputs.registeredHoles s inputs,
            checkedIncidences := @Inputs.checkedIncidences s inputs, receiptPrecondition := inputs.receiptPrecondition,
            actualTypedPath := inputs.actualTypedPath, actualContext := inputs.actualContext, execute := inputs.execute,
            observationGuards := inputs.observationGuards, traceForm := fun x => TraceForm.unfinished,
            observationFields := inputs.observationFields, checkedObservation := @Inputs.checkedObservation s inputs,
            worldGuards := inputs.worldGuards, installedCount := inputs.installedCount, installed := inputs.installed,
            alias := inputs.alias, capture := inputs.capture, captureValue := inputs.captureValue,
            sharedPosition := inputs.sharedPosition, witnessAt := inputs.witnessAt,
            carrierGuards := inputs.carrierGuards, carrierCaptures := inputs.carrierCaptures, demand := inputs.demand,
            force := inputs.force, forceIncidence := inputs.forceIncidence }.traceForm
        returned ≠
      TraceForm.pureReturn value
'YulangClosure.OriginalLiteralInputDependenceR242.trace_discriminator_can_vary' depends on axioms: [sorryAx]
@diagnostic_pure_return_consumer : ∀ {s : Sorts} (inputs : Inputs s) (returned : TraceRow s) (value : ValueRow s),
  have varied :=
    { compatible := inputs.compatible, eventCoherent := inputs.eventCoherent, valueForm := inputs.valueForm,
      ground := inputs.ground, fixedExternal := inputs.fixedExternal, structuralGuard := inputs.structuralGuard,
      structuralFields := inputs.structuralFields, actual := inputs.actual, functionGuards := inputs.functionGuards,
      capturedFields := inputs.capturedFields, checkedInlet := inputs.checkedInlet, actualInlet := inputs.actualInlet,
      carrierAccepted := inputs.carrierAccepted, puncturedContext := @Inputs.puncturedContext s inputs,
      otherValues := @Inputs.otherValues s inputs, registeredHoles := @Inputs.registeredHoles s inputs,
      checkedIncidences := @Inputs.checkedIncidences s inputs, receiptPrecondition := inputs.receiptPrecondition,
      actualTypedPath := inputs.actualTypedPath, actualContext := inputs.actualContext, execute := inputs.execute,
      observationGuards := inputs.observationGuards, traceForm := fun x => TraceForm.pureReturn value,
      observationFields := inputs.observationFields, checkedObservation := @Inputs.checkedObservation s inputs,
      worldGuards := inputs.worldGuards, installedCount := inputs.installedCount, installed := inputs.installed,
      alias := inputs.alias, capture := inputs.capture, captureValue := inputs.captureValue,
      sharedPosition := inputs.sharedPosition, witnessAt := inputs.witnessAt, carrierGuards := inputs.carrierGuards,
      carrierCaptures := inputs.carrierCaptures, demand := inputs.demand, force := inputs.force,
      forceIncidence := inputs.forceIncidence };
  Meaning varied (Query.trace returned) ↔
    varied.eventCoherent returned.event ∧
      (varied.observationGuards returned).Valid ∧
        Meaning varied (Query.world returned.event) ∧
          (value.event = returned.event ∧ Meaning varied (Query.value value)) ∧
            (varied.observationFields returned).Holds (Meaning varied)
'YulangClosure.OriginalLiteralInputDependenceR242.diagnostic_pure_return_consumer' depends on axioms: [propext]
@diagnostic_unfinished_consumer : ∀ {s : Sorts} (inputs : Inputs s) (returned : TraceRow s),
  have varied :=
    { compatible := inputs.compatible, eventCoherent := inputs.eventCoherent, valueForm := inputs.valueForm,
      ground := inputs.ground, fixedExternal := inputs.fixedExternal, structuralGuard := inputs.structuralGuard,
      structuralFields := inputs.structuralFields, actual := inputs.actual, functionGuards := inputs.functionGuards,
      capturedFields := inputs.capturedFields, checkedInlet := inputs.checkedInlet, actualInlet := inputs.actualInlet,
      carrierAccepted := inputs.carrierAccepted, puncturedContext := @Inputs.puncturedContext s inputs,
      otherValues := @Inputs.otherValues s inputs, registeredHoles := @Inputs.registeredHoles s inputs,
      checkedIncidences := @Inputs.checkedIncidences s inputs, receiptPrecondition := inputs.receiptPrecondition,
      actualTypedPath := inputs.actualTypedPath, actualContext := inputs.actualContext, execute := inputs.execute,
      observationGuards := inputs.observationGuards, traceForm := fun x => TraceForm.unfinished,
      observationFields := inputs.observationFields, checkedObservation := @Inputs.checkedObservation s inputs,
      worldGuards := inputs.worldGuards, installedCount := inputs.installedCount, installed := inputs.installed,
      alias := inputs.alias, capture := inputs.capture, captureValue := inputs.captureValue,
      sharedPosition := inputs.sharedPosition, witnessAt := inputs.witnessAt, carrierGuards := inputs.carrierGuards,
      carrierCaptures := inputs.carrierCaptures, demand := inputs.demand, force := inputs.force,
      forceIncidence := inputs.forceIncidence };
  Meaning varied (Query.trace returned) ↔
    varied.eventCoherent returned.event ∧
      (varied.observationGuards returned).Valid ∧
        Meaning varied (Query.world returned.event) ∧ (varied.observationFields returned).Holds (Meaning varied)
'YulangClosure.OriginalLiteralInputDependenceR242.diagnostic_unfinished_consumer' depends on axioms: [propext]
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

