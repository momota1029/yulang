# R173 proof handoff, revision 1

Outcome: **BLOCKED_ORIGINAL_INTERPRETATION**. Outcome class:
`source-native-evidence`, with an exact missing semantic input. No new theorem
or Lean module is delivered; original inference soundness remains OPEN.

## Assignment and authority

- Sprint: `LAMBDA-INFERENCE-GENERATION-ADEQUACY/20261102-R173`, contract revision 1,
  SHA-256 `00ea0e1db6fb88659d4b4e1f8b55d6fc5cd1e7c2f315cfb51d738c989f228b4c`.
- Assignment: `R173-PROOF`; primary-supplied baseline `yulang3/a80f58d4f`.
- Worker: `/root/lambda_inference_generation_adequacy_r173_proof`, actual
  current-session task received from `/root`; active-work/hash acknowledgement
  sent before any write. Requested role/model: registered `lean_prover`;
  requested effort and effective observed model/effort: UNKNOWN in available
  metadata. Sole author; no descendants.
- Exact leases: this handoff and, only upon a constructive result,
  `notes/theory/lean/YulangClosure/LambdaInferenceGenerationAdequacyR173.lean`.
  The latter was not created. No other output or scratch path was written.
- Applied `yulang-lean-proofs` and its `sources.md` / `execution.md`; read root
  AGENTS/base map, sprint rules, handoff protocol and current snapshot.

Source authority is the Authoritative Source Generalize definition §§2–3,
selecting construction §§3–5, including the independent local premises L1–L5
in construction §2 and Parameter/Lambda rules in §3.1. The Authoritative
annotation-effect policy §§1–1.1 keeps contravariant concrete permission
distinct from input-row closure. Top-level inference principles §1 govern
generation/propagation; type inference does not require executing source code.

## Unchanged original claim and actual meanings

`YulangClosure.SourceProblem.InferenceSoundness`, `Contracts.lean:127–130`:

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

`SourceProblem` (`Contracts.lean:103–117`) declares `generates`, `solves`,
`sourceJudgment` and `sameScoped` as independent fields. These fields have no
constructor equations in that definition. `InferenceConstruction.lean:52–56`
and `OriginalProofProgress.lean:71–76` explicitly leave the original concrete
SourceProblem instance, original interpretation and same-scoped witness open.
The targeted search for concrete field assignments in `YulangClosure/*.lean`
found an abstract countermodel in `OriginalPrincipalityResolution.lean`, not
an instance identifying Yulang's generated Rust constraints and solutions.
Therefore there is no defined actual Yulang `p.generates` or `p.solves` here
to unfold for the requested implication. This is a missing interpretation,
not evidence that the approved inference algorithm is unsound.

The independent candidate meanings are precise:

- `OriginalSource.Build C S = compile (sourceRules C S)`
  (`OriginalSourceGeneration.lean:870`).
- `OriginalSource.Satisfies K E` (`:842–866`) interprets local atoms using
  `K.atom`, finite checking using `Checking`, existential and universal
  binders using `K.admitted`, and Shared using the same environment anchor.
- `OriginalSource.SourceJudgment K E C S = Judgment K E (sourceRules C S)`
  (`:801–804`). These finite judgments have independently supplied local
  meanings; generated syntax alone does not instantiate those meanings.
- `generated_constraints_imply_source_judgment` (`:1026–1032`) consumes the
  entire `Satisfies K E (Build C S)`, not the parent fields. Its result has
  no parent `sameScoped` conjunct.

## First unavailable registration and exact required equation

For the unannotated outer Lambda shell, the first binder is the formal
description, above invocation. Existing code already constructs a local
description producer; it must not be reported missing or reproved:

```lean
OriginalParameterWorld.FormalAssignment s View =
  (parameter : Parameter) → Route →
    ScopeValues s View parameter.typeScope → Contract s parameter.formal.entry

Contract s .value = s.Descriptor
Contract s .computation = s.Interface
```

Owning definitions are `OriginalParameterWorld.lean:53–69` and
`OriginalFormalAdmission.Introduction.description` (`OriginalFormalAdmission.lean:50–53`).
`Introduction.description intro assignment state` installs the single
`assignment parameter route prior` contract at
`⟨parameter.formal.site, .descriptor⟩`. `localAdmissions` (`:122–132`)
recognizes exactly that produced payload for the description binder.
`produced_description_admitted` (`:154–162`) proves its admission **given that
assignment and decoded state**. It neither obtains them from a Rust solution
nor validates every untouched original source atom.

The first unavailable independent registration is the original semantic
readback of a generated, prepared formal's native endpoints, under solution
`a`, as this pre-invocation `FormalAssignment`. No such registration function
or equation is defined in the pinned construction. The required equations,
stated as requirements rather than Lean declarations or new definitions, are:

```text
FA_a(parameter, route, prior) : Contract sorts parameter.formal.entry

Value entry:
  FA_a(parameter, route, prior)
    = originalValueDescriptor_a(prepared.native_root, originalTypeScope(prior))

Computation entry:
  FA_a(parameter, route, prior)
    = originalCompleteInterface_a(prepared.native_root, prepared.entry_effect,
                                  originalTypeScope(prior))

description payload
  = declaration decodedState parameter (FA_a(parameter, route, prior))
```

`originalValueDescriptor_a`, `originalCompleteInterface_a`, `FA_a` and their
source/scope registration are the **missing inputs**, not existing constants
and not aliases for solver success, `Build` or `Satisfies`. In particular,
the complete interface cannot be replaced by the effect endpoint alone.
The RHS must follow the actual generated native root/port and original
annotation/capture/interface interpretation. It must be justified for the
same parent `a`, declaration, occurrence route and prior telescope. Its
function arguments cannot include the later invocation, body result or a
desired source derivation. Choosing an arbitrary `FormalAssignment`, then
defining its admission to hold, does not discharge this registration.

The earlier source-encoding part of this registration must also identify
the same Lambda/formal/pattern/body/annotation and satisfy

```text
encodedFormal.outerComputation
  = originalWrittenFormalAnnotation.ty.effects.is_some()
encodedFormal.entry = Value or Computation according to that same equation
```

The real collector decides this from the outer written annotation. A solved
latent Function/Comp shape cannot supply it. For an outer expression
annotation, the additional `finalAnnotationFormation` atom and actual
annotation boundary wrap the description binder; their independent original
meaning must be supplied too. They are not discharged by peeling the shell.

**Owner:** Luna's original inference interpretation/semantic-registration
packet. The owning formal Lean interface is `FormalAssignment`; the native
field producer is `initialize_candidate_source_levels`; the root parent
fields remain owned by `SourceProblem`'s still-uninstantiated concrete instance.
This packet stops at this missing independent input as required by R173.

## Actual Lambda generation and why its equations are insufficient alone

Static source reads at the pinned hashes establish these construction facts:

1. `candidate_source.rs:1103–1118` registers the same Lambda index,
   parameter/recipe, original outer-annotation role and scope, initially
   `native_root = None`, `entry_effect = None`.
2. Session construction (`lib.rs:10424–10468`) allocates parameter value
   variables, then calls preparation. `initialize_candidate_source_levels`
   (`candidate_source.rs:2303–2325`) checks the actual recipe identity,
   obtains its positive parameter root, allocates an effect port only for
   Computation entry, and writes those two fields.
3. `FormalEntry`/`FormalAnnotation` dispatch (`candidate_source.rs:2472–2479`)
   uses the retained original annotation and registration. Formal Name effects
   are equated to that registration's entry port. This packet does not read
   or revalidate the effect-annotation helper implementation beyond the
   R172 frozen evidence; no propagation law follows just from dispatch.
4. `admit_lambda_fact` (`lib.rs:11622–11842`) uses the actual parameter domain
   (possibly a retained `formal_domains` domain), body value endpoint, body
   effect endpoint, distinct argument-effect and return-effect ports. In the
   candidate graph branch its emitted local equations are:

```text
slot 3:  entryEffect+ <= returnEffect-       [Value entry only]
slot 4:  bodyEffect+  <= returnEffect-       [both entry modes]
default slots: defaultEffect_i+ <= returnEffect-
slot 2:  Function+(domain-, entryEffect-, returnEffect+, bodyResult+) <= root-
```

Computation entry reuses `registration.entry_effect`; Value entry allocates
an entry effect and includes slot 3 even when the argument is unused. The
Function constructor retains separate body result and return-effect ports.
The branch without the candidate graph uses `(empty, body_effect)` instead;
this is a source comparison, not an equivalence claim for that branch.

These are actual constraint construction equations. A scalar solution of
these edges alone does not identify the source description/captures, original
admission, receipt, Shared permission, annotation boundary or complete body
consumer. Those meanings cannot be declared true merely because the edge
solver accepts. This packet establishes no reachable compiler defect.

The remaining derivation order is exactly the original one:
description → view → closure/capture atoms → every independently admitted
invocation → receipt → entry premises → (Value Return/rebind, if applicable)
→ Shared → pattern → EventProof/body consumer → body.
`OriginalSourceGeneration.sourceRules` (`:132–168`),
`OriginalFormalShared.lambdaTree` and `entryPremises` compute this order.
`closureKernel` preserves the original `atom` meanings; local description
admission does not prove `captureWholeEnvironment`, `closureFormation`,
`sourceFormalRole`, annotation formation or entry/effect laws. Genuine
subsource induction hypotheses can prove the pattern/body child rules at
their actual scopes. They cannot prove the containing Lambda's own atoms,
admissions, whole body-consumer checking or Shared license.

## Parent application and next discriminating input

No new implication applies to the parent yet. The printed reconstruction
theorem is reusable after, and only after, actual generation/solution
interpretation proves its independent satisfaction premise. It then yields
the independent source judgment, still requiring the same original witness
`e` for `sameScoped s x e a`. Scope, rigid imports, hidden witness, all uses
and futures stay jointly attached to that one `e`; endpoint equality or one
witness per challenge cannot substitute for it.

Stable request `R173-ORIGINAL-FORMAL-READBACK-1`: provide the registered
solution-to-original description/interface interpretation above, including
the original annotation identity and source occurrence/scope encoding, with
its actual constructor equation and sound local law. Inputs: frozen R173
source trace, Source Generalize §3, `FormalAssignment`, and the concrete
chosen generated-constraint/solution representation. Output must be an
independently justified registration and proof, not another assumed bridge.
Falsifier: an actual successful generated solution whose registered formal
cannot satisfy that original description/interface or whose reading depends
on a later invocation. None was demonstrated here. All later Lambda and
non-Lambda obligations, R171 origin/preparation application and the shared
witness bridge remain OPEN. No source constructor was removed.

## Frozen inputs and checks

All eight contract input hashes match. Canonical Rust paths are
`crates/yu-solver/src/lib.rs` and `crates/yu-solver/src/candidate_source.rs`.
An initial hash command used an incorrect `tools/inference-playground/src`
prefix: it exited 1 (missing candidate_source; unrelated lib had another
hash). The corrected canonical-path command exited 0 and matched both pins;
the unrelated lib contents were never read.

| Input | SHA-256 |
| --- | --- |
| `Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `InferenceConstruction.lean` | `576d69266da62c0f75fa9748ff0f0691a9f0bc3aca5148be9d25cef82d2010f0` |
| `OriginalProofProgress.lean` | `21e361962538d5e2738041b58186682a4a9fb3ad10c75f4c39dc97e32a443f39` |
| solver `lib.rs` | `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be` |
| solver `candidate_source.rs` | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` |
| R172 theory note | `3558480ed78086ad7471b96a6e41aa88db3b7b8a6d8b54e092fae7b6dce26ef9` |
| R172 proof handoff | `388b20cfa8698c5e6a71b31661fbbc428a72bb2c1c720562a225da439ec7b37c` |
| R172 source handoff | `568a16bc3ca177e57ba0915c4b9dc96cf6c9aa6c364df0c31d57e61333e20a9e` |
| `OriginalParameterWorld.lean` | `7b5f849f744dbe56f374d8be6b11a5a218176abf6eeda2fb9da8180c7b1ff802` |
| `OriginalFormalAdmission.lean` | `77230ab7984ee544db16fe4d9663b73f98b9afa9c5d2610fad59c26753d5ac7c` |
| `OriginalSourceEnvironment.lean` | `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132` |

Other directly consulted source-meaning and authority hashes match the R172
manifest: Syntax, Generation, FormalShared, SourceClosure, SourceChecking,
Source Generalize design/construction and annotation policy. No frozen input
was edited. Combined tool displays that truncated were followed by bounded
reads of the relevant definitions.

Pinned project configuration read: Lean 4.35.0, no external packages,
`-j1 -M1024`. `elan which lake` exited 0, resolving
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`.
Native `lake --version` exited 0: `Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)`.
`lake --no-cache env lean --version` exited 0: Lean 4.35.0,
commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Release.

Exactly one of the two permitted proof checks ran, through stdin with the
resolved native Lake, in `notes/theory/lean`:

```text
lake --no-cache env lean -j1 -M1024 --stdin
import YulangClosure.Contracts
import YulangClosure.OriginalFormalAdmission
#print YulangClosure.SourceProblem.InferenceSoundness
#check @YulangClosure.OriginalSource.generated_constraints_imply_source_judgment
#print axioms YulangClosure.OriginalSource.generated_constraints_imply_source_judgment
#print YulangClosure.OriginalParameterWorld.FormalAssignment
#print YulangClosure.OriginalFormalAdmission.localAdmissions
#check @YulangClosure.OriginalFormalAdmission.produced_description_admitted
#print axioms YulangClosure.OriginalFormalAdmission.produced_description_admitted
```

Exit 0, reported command wall time 0.401 seconds. Printed reconstruction type:

```lean
∀ {Value : Type} (kernel : OriginalSource.Kernel Value)
  (environment : OriginalSource.Environment Value) (context : OriginalSource.Context)
  {category : OriginalSource.Category} (source : OriginalSource.Source category),
  OriginalSource.Satisfies kernel environment (OriginalSource.Build context source) →
    OriginalSource.SourceJudgment kernel environment context source
```

Its complete axiom list is `[propext, Classical.choice, Quot.sound]`.
The second audited existing theorem has this exact parameter/conclusion shape
(names opened solely for readable transcription):

```lean
∀ {s : Sorts} {View : Type} (intro : Introduction s View)
  (assignment : FormalAssignment s View) (inputs : Inputs s)
  (readout : RuntimeReadout s View) (base : LocalAdmissions s View)
  (environment : Environment (Payload s View)) (state : Decoded s View),
  decode readout environment = some state → ∀ occurrence : Nat,
    Admitted inputs readout (localAdmissions intro assignment base) environment
      (descriptionBinder intro.parameter)
      (scopeCandidate environment occurrence
        (.logical .description (intro.description assignment state)))
```

Its complete axiom list is `[propext, Quot.sound]`. These are existing
conditional theorem audits from existing dependencies, not checks of a new
registration, fresh builds of their dependency cone or closure of the parent.
No theorem was delivered requiring a new axiom audit. The build/helper was
not run because the decisive semantic inputs are absent and the packet
forbids build/cache growth. No artificial failing proof was constructed.

Budget: 900 seconds; stopping at the semantic-input boundary within that
bound. Exact whole-worker duration/RSS are UNKNOWN. Cache census before and
after the stdin check: 424 files / 100,516,779 bytes in each census. This checks
file count/total size, not a bytewise cache digest. The contract and all eight
contract input hashes matched again after the check. No build, Cargo, tests, installation,
new environment, dependencies, cache/output generation, compiler changes,
runtime-subtree reads, Git, shared-record edits or descendants. Only the
leased Markdown handoff was written. Review is pending fresh independent
assignment by Luna; producer inspection is not certification.

**STOP: all writes stopped after final handoff hash. No unresolved descendant
lease. Return to Luna for original-registration ownership and integration.**
