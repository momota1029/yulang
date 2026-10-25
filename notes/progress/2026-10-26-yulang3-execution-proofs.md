# Yulang3 explicit-execution proof progress — 2026-10-26

## Scope and provenance

The current user request authorizes proof development and push on `yulang3`.
Construction began at `de9d8e5164647bc777101f07a392992c98d4bb87` in an isolated
checkout. Incoming R56–R58 records and the separately reviewed singleton-beta
integration at `4eb348f7ebf53509ae701c6b0434041a90f8f573` were retained.
The first checkpoint was pushed as
`22655e3ce735a2c41fa8cb41ff3eb281623d8f24`. Later R59 scheduling records through
`77b7942be` were fast-forwarded without changing any Lean dependency.
These modules are fresh constructions, not recovered R55 candidate bytes;
historical failed audits and withdrawn questions retain their status.

Source: `docs/yulang-operational-type-safety-ja.tex`, with its opening
corrections and `notes/theory/2026-10-24-corrected-core-value-continuation.md`.
The results below concern the represented explicit executor. Full language
progress, effects/lifetimes, source/native correspondence and original
Simple-sub A/B obligations remain OPEN.

## Accepted results

### Type application

`PaperTypeApplicationPreservation.lean` proves cancellation after inserting an
arbitrary block of type binders and instantiating it with the actual arguments.
It covers all existing raw syntax families, metadata and the complete
declaration table, including nested binders and formal-binder template bodies.

`instantiate_body` consumes `PaperValueTyped.subst_explicit` and restores the
identical declaration, graph and lexical environments. `typeBetaValue_preservation`
and `typeBetaForce_preservation` prove the actual beta redex; `force_typeBeta_delay`
also proves the distinct subsequent Force/Delay endpoint. Continuation response
and result types are independent. No closed-context restriction or assumed
preservation law is introduced.

Source SHA-256: `60e095545530bc784487a4bfcc1c7acfc1160b3adf8c1c8dc03ab98806154556`.

### Registered templates

`PaperTemplateExecution.lean` implements a finite Nat-key lookup and one body
expansion, checking both type and value arities. The unchanged unique complete
entry resolver identifies the actual selected code body.

`BodyTyped` checks the registered body once in the reversed formal environment;
`BodiesTyped` requires this for every table member. These are independent
syntax-directed derivations, not assumptions of execution safety. All captured
term/graph values are explicit arguments, as the manuscript requires.
`BodyTyped.instantiate` consumes cancellation; `BodyTyped.expand` then performs
graph weakening and simultaneous term substitution. `template_applicable` and
`template_preservation` apply these lemmas to the existing invocation judgment
with arbitrary caller graph and lexical environments. A two-type/two-value
example distinguishes formal order and checks the actual expansion.

Source SHA-256: `3ead9cf7d0f57d02d5fd8b44da24f133d7859e76dff8ee1d1b17cb233920d792`.

### Repeated response/resume and failure

`PaperCombinedExecution.lean` retains every successful existing core/let,
tuple-split, perform and request-bind transition and adds empty-owner raw
resume plus failure unwinding. The exact failure reason is preserved.
`finite_prefix` applies to actual successful `controlStep` equations;
`finite_interaction` also admits arbitrary interleavings of external responses.
Its separate protocol checks only each foreign response at the actual request
instance's response type, never assuming an internal preservation law.

`shared_continuation_prefixes` reuses the same immutable saved continuation.
`example_arbitrarily_many_rounds` constructs actual perform, request-bind,
response, resume and split transitions for every natural number `n`, proving
exactly `n` responses and `n` resumes. It then applies the general preservation
theorem to that family. Nonempty-owner cases remain explicitly unsupported;
`none` is not identified with a safe terminal result.

Source SHA-256: `58661ddec13e1fe4abb6a9b6627597fa824dedbf36f952e56dc15906141314d1`.

### Connected concrete execution

`PaperExtendedExecution.lean` connects all three results to one deterministic
executor. It preserves every successful Combined transition and its priority;
the fallback performs a direct type-beta step, then actual template lookup and
expansion. The executor does not contain typing evidence.

`preservation` takes exactly the independent `BodiesTyped d` obligation, initial
`StateTyped d g e state result`, and the actual successful `controlStep`
equation. It preserves the identical declarations, graph environment, lexical
environment and final result type. `erasure`, `finite_prefix` and
`finite_interaction` extend this to the corresponding concrete transitions and
arbitrary finite interactions. The foreign-response protocol checks the actual
operation instance's response type. No internal preservation law is assumed.
Embedding previous Combined traces does not require `BodiesTyped`.

Direct administrative beta is supported in Ret, Force, Split, Field, Lookup,
Unroll, UnionCase and the Resume continuation operand. This is not recursive
value normalization. The existing return/pop priority and the explicit
nonempty-owner rejection boundary remain intact.

The mixed example proves its table bodies independently and constructs all
three actual transitions:

```text
template 42 [Int, Bool] [7, true]
  → Force ((Λ. Delay (Ret true)) [Int])
  → Force (Delay (Ret true))
  → Ret true
```

Source SHA-256: `a29c5cc15748e8a91338f2a068e94ff7dc58c2a19adad564ba3f5a6fea337ea7`.

### Structural elimination and its complete transport cases

The explicit paper judgment now contains the manuscript's intersection
projections and Bottom elimination. `choose value false` selects the left type;
`choose value true` selects the right. Both select a derivation of the same raw
value, following the existing polarity in `CoreSyntax.lean`.

All five explicit mutual typing recursors carry the three new cases: type
substitution, graph weakening, term renaming, term replacement and supported
syntax. Raw rename/replace/support now traverse choose and absurd operands,
extending cases that were previously unsupported. The existing binder lifting
mechanisms are unchanged. Prior substitution results are preserved when both
the source and replacement values were already supported, in particular for
prior typed substitutions. An arbitrary untyped replacement containing a
formerly unsupported choose/absurd may intentionally produce a different raw
result: its operand is now correctly renamed beneath a binder. The old partial
API checked support of the substituted source, not of every replacement.

`PaperCoreStep.step` actually reduces `choose (.both value) side` to `ret value`.
`choose_applicable`, the existing all-successor preservation theorem, and
`PaperCoreControl.controlStep_evidence` establish its selected interface and
ordinary control behavior. `absurd_no_step` explicitly records that the partial
principal operator supplies no reduction for absurd; this is not a proof that
closed Bottom values cannot exist.

`PaperEliminationExamples.lean` supplies 11 authored examples: a single lambda
with distinct callable interfaces, negative polarity checks, identical runtime
payloads, capture avoidance under term/response/type binders, an explicit open
Bottom assumption, actual Combined execution and preservation, and composition
of type beta with Force/Delay and choose.

| Changed/new source | SHA-256 |
| --- | --- |
| `PaperExecutionSyntax.lean` | `78f23b9e946b0259cdb63797ed226706112f71375a013e0b9cc8745ad5afe8b0` |
| `PaperExecutionTypingSubstitution.lean` | `fae64aa9a5c37572a3f654c403b7fb8ff7eb7adccaa4e3540fff85e61ce84819` |
| `PaperExecutionGraphWeakening.lean` | `313a550a550716e235e73690d238f1040838aeebd2cc0cf0b7753979ab6fe38d` |
| `PaperTermSubstitution.lean` | `42d7f46d992e715443a7116066b51ae1748849718f6c4e716d9169ea069059d9` |
| `PaperCoreStep.lean` | `6357b14217e82421eed87da981cef8e94014dcaea634d746ad0b4bb39bff6144` |
| `PaperCoreControl.lean` | `71594dfb24af402f7b4835dc54b5383a46106faba959b687295cc0431361530e` |
| `PaperEliminationExamples.lean` | `d7b412df9bf7cfe47c538b48e1fb6ebfd8fc6c177d484cc3912573608d53071d` |

## Verification and review

Official Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`,
Lake `5.0.0-src+eb6cafb`; release archive SHA-256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
Pins/manifests were unchanged. Each native call used one Lean thread,
`-j1 -M1024` and a 120-second process-group timeout; no timeout occurred.

Targeted producer builds and audits passed before integration: 36 authored
type-application theorems, 12 template theorems, 37 Combined theorems and 33
Extended theorems. The structural packet audited all 143 authored theorems in
its seven files plus 15 dependent endpoints and three new typing constructors.
There are 131 newly authored theorems across this task; audit totals below also
include old foundation theorems and generated declarations.

The final default-root `lake build` passed all 49 jobs in 99.949398 seconds,
including the historical singleton-beta module, all four new execution modules,
and the new elimination examples. `YulangClosure.lean` imports the connected
executor and examples, so a default build checks them.

The committed `AuditExecutionProofs.lean` enumerates actual originating modules,
requires theorem declarations and 26 named public endpoints, rejects project
axiom declarations, and prints every actual type and complete transitive axiom
list, including private/generated helpers. It separately checks the three new
typing constructors as constructors. The final audit passed in 6.976777 seconds.
The unmodified repository `validate_audit` accepted all 1,368 unique ordered
begin/type/axiom/end blocks, including 348 private declarations.

| Audited module | All theorem constants |
| --- | ---: |
| `PaperExecutionSyntax` | 474 |
| `PaperExecutionTypingSubstitution` | 57 |
| `PaperExecutionGraphWeakening` | 16 |
| `PaperTermSubstitution` | 399 |
| `PaperCoreStep` | 70 |
| `PaperCoreControl` | 14 |
| `PaperTypeApplicationPreservation` | 140 |
| `PaperTemplateExecution` | 28 |
| `PaperCombinedExecution` | 87 |
| `PaperExtendedExecution` | 71 |
| `PaperEliminationExamples` | 12 |
| **Total** | **1,368** |

Complete axiom groups: 704 use `[propext, Quot.sound]`, 280 use `[propext]`, and
384 use none. The three new typing constructors use none. No audited theorem
uses `Classical.choice`, `sorryAx`, a custom axiom, a native-evaluation trust
assumption, or a checker bypass. These counts are not a claim to have audited
every unrelated historical module in the repository.

Fresh independent reviewer `/root/proof_review`, who authored no proof and made
no checker call, reviewed the four frozen execution modules, the seven-file
foundation/example delta, actual theorem types and complete axiom reports,
source correspondence, dependent premises, and the persistent audit harness.
All code scopes were CLEAN with no blocking/major finding. The reviewer also
accepted the final integrated dependency build and all 1,368 complete audit
blocks, checked frozen source/dependency hashes and diagnostic locations, and
returned CLEAN. A documentation overstatement about arbitrary untyped raw
replacement compatibility was narrowed to the supported/typed scope above;
no proof-source repair was required by review.

The final build reports 668 existing lint/deprecation warnings: 23 in
`PaperExecutionSyntax`, 235 in `PaperExecutionBinderLaws`, 3 in
`ControlComposition`, 96 in `PaperTermSubstitution`, 4 in `PaperCoreStep`, 276
in the historical `PaperTypeBetaExecution`, 22 in `PaperTupleSplitExecution`,
2 in `PaperPerformLetExecution`, and 7 in `NativeIntegerComparison`.
Every diagnostic location was mapped to an unchanged source line. New modules,
new clauses and the audit have zero warnings. Shared simultaneous-induction
tactic cleanup remains separate work; no linter was disabled or warning hidden.

Reproduce from `notes/theory/lean`:

```sh
lake build
lake env lean -j1 -M1024 AuditExecutionProofs.lean
```

Final audit source SHA-256:
`aa16f7e520fc56b6694e04d42e81a6f58c0ffe64b4db30c432fb2bd77692052f`.
Complete audit stdout SHA-256:
`6e3eee81ffb975b006b7c53441c2821fd3dbc0acd02f856427e3adb4312f705a`.
Complete root-build stdout SHA-256:
`8c0c4d16eaaff4def9652e1db48310faa2259e6363a506ff3acbcc9a50347425`.
Raw receipts remain task-local; the script, source hashes and reproduction
commands are committed. No compiler, toolchain, manifest, checker policy,
withdrawn-question record, or live scheduling ledger was changed by this task.

## Remaining obligations

The represented executor now has concrete all-successful-step and arbitrary
finite-interaction preservation for these additions. It remains a partial
executor, so `none` must not be treated as safe termination or progress.

The remaining principal/context constructors, full normalization, nonempty-owner
freshening with immutable evidence identities, graph guardedness, source/native
realization, effects/lifetimes, whole-language progress and inference
soundness/principality/termination remain OPEN.

`CallProgressObstruction.lean` already proves
`reachable_typed_viewed_force_stuck` for the current formal Call relation.
Its missing Force/View transition must be repaired and validated before a
general progress theorem for that relation can hold. This is a formal-relation
obstruction, not a newly established source-language defect.
`PaperFreshHeapAllocation.lean` proves `FreshHeap.self_alias_payload`: payload
typing alone permits a self alias at arbitrary type, including Bottom. The
separate graph/alias/guard argument cannot be replaced by the new absurd rule.
Nonempty-owner continuation resumption also needs a distinction between
immutable evidence and current owner/world identities. Existing withdrawn
semantic questions retain their status.
