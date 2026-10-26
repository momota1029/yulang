# Independent review: original identity Name realization

## Verdict and frozen artifacts

**PASS for the stated conditional local source supplier. No blocking finding
or requested source/note correction.** This review does not close original
Function introduction, source soundness, Effect hygiene, principality, or
inference termination.

The producer and reviewer are different assigned leaves. The reviewer had
no authoring role in this target. The primary assigned the frozen source,
then separately supplied the frozen paired note. Both hashes were checked
before the final verdict:

| Artifact | SHA256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/OriginalIdentityRealization.lean` | `30b0676f4af22dc7da2c75596a338db57a24b17662a4057801cfdff7ab4a2f42` |
| `notes/theory/2026-10-27-original-identity-realization.md` | `a82cea17ac7081fc95e74a632cf6250233ffffce74682633b0258afe0bffeab3` |

The checked result joins the completed argument Force/Return branch, the
fresh native formal binding, the subsequent Name receipt and value, and
the original generated Lambda body consumer. The note accurately leaves
the rest of the constructor and its execution correspondence open.

## Source and dependency review

The review read the complete target source and paired note, then followed
the relevant definitions and proof bodies through `OriginalSourceClosure`,
`OriginalReturnWorld`, `OriginalFormalAdmission`,
`OriginalSourceEnvironment`, `OriginalSourceGeneration`,
`OriginalSourceChecking`, `OriginalSourceInterpretation`,
`OriginalForcedParameter`, `OriginalParameterSemantics`, and
`SourceIdentityWorld`/`NativeClosureEnvironment`.

The governing source checks were Source-Generalize
`2026-10-08-source-generalize-definition-and-proof.md`, especially the
Parameter/Lambda/Name/Call schemas and Desc/Event/EventProof ownership;
`2026-10-08-call-semantic-input-realization.md`, especially hereditary
compatibility and actual Return/Name interpretation; and the corrected
`2026-10-26-source-relay-return-instance.md`. The latter's distinction
between retained carrier C and returned identity closure W is preserved:
forming W does not execute its prospective Value-entry invocation.

Native comparison covered `tools/inference-playground/src/runtime/machine.rs`
Value-entry setup and completed argument return, `bind`/`extend`, lexical
Name lookup, `dispatch_name`, and `consume`. This establishes the intended
ownership of the represented operations; it is not a new whole-machine
simulation proof.

## Decisive checks

### Descriptor and invocation quantifier order

`generated_identity_name_realization` computes `Identity.formalDescriptor`
from the given `FormalAssignment` and the complete ambient `Telescope`.
Its conclusion puts `exists description, view` before `forall invocation`.
The descriptor is fixed outside that universal quantifier. The generated
source is the original `Build` of the Value-entry identity Lambda; its
body resolves the formal through `identity_body_resolves_formal`.

The theorem retains arbitrary declaration, context, ambient telescope,
route, sites, formal name, and annotation parameters. It does not replace
the telescope by an empty one or demand global site freshness. This is
still conditional on the actual `Satisfies (closureKernel ...) ... Build`
premise, not a theorem that every such input has a satisfying derivation.

The actual formal admission construction supplies the entered-body
judgment. The main theorem does not receive that judgment, a source Name
judgment, or a preassembled body-consumer certificate as an extra input.

### Same complete Call, carrier, demand, Force, and Return

`receipt_recovers_call` reconstructs the raw admitted invocation and its
complete `CallInput`. Its `CheckedDomain`, active input, and descriptor
assignment are retained through the actual receipt decoding. The input
retains the original value/root/event, context, continuation,
carrier/root/view, receipt, typed path, consumer, and incidence fields.

`Use.carrier` uses that exact input's carrier, root, and event.
`receipt_origin_carrier` proves equality of the entire carrier row with the
recovered challenge's carrier row at the checked inlet of the original
invocation descriptor. It does not replace that inlet by the carrier's view
interface or select another admitted carrier.

`ForceCut.demanded`, `ForceCut.executed`, and `ForceCut.actualReturn`
refer to this same row, the same demand event, and the same raw observation
at `use.before`. The return descriptor is the already selected formal
descriptor. `use.before` is computed from the post-Force packet snapshot;
it is not silently identified with the earlier receipt event.

`ForceCut.whole` is a substantive remaining recursive premise:
`Meaning (.carrier (use.carrier operator))`. It is not supplied by the
opaque `carrierAccepted` field. The new theorem eliminates that premise
through the original carrier/trace interpretation to derive the pre-bind
world and returned membership. It does not assume the final world,
returned value membership, body judgment, or complete Call safety as its
own result certificate. The source and note both expose this distinction.

### Real lookup and the Name receipt update

`native_name` derives successful lookup from `bind_read` at the fresh
environment index, followed by `name_success` and the explicit raw
receiving-view match. It does not take successful Name lookup as a field.
The binding retains the actual lexical parent, raw value and view; the
fresh cell's semantic interpretation is the preselected descriptor and
the same returned value/root.

`nameEvent` performs the represented native receiving receipt insertion.
`name_event_receipt` proves the new receipt at the old receipt count, the
incremented count, and unchanged receiving views. Thus world reasoning
does not treat a Name observation as a receiving-world stutter.

`name_event_world` unfolds the original world meaning. It retains the
alias, capture, and shared clauses through their concrete readouts and
restricts each installed binding certificate along the supplied original
compatibility relation. `force_supplies_name` then derives the actual
Name world and value membership, followed by restriction of that same
descriptor/value/root to every compatible future.

The native limit is precise: `SourceIdentityWorld` is a world projection.
The `dispatch` argument is an externally supplied result of the Name
dispatch operation; this theorem does not run or verify the separate
dictionary-machine update or its errors. The callback-entry path and the
authenticity of raw packet/readout data are likewise not supplied here.
The paired note's explicit native-execution authenticity obligation
covers this boundary. The result must not be cited as an unconditional
successful full Rust Name step.

### Runtime Event, EventProof, and exact body ports

`value_entry_consumer_at_receipt_ports` constructs the actual retained
Shared body state after the admitted Return. It proves that state's event
is the Return readout event, that the relevant interfaces equal the
receipt state's interfaces, and that the selected formal contract is
preserved. The main theorem uses `computed_return_event` to identify this
runtime event with `use.bound descriptor`.

The independent `EventProof` may change logical eta/witness. No equality
between its event and the runtime event is assumed or proved. The
consumer action obtained from finite `Checking` quantifies over every raw
observation at the fixed body-final and Lambda-body-consumer ports. This
allows it to act on the later actual Name observation without such an
event equality.

`NameRealization` uses precisely
`state.interfaces (nameSite, finalRoot)` and
`state.interfaces (lambdaSite, bodyConsumer)`. It retains the original
pure-Return trace-form equality, independent observation guards, and
positive observation fields. These fields are not manufactured from
the finite checking derivation.

### Every future and the scope of Function elimination

The derived membership keeps the same descriptor, returned value, and
root through every `operator.compatible` future; only the event changes.
`realized_name_future_function` further quantifies over every actual
provider of that same value/root, every complete original admitted
challenge, and every executed raw observation. It returns the original
`ActualAdm` and `ObservationMem` conclusions.

This is elimination of the returned formal value's Function membership,
when its descriptor is Function. It does not introduce the identity
closure's own Function membership, prove its captures/provider case,
or identify the relay's carrier with that closure.

### No circular safety definition or relative-meaning cast

The source premise is the original generated formula with actual finite
`Checking`; the bridge follows `checking_sound` and `computation_action`.
There is no replacement of typing by safety and no new complete-Call
certificate assumption in the main theorem. `Meaning` is the original
greatest fixed-point interpretation. The new file neither mentions nor
casts into `Background`; the relevant imported background results unfold
their relative operator separately.

## Independent kernel checks and declaration audit

All checks used the supplied pinned executable
`/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake`
from `notes/theory/lean`, with `lean -j1 -M1024` and no output-file option.
The observed toolchain was Lean 4.35.0,
commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, and
Lake `5.0.0-src+eb6cafb`. The authorized escalation was used to execute
the pinned checker; no build or cache mutation was requested.

| Independent check | Actual result |
| --- | --- |
| `lake env lean -j1 -M1024 YulangClosure/OriginalIdentityRealization.lean` | Exit 0, no diagnostics. |
| Exact-source scratch copy plus `#check` and `#print axioms` for all 15 authored theorems, including the private helper | Exit 0. The copied prefix was compared with the frozen source byte-for-byte. |
| Imported originating-module census, printing every type and transitive axiom set and rejecting unapproved axioms | Exit 0; 213 declarations, 129 theorem declarations. |

The census is independently constructed using the environment's original
module ownership. It includes private and generated declarations, rejects
target axiom declarations, and rejects any transitive dependency outside
`propext`, `Classical.choice`, and `Quot.sound`. It uses
`pp.fullNames`, `pp.privateNames`, `pp.proofs`, `pp.deepTerms`, and
`pp.maxSteps = 1000000`. The final log has 213 matching begin/end records,
213 axiom rows, no errors, and no `...`, `…`, or `⋯` elision.

The census found 129 theorem declarations (15 authored and 114 generated),
72 definitions, 4 inductives, 4 constructors, and 4 recursors. Across all
213 declarations, the axiom groups are exactly 107 with none, 98 with only
`propext`, 5 with `propext` and `Quot.sound`, and 3 with all three allowed
standard axioms. No project axiom, `sorryAx`, hole, or checker bypass was
found. The main theorem is not axiom-free.

Every authored theorem's type and axiom set was checked. The authored
axiom inventory is:

| Axiom set | Authored theorems |
| --- | --- |
| None | `identity_value_entry`, `name_event_installed`, `name_event_world`, `carrier_keeps_actual_call`, `realized_name_future_function` |
| `propext` | `name_event_receipt`, `receipt_origin_carrier` |
| `propext`, `Quot.sound` | `native_name`, `native_name_installed`, `force_supplies_name`, `receipt_recovers_call`, private `name_realization_of_consumer` |
| `propext`, `Classical.choice`, `Quot.sound` | `identity_body_resolves_formal`, `value_entry_consumer_at_receipt_ports`, `generated_identity_name_realization` |

The first census harness failed because its two local counters lacked
explicit `Nat` annotations. Only the scratch harness was repaired; the
failure log is retained. The initial source-copy printer also elided three
proof subterms, so the unelided full census is the authoritative full-type
receipt. Neither issue required a target change.

Independent evidence files:

| Artifact | SHA256 |
| --- | --- |
| `/tmp/yulang-identity-review-audit.lean` | `329423d55f295aaf86c910bfcd42b75077c3f79e74a04475a92f83b7682e015c` |
| `/tmp/yulang-identity-review-audit.log` | `63fa4102c0a32ec3170756b1d6ec3de63393c4a474a2b389f6b5da16840c4520` |
| `/tmp/yulang-identity-review-census.lean` | `7f311fdb7aa9c71cee3510fcb6e76f816993aa31400c27ef59ceec647af9ee97` |
| `/tmp/yulang-identity-review-census-final.log` | `964a1ccd69809e97136e16e59c91b979c688251bcb5e264747a675684ebd81cc` |
| `/tmp/yulang-identity-review-authored-full.log` | `e98b2feacad87abb8c53ad253611369a4c941d643ebe94aef5660595ac27ef4d` |
| `/tmp/yulang-identity-review-census.log` (initial harness failure) | `82ba561f035ac5db4283a71c07a2abf73d0d93db63efe81fe6c01cf35f24f081` |

## Checked source revisions and remaining owners

These hashes were independently compared with the paired note:

| Source | SHA256 |
| --- | --- |
| `OriginalFormalAdmission.lean` | `77230ab7984ee544db16fe4d9663b73f98b9afa9c5d2610fad59c26753d5ac7c` |
| `OriginalForcedParameter.lean` | `d16a45c459ea78b0f583ebd34d7a442d7247b55358ff6d990e3416c3d841aedf` |
| `OriginalSourceClosure.lean` | `e39f165848c512830e6f92893c61e2d9f07cec66b729e8878c5f7d3491ab429a` |
| `OriginalReturnWorld.lean` | `0710f5d969af927c8f42b42f4972ba4f53ddce4ddb082e9d3d360e90c9ccf12b` |
| SG definition/proof, 2026-10-08 | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| Call semantic input realization, 2026-10-08 | `fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a` |
| Corrected relay Return instance, 2026-10-26 | `b8d806d2768cc1231ca4361ebe221190fde3f988f0c3ca7f41edc868e52afdbf` |
| Native runtime `machine.rs` | `b621ba8ec28d7819db881a4fd5bad0236edbf23e2aa92a879eb1dd211a30c46e` |

The first remaining semantic premise is the same-call whole-carrier
Meaning. Its source formation/admission realization belongs to the
original Call input interpretation; `carrierAccepted` does not discharge
it. Authentic native execution must also supply the packet, dispatch,
readouts, trace form, compatibility, coherence, and guards. The original
Lambda/Call constructor still owns zero-step/admin/pending observations,
Request/resumption suffixes, invocation Return/deactivation, captures, and
provider introduction. Original principal transport still needs its
nonempty complete source instance and the original comparison proof.

Those are explicit open boundaries rather than defects in the local
conditional theorem. No general closure status changes follow from this
review. Integration and any wider completion adjudication remain with
the primary.

Only this leased review record and the reviewer's unique `/tmp` artifacts
were written. No target/note, compiler, existing proof, shared status,
root import, Git state, build cache, or `.olean` was changed; no child was
spawned. All owned checker sessions ended. Review writes are stopped.
