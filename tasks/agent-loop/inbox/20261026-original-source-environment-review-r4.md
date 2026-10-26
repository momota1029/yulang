# Original Source Environment R1 repair — independent delta review

## Current verdict and exact scope

**ACCEPT** the frozen repaired source
`971f67a932a663981bc7f72eaeb818d558c4ab65ed7580057c2f0b2cfeb11f07`
for its explicitly conditional local construction. The earlier **MAJOR R1**
finding is repaired: App's actual callable is selected from
`callee.returnedValue`, while a Lambda retains its closure's `finalRoot`.
No new material defect was found in this delta.

This acceptance covers source-owned App/Lambda registration, its immutable
frame fold, the retained raw callable in invocation admission/capture, the
separate per-goal descriptor readout, and the conditional local Function
constructor. It also retains the previously inspected Shared witness,
entry-prefix restoration and complete alias projection. It does not close
full original Kernel interpretation, all Checking constructors, L4, other
source/client subject owners, original native generated satisfaction, or
whole original inference soundness. The original full-language parent scope
is unchanged and OPEN.

In particular, the existing binder admission does not receive a CheckGoal.
Its domain is the source binder's descriptor domain. The semantic Function
step is accepted with its explicit `targetReadback`, semantic child induction
hypotheses, view/event readback and target guard/capture premises. This is not
acceptance of a global interpretation for arbitrary intermediate Checking
goals. A separate goal-indexed admission packet is required for that bridge.

Reviewer: `/root/original_source_review_r4`, independent of author
`/root/whole_soundness_route_r4`. Delta activated 2026-10-26 13:45:54 UTC.
The only repository write was this exact receipt. Scratch is exclusively
`/workspace/scratch/f98087c7ac1a/source-environment-review-r4/delta/`.
No producer edits, Git, shared status/import/configuration edits or children.
The prior REPAIR receipt is retained verbatim below and as immutable evidence,
SHA-256 `1e7d3bca139b47a43214f5853156b007386d32d701eeccc96a0085246dd9128b`.

## Governing source and original application

The adopted authority remains
`notes/design/2026-10-08-source-generalize-definition.md` §2 selecting
`notes/theory/2026-10-08-source-generalize-definition-and-proof.md` §§3–5.
The latter §3.2 requires same-operand logical composition and complete
Function checking on the original independent domain; §3.3 distinguishes
source descriptions, Shared evidence and actual runtime events. The
accepted `OriginalSourceGeneration.sourceRules` and `Checking` definitions
are the actual original construction used here, not a replacement grammar.

The following correspondence is constructed in the frozen module, under
namespace `YulangClosure.OriginalSourceEnvironment`:

| Original obligation | Actual repaired construction and checked roots |
| --- | --- |
| The ordinary App checks the callee's returned value against the App descriptor | `source_app_value_incidence` proves that exact `Premise.checking` occurs in the generated source rule. `source_app_call_owner` records the same callee/argument sites and source context. |
| The original callable differs from the eventual App result | `CallOwner.subject`, `registered_app_subject`, and `registered_app_callable` select `(callee.site, returnedValue)` for both value and root. The source binder descriptor is read separately. |
| Lambda's own invocation opens its closure | `source_lambda_call_owner`, `registered_lambda_subject`, and `registered_lambda_callable` retain `(lambda.site, finalRoot)`. |
| Registration must come from raw source rather than a successful derivation | `sourceCallOwners` calls the immutable accepted `sourceRules`; `Root.withSource` installs that result. `localCallOwner` reads actual `sourceCallIncidence` / `closureFormation` atoms. No solved descriptor, admission, execution success or membership is consulted. |
| Every source container and scope wrapper must be traversed | `callOwners` / `forestCallOwners` recurse through every rule/forest constructor, every quantifier/publication/initializer/execution wrapper, and both choice branches. The registered owner classes in this packet are explicitly App and Lambda. |
| Descriptions must not change actual subject identity | `Root`, `Decoded`, and raw `Actual` retain the registry. `runtime_preserves_call_owners` and `decoded_call_owners` cover the complete frame fold; `logical_preserves_callable_owner` retains owner, endpoint, actual value and root. |
| Invocation admission and observation capture must select the same callable | `DataAdmitted` reads value/root via `callRow`; `admitted_invocation_captures_subject` proves the captured active input contains those same original raw operands. |
| Composition must not equate actual subjects with every intermediate descriptor | `goalRow` changes only the checked upper descriptor. `goal_row_same_subject` preserves actual value/root/event; `function_shape_for_registered_owner` permits arbitrary lower/upper descriptor endpoints at the same registered occurrence. |

The absence-of-owner fallback in `callSubject` is not source evidence.
`FunctionShape` requires a registered owner at the actual site/context.
No original case is justified by an arbitrary caller-written registry or that
fallback. Raw IDs retain their existing resolved-source interpretation;
this packet does not prove the full native resolver/site-allocation bridge.

### Complete independent admission and the genuine remaining boundary

The repair does not normalize raw candidates, consult stored anchors to admit
a challenge, or add a provider catalogue/target-validity filter. Invocation
admission retains every raw current configuration, carrier, view token,
receipt, path, consumer and incidence field. Its checked-domain test remains
`CheckedDomain` on the whole reconstructed challenge. The existing
`original_challenge_supplies_admission`, `admission_recovers_challenge`, and
`admission_ignores_stored_maps` preserve this correspondence, subject to the
explicit original view/event readback equations. Neither registry data nor
checked descriptors are placed in actual event keys.

`FunctionShape.decoded` now contains registered source owner/site/context and
Function classifications. It contains neither `targetReadback` nor a domain
inclusion or body/output certificate. The local
`function_checking_constructor` retains both finite Checking children and
concludes `FunctionAt inputs Z (state.goalRow binder goal)`. Its exact extra
premises remain visible: `DomainMeaning`, `ObservationMeaning`,
`targetReadback`, view/event readback, source Function membership, and target
guards/captured positive fields for every actual provider.

The target-alignment residual is substantive. For a fixed actual subject,
let the original binder descriptor 30 admit carrier `false`, while an
intermediate target descriptor 40 admits carrier `true`. `goalRow` and the
shape can represent the intermediate descriptor without changing the
callable; binder-only `DataAdmitted` still tests descriptor 30. Therefore a
complete interpretation of that intermediate Checking occurrence needs its
own authentic domain/telescope alignment. The frozen note and handoff state
exactly this limitation. Moving `targetReadback` outside `FunctionShape`
correctly avoids presenting a false general shape law; it does not prove the
missing global alignment. No global domain-coincidence assumption is accepted.

### Retained scope and actual/logical separation

The repair delta preserves all previously inspected fixed-frame/readout
machinery. `Decoded.fixedFrames` and `Actual.fixedFrames` retain complete
Shared/runtime payloads including witness, binder and entry-path metadata;
all six runtime semantic readouts see that prefix. Logical frames preserve
actual identity. Restore uses the original entry frames and names, while the
complete initialization history remains separate for replay. The extended
`Actual` record carries the same immutable source registry, and
`publication_data_matches_fold` / `alias_preserves_complete_publication`
retain complete entry/completed projections and captures. No new cloning of
Shared evidence, publication identity or runtime invocation payload appears.

Observation meaning with no active invocation remains `False`; this does not
silently validate arbitrary observation-mode identity. The full source proof
must still be indexed by actual decoded, mode-admissible occurrences.

## Exact frozen evidence and census reconciliation

All final author manifest entries were verified twice, including at
13:53:56 UTC: **3 repository outputs plus 68 scratch artifacts, 71 entries in
total**. All remained byte-identical. The author's 68-artifact count refers
to the scratch list, not the additional three repository outputs.

| Frozen artifact | SHA-256 |
| --- | --- |
| Environment source | `971f67a932a663981bc7f72eaeb818d558c4ab65ed7580057c2f0b2cfeb11f07` |
| Theory note | `bd637740fa5e5de73f6dad80cbbe8ba0a039ab026b7fbb548578af376557e9ee` |
| Author handoff | `86dfff994f16b06cc3da22d5e1f958af095f614686d08350eb57cd49d17eedcb` |
| Author final-freeze manifest | `ab2d3fc5f66d59d5233ed59c0bfa2092e8e4af0132073d2a95cd98e24cdba0f8` |
| Author complete check22 census | `977ca2c089ce3eb7cca11337886b56d8ed17feaea3353219d714fca84edd867f` |
| Author audit source | `fb4222727dd9549fb7c2eec7cb10b6c70112a6c189c906703e49c8fa660062f7` |
| Reviewer extracted 76 full public types/axioms | `d7052b86d127a30930c2f889b700f0a066ad303625e7fa59b0720669c00722d7` |

The exact author audit uses the originating module index, enumerates every
private/generated declaration, rejects project axioms, prints each complete
explicit type and transitive axiom set, and checks every required public root
is an originating theorem. The reviewer reconciled **753 unique complete
BEGIN/END declaration pairs, 289 theorem constants, 76 public theorem roots,
and 13 probe axiom records**. The source's 76 public theorem names all match
that inventory. Every printed axiom set is within `propext`,
`Classical.choice`, and `Quot.sound`; that is the actual union. The accepted
check22 log has no errors or warnings. No `sorryAx` or recovery artifact from
any failed audit is counted as accepted evidence.

The author's final 13 probes include nonconstant closure `true` / root7
versus App Unit result `false` / root23, actual generated App premise,
encoded invocation value/root, genuine Lambda subject, and descriptor40 /
descriptor30 retaining one callable. The eight original raw-payload,
current-state, view-token, Shared-prefix and publication probes remain.
These are finite representation/source discriminators, not a complete
original semantic model or a proof of the opaque source input relations.

## Independent verification and retained failures

The authorized three focused bundles were consumed without extension.
Every actual Lean compilation used the pinned native Lake/Lean 4.35.0,
`-j1 -M1024`, one CPU affinity and the exclusive delta project/cache/TMPDIR,
with `PYTHONDONTWRITEBYTECODE=1` and a 120-second total bundle watchdog.
The exact commands, exits and times are retained in the three runner logs
and summaries. No independent census completion or expanded-probe success is
claimed.

1. `focused01` failed before Lean checking: the reviewer-added 1280 MiB
   **virtual-address** cap caused Lake `--version` to abort with thread-creation
   resource failure. Runtime 0.015 s; exit -6. This is tooling evidence, not a
   mathematical failure. The log and runner are preserved.
2. `focused02` resolved Lake/Lean versions and independently rebuilt all nine
   exact mathematical modules from source: Syntax, Generation,
   NativeClosureEnvironment, Contracts, SourceIdentityWorld,
   SourceFunctionMembership, NativeDictionaryDenotation, Interpretation,
   and Environment. **All nine exited 0 with empty diagnostics.** The extra
   reviewer-only audit then failed on a nested-source reduction proof, a
   trivial Source.site normalization, and untyped metaprogram Nat counters.
   Its failed source/log are preserved; the whole audit is rejected. Bundle
   runtime 41.461 s. Selected standalone declarations in that failed file
   printed standard-only axioms, but this is not promoted to an accepted
   independent audit suite.
3. `focused03` repaired those reviewer expressions and attempted only the
   extra audit against the already built exact inputs. Expanding the nested
   annotated source fixture reached the **Lean kernel -M1024 memory limit**,
   producing further error-recovery diagnostics. Runtime 7.877 s; exit 1.
   The whole audit is rejected; its recovery axiom names are not accepted.
   No production module was edited or reinterpreted to make the probe pass.

The resident-memory sampler in the wrappers reported only approximately
10 MiB and did not resolve child processes reliably in this PID namespace;
those aggregate samples are not treated as valid peak-memory measurements.
`RUSAGE_CHILDREN` reports 1,015,112 KiB for bundle02 and 1,056,200 KiB for
bundle03; the Lean heap cap was active, as the latter diagnostics show.
The intended aggregate watchdog does not constitute independently verified
aggregate-memory enforcement. No further checker call was made after the
three-call budget. This tooling limitation is preserved rather than hidden.

| Reviewer artifact | SHA-256 |
| --- | --- |
| `delta/check/focused01.log` | `72c9e3d41a5a514ba88af6523ca2ded9bf140816a1975bb8eca0d29cc5104aef` |
| `delta/check/focused02.log` | `abfb0809bbac2f70644504b13d167bab5acb234eca9401093352aca14f073990` |
| `delta/check/focused03.log` | `998f59e81ef3b56261962b727ef5452eb31097d46269c9c1c23dec84b63cd5e7` |
| Final rejected extra audit source | `6ec051500ef2d94f7d837ae4a64ce6be49358c3058b0df3917e3fbeb4b4ea4dd` |

### Concurrent integration configuration

During this review the primary reported unrelated publication `fb6f2905a`,
adding WholeMetatheory/default-target integration. The frozen nine math
modules and all author artifacts remained unchanged. The independent build
used its captured historical project configuration, not a silently refreshed
current one:

- checked `lakefile.toml`: `cab85ff9a8a7dc5103fe932739dcea0dfc02e6420b1277565449882c802473bd`;
- current `lakefile.toml` after the unrelated glob addition:
  `e62c909702ea210955e7d4b1c5d19991a1997a96990f70eb398f3044a479b56d`;
- both toolchain files: `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`;
- both package manifests: `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`.

The current configuration adds only `YulangClosure.WholeMetatheory` to the
library glob list. This review's explicit nine-module rebuild is not a
combined current-default-target integration check; that belongs to the
primary. No mathematical input drift is inferred from this unrelated change.

## Stop and parent boundary

The R1 source-port defect is closed for the frozen conditional local packet.
The accepted mathematical evidence is the complete reconciled author census,
the successful independent nine-module rebuild, and independent direct
inspection of source correspondence and proof premises. The two optional
reviewer audit attempts are explicitly not PASS evidence.

Full goal-indexed admission, all other authentic source/client subjects,
actual RuntimeReadout/LocalAdmissions interpretations, full current-world
certificates, target guards/captures, view/event/future compatibility, L4 and
native/source inference closure remain with their original owners and parent
obligations. No global theorem is asserted and no original source form,
challenge or witness-sharing obligation is removed.

**WRITES STOPPED** after this receipt and the delta freeze manifest. No
checker, child or other process remains running. Only the primary may
integrate or change shared status.

---

# Preserved prior R1 receipt — superseded verdict for the old fcb6 source

The following historical receipt is retained verbatim. Its REPAIR verdict
continues to apply to the old `fcb6c1f5…` snapshot, not the repaired `971f67a9…`
source accepted above.

# Independent OriginalSourceEnvironment review r4

Receipt revision: 1 — **REPAIR**.
Reviewer: `/root/original_source_review_r4`, independent non-author.
Producer: `/root/whole_soundness_route_r4`.
Finding: **R1, MAJOR, blocks semantic acceptance of the frozen packet.**

The frozen Lean declarations and their census are checker-successful, but the
Function/admission interpretation selects the wrong actual source operand for
an ordinary App. This is an original-source correspondence failure, not a Lean
kernel counterexample. The primary adjudicated R1 as a required repair rather
than a claim-narrowing opportunity and activated the original author for repair.
No acceptance of the rejected bytes is implied by the successful census.

## Assignment and authority

Activation: 2026-10-26 13:20:56 UTC. Budget: 1200 wall seconds, at most two
focused Lean check bundles of at most 120 seconds, one thread and `-M1024`.
**No independent Lean check was run or needed.** The source mismatch is explicit
in the original generated rule and the frozen field definitions; the primary
directed the reviewer to retain the finding and release the slot for repair.

The sole repository write lease is this receipt. The sole scratch lease is
`/workspace/scratch/f98087c7ac1a/source-environment-review-r4/**`.
No producer code/proof/note, Git state, shared status/import, configuration,
dependency, native source, or expected output was edited. No children were
created. Actual runtime identity is the supplied agent ID; additional session
UUID/model/effort evidence is UNKNOWN. No custom runtime is claimed.

The already-read AGENTS/design-authority/proof-closure/referee requirements and
the `yulang-lean-proofs` skill were applied. The review read the entire frozen
module, note, handoff and audit source, and checked them against:

- the actual accepted `OriginalSourceGeneration.sourceRules` App and Lambda
  rules and the finite `Checking` constructors;
- source Generalize §§3.3–3.4 and §§5.1–5.2, including fixed actual fields,
  separate description/evidence regions, same-event witnesses and scopes;
- the selected contextual Function membership and immutable semantic-input
  definitions already reviewed in the preceding interpretation packet;
- the accepted `OriginalSourceInterpretation` definitions of full challenge,
  same-provider membership, raw/checked observations and source assignment;
- the full original `SourceProblem.InferenceSoundness` and sameScoped boundary.

## Exact rejected freeze and preserved evidence

The producer's freeze was at 13:19:54 UTC, with writes stopped before review.
All **52** repository/scratch entries in its manifest were byte-verified before
the primary activated the repair. The full rejected source, note, handoff,
manifest, audit, census and relevant accepted Generation source are copied to
the reviewer's exclusive `evidence/` directory. These immutable review copies
remain authoritative for this receipt even while the author prepares a new
revision of the repository files.

| Artifact | SHA-256 |
| --- | --- |
| `OriginalSourceEnvironment.lean` | `fcb6c1f530aa6b84aa8e0af012d0ed7a997e75034183145515c173fdcbb45ed3` |
| `2026-10-26-original-source-environment.md` | `94f205f5487bc7af8f949c319186ae94a08b80f1a0996e6a3c86bdf8a07885f7` |
| Author inbox `20261026-original-source-environment-r4.md` | `071c51c930d553d50f3206b3e05a329b2e9fa0763cb2a75c53ab3a02f1a82f9e` |
| Producer `final-freeze.json` | `5e66ab670d043a32128d1cf8530eb86bf13e0536b42935634c2439aed5c39ecf` |
| Complete check15 census | `858ca5fe417aa310b69da36a87716bf5f500299e7b850a249d0b32f06020b43b` |
| `OriginalSourceEnvironmentAudit.lean` | `8d5f2724a911ceae69323b21991ad2a97e35a3f7ca0687d1bc2404001c4d0fcc` |

Producer baseline: `ee61ba0b68789e2dea9eac024130f21c5a4e6453`.
Accepted Interpretation publication:
`8622f29d2c1b8934f8b257574c4b6b0e3db5ca42`, source
`feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef`.
Accepted Syntax/Generation remain respectively
`3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1`
and `ab37f3739d89dff9e7918fb745f5a308a3e597ab4aaa9e5a172fcacaeddabf0b`.
No Git operation was used to replace these exact byte identities with a
worktree-status assumption.

## R1 — wrong callable endpoint in the actual App checking rule

### Original rule and smallest source specimen

Take the raw source App whose callee is an identity Lambda and whose argument
is the Unit literal, written schematically as `(λx.x) ()`.
Let its App site be `a` and its callee site be `c`.

The actual adopted builder emits this value-checking premise for App:

```
goal.site  = a
goal.lower = Endpoint(c, returnedValue)
goal.upper = Endpoint(a, descriptor)
```

The actual callable is the value returned by the callee at `c.returnedValue`.
The App's own `a.finalRoot` is its result. In this specimen those are distinct:

```
value(c.returnedValue) = closure_f, root(c.returnedValue) = r_f
value(a.finalRoot)    = unit,      root(a.finalRoot)    = r_unit
```

The target Function description at `a.descriptor` is a third, independent
source-owned field. Equality of solved descriptions does not identify either
of these actual objects or roots.

### Frozen definitions that conflict with that rule

The frozen `Decoded.callRow` unconditionally selects:

```
descriptor := state.assignment.descriptor (binder.site, descriptor)
value      := state.assignment.value      (binder.site, finalRoot)
root       := state.assignment.root       (binder.site, finalRoot)
```

`FunctionShape.owner` requires `binder.site = goal.site`. Its `decoded` field
relates the descriptor slot to `goal.upper`, but supplies no authentic incidence
selecting the callee's returned-value object.

For the original App goal, `callRow` therefore selects `unit/r_unit` rather than
`closure_f/r_f`. This affects **admission itself**: `DataAdmitted` requires the
raw invocation's value and root to equal the `callRow` values. A genuine raw
invocation with `raw.value = closure_f` fails that equality when the App result
is Unit. The full `CheckedDomain` is then tested at the wrong callable tuple.

Consequently the hypotheses and conclusion of
`original_challenge_supplies_admission`, `observation_child_transport`, and
`function_checking_constructor` concern the wrong source operand in this
ordinary generated case. Their internal proofs remain valid for the row the
definitions chose; they do not establish the claimed original App application.
This is not repaired by retaining every view token, observation, provider or
future event after the wrong object has already been selected.

The eight producer probes use a constant endpoint-value map and do not derive
the App value goal from `sourceRules`. They therefore cannot distinguish the
callee's returned callable from the App's result. This explains why the source
defect survives the successful census/probes.

### Required repair and composition constraint

The primary assigned the original author to construct a source-owned callable
subject endpoint map, retained independently of logical descriptions and
membership. `callRow`, invocation decoding/capture, `DataAdmitted`, and the
Function-shape correspondence must select the **same original actual subject**.

For the authentic generated App root incidence, the subject must be
`callee.returnedValue`; the App descriptor and final-result ports remain
separate. For a Lambda invocation, the closure's own finalRoot can be the
correct original callable subject. These are owning-rule facts, not a choice
made from a desired Function description or successful typing.

**Do not impose subject = every intermediate `goal.lower`.** The primary
explicitly corrected this potential overrestriction during adjudication.
`Checking.compose` retains the same site/environment while its children use
first→middle and middle→last descriptor endpoints. The actual source occurrence
subject remains fixed across those checks. Only the authentic original App
root incidence identifies its subject with the callee-returned operand;
intermediate lower/middle/upper descriptions remain independent.

The same caution applies to the frozen descriptor-slot equality in
`FunctionShape.decoded`: a repair must not accidentally freeze every
intermediate checked upper descriptor to the App's original descriptor slot.
The fixed actual subject and each checking child's descriptor interpretation
have distinct responsibilities. This is an acceptance constraint on the
repair, not a demand to finish the entire Checking induction in this packet.

The required discriminator should construct the App checking incidence from
the actual raw-source rule and use nonconstant value/root maps distinguishing
the closure and Unit result. Its genuine raw invocation must select the
closure and retain the same complete challenge. The existing incoming-current,
raw-payload, Shared-prefix and publication checks should remain valid.
Fresh final hashes and a new all-originating census are required after repair.

## Other reviewed boundaries

No additional independent blocker was established in the static review of
the repaired Shared-prefix and publication machinery. This is not acceptance
of the rejected packet as a whole.

- `Runtime` and `Logical` are separated; actual raw view tokens differ from
  their logical interface interpretation. Incoming runtime history/current
  configuration is retained, and raw candidate payloads are not normalized by
  an anchor map.
- The exact Runtime/Shared prefix is retained in both `Decoded.fixedFrames`
  and `Actual.fixedFrames`. All six runtime readout maps receive it, including
  the complete Shared witness and original binder/entry metadata. Typed-frame
  proofs relate it to the original `Binder.isFixed` classification.
- Logical frames preserve the computed actual projection. Restore begins from
  entry frames plus caller logical frames; completed fixed history remains
  separate replay data. Alias readback preserves the complete publication
  projection rather than merely matching a name.
- `Admitted` does not consult anchor/publication maps as domain filters.
  Original semantic view/event readback equations remain explicit. However,
  R1 means that the current invocation domain is attached to the wrong source
  subject for App, so map independence alone does not establish correspondence.
- Folded literal/formal-Name applications read the entire decoded prefix and
  keep the independent current-world premise. Authentic runtime readouts,
  installed-world correspondence and LocalAdmissions remain open inputs.
- `FunctionShape` does not contain whole inclusion or body-safety predicates;
  domain/observation child meanings, target guards/captures and future
  compatibility remain explicit. Full Checking/L4 closure is not claimed.
  `ObservationMeaning` with no recorded invocation remains False; the note
  correctly does not claim an unconditional identity-checking theorem there.

The pre-freeze Shared-access repair is distinct from R1. Its old successful
source `3b89f37656c8163ca18ababe5565e34a60e2b14b30c7b0950288d161d3f6392d`
and successful check12 census
`26e6506b8633e770ff69e7b96fd902d4ac7a11cfb224a8f724b1c6a2d6ee66cc`
remain preserved. Neither superseded version is accepted by this receipt.

## Census and verification reconciliation

The final producer audit source was read in full. It selects declarations by
Lean's originating module index, includes private/generated declarations,
prints complete types with explicit/proof arguments, verifies required theorem
roots, and checks transitive axiom Names. The reviewer independently parsed
the entire check15 log and compared all public theorem names with the source.

| Evidence | Reconciled result |
| --- | --- |
| Originating declarations | 651 unique, balanced complete type/axiom pairs |
| Theorem constants | 242, as reported by the actual module census |
| Public theorem roots | All 63 match the source declarations and complete log entries |
| Concrete producer probes | Eight complete axiom reports; audit source reviewed |
| Axiom union | `propext`, `Classical.choice`, `Quot.sound` only |
| Diagnostics | Check14 module log empty; check15 census has no errors/warnings or accepted `sorryAx` |
| Independent Lean calls | 0 of 2; no redundant checker run to rediscover an explicit source-port mismatch |

All producer failures/superseded attempts remain in the verified manifest,
including checks02–09, the failed check11 audit fixture and its rejected
placeholders, the successful but superseded check12, and check13's retained
unused-simp warning. No reviewer probe failed or was discarded. No producer
cache was written by the reviewer.

Reviewer evidence contains the complete public type/axiom extract, SHA-256
`a9fba8509d05c900bb4cbad432345e671e1c80cf317f004672bc6ccb05328d1a`,
and `census-and-freeze-review.json` with the full source/public-axiom map.
All evidence is under the sole reviewer scratch lease.

## Parent disposition and stop receipt

The original parent remains the full source/inference soundness obligation,
including authentic subject identity, complete Call/effects/scopes, all original
constructors and one shared witness strategy. R1 is a concrete missing/wrong
source incidence and must be repaired at the original source/environment
owner. It is not a reason to reject the ordinary App, narrow the grammar or
assume the desired callable membership.

Even after R1 repair, authentic view/event actions, all seven Kernel fields,
full finite Checking and L4 induction, native generated satisfaction,
SameScoped and original InferenceSoundness retain their exact existing
obligations. The primary owns repair authorization and the subsequent frozen
review/integration. This receipt grants no acceptance of a future mutable
revision.

**WRITES STOPPED.** No reviewer Lean process, postprocessor, child or unresolved
descendant lease remains. Only this receipt and the exclusive reviewer scratch
were written. The retained finding receipt releases this reviewer slot for
the already-authorized original-author repair.
