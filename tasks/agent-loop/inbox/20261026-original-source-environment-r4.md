# Original source environment r4 — R1 repair author handoff

## Ownership, baseline and stop boundary

Author: `/root/whole_soundness_route_r4`.
Initial baseline: `ee61ba0b68789e2dea9eac024130f21c5a4e6453`.
Accepted Interpretation dependency: publication
`8622f29d2c1b8934f8b257574c4b6b0e3db5ca42`, exact source SHA
`feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef`.

Only the leased Environment module, its theory note, this inbox, and
`/workspace/scratch/f98087c7ac1a/source-environment-r4/**` were written.
Syntax/Generation/Interpretation and their previous scratch are unchanged.
No Git, shared imports, native/runtime, dependency/configuration,
expected-output edits or children. No checker or unresolved descendant remains.
The final manifest is the last artifact write; writes-stopped and its exact
hash are sent to the primary afterward. Fresh independent review is required.

## Independent finding and preserved superseded success

Review R1 found a real source-correspondence defect in compiler-successful
`fcb6c1f530aa6b84aa8e0af012d0ed7a997e75034183145515c173fdcbb45ed3`.
The old `Decoded.callRow` hardcoded `(binder.site, finalRoot)` for callable
value/root. Original `sourceRules` App instead generates
`callee.returnedValue ≤ app.descriptor`. In `(lambda x. x) Unit`, the old
readout could select the returned Unit instead of the invoked closure.

Before edits, exact source, olean, note, inbox, audit, successful census,
summary, check/input ledgers and final-freeze manifest were copied to
`superseded/call-subject-before-repair/`. The old census
`858ca5fe417aa310b69da36a87716bf5f500299e7b850a249d0b32f06020b43b`
and its 651/242/63 counts are **superseded**, not final source-correspondence
evidence. The still-earlier successful `3b89f376…` source/census remain
superseded by the already-retained Shared-prefix repair.

## Concrete R1 construction

`CallOwner.application` retains original App site/context/callee/argument;
its actual subject is `callee.returnedValue`. `CallOwner.closure` retains the
Lambda site/context/formal/pattern/body; its subject is the closure's own
`finalRoot`. Their constructors contain only source incidence data.

`localCallOwner` reads the original generated `sourceCallIncidence` and
`closureFormation` atoms. `callOwners`/`forestCallOwners` traverse every
rule-tree/forest constructor. `sourceCallOwners` applies the accepted source
builder to raw syntax, and `Root.withSource` installs that immutable registry.
The traversal retains all source grammar containers; the specific registered
owner classes proved in this repair are App and Lambda. Other original
source/client subject interpretations remain explicit future work.

`Root`, `Decoded` and the independent raw `Actual` projection now retain
`callOwners`. All frame classes preserve it. `Decoded.callSubject` reads its
source-owned endpoint; `callRow` reads both value and root there. The original
binder descriptor slot is separate. `DataAdmitted` and the actual captured
observation use the same callable, proved by
`admitted_invocation_captures_subject`.

The total readout's absent-owner fallback is provisional data, not source
correspondence. `FunctionShape` requires the actual registered owner and its
source site/context. No original application is justified by the fallback
or by an arbitrary supplied registry.

The general shape no longer fixes `goal.upper` to the original descriptor
slot and never fixes `goal.lower` to the raw subject. `Decoded.goalRow`
retargets only the checked descriptor, keeping the actual value/root/event.
`function_shape_for_registered_owner` accepts arbitrary lower/upper endpoints
at the same original occurrence. Ordinary compose can therefore keep one
callable while its lower/middle/upper descriptors change.

The unchanged `Kernel.admitted` receives environment/binder/candidate and
cannot itself inspect the current CheckGoal. The local semantic Function
constructor therefore carries explicit `targetReadback` outside
`FunctionShape` and returns membership at `goalRow`. Authentic general
intermediate-domain telescope alignment remains OPEN. No Binder.arity reuse,
checked descriptor in raw identity, anchor-domain filter or altered D_F was
introduced.

## Existing complete payload and scope work retained

The original six scoped data-map stages, complete raw invocation/receipt/path/
consumer/incidence fields, actual view-token/Interface distinction, incoming
raw history/current state, publication entry/completed replay split, full
aliases and the Shared-witness repair remain intact.

`Decoded.fixedFrames` and `Actual.fixedFrames` retain every original fixed
Shared/runtime frame, including witness, binder and entry-path metadata. All
six runtime semantic field readouts receive that prefix. Logical frames
preserve it. Restore supplies the original initializer entry prefix and keeps
completed/later fixed history separate. No duplicate completed Shared frames
are preloaded during source replay.

The source applications remain full-frame literal and value-formal Name
clauses plus the actual `Checking.function` constructor and its semantic
induction step. The latter transports complete descriptor-indexed
`ObservationMem inputs Z` for the same provider.

## Review roots

| Risk or construction | Public declarations |
| --- | --- |
| Original App source incidence | `source_app_value_incidence`, `source_app_call_owner`, `registered_app_subject`, `registered_app_callable` |
| Genuine Lambda subject | `source_lambda_call_owner`, `registered_lambda_subject`, `registered_lambda_callable` |
| Source subject preservation | `logical_preserves_callable_owner`, `runtime_preserves_call_owners`, `decoded_call_owners` |
| Admission and captured subject agree | `admitted_invocation_captures_subject` |
| Arbitrary intermediate descriptors | `goal_row_same_subject`, `function_shape_for_registered_owner`, `FunctionShape`, `Decoded.goalRow` |
| Complete challenge correspondence | `decode_encode_challenge`, `encode_decode_invocation`, `original_challenge_supplies_admission`, `admission_recovers_challenge`, `admission_ignores_stored_maps` |
| Raw identity and incoming event | `invocation_redecoration`, `two_descriptions_one_runtime_key`, `distinct_runtime_payloads`, `invocation_uses_incoming_current` |
| Exact Shared prefix | `shared_frame_retains_whole_witness`, `decoded_original_fixed_prefix`, `restore_retains_entry_witness_prefix` |
| Publication/aliases | `restore_decodes_actual_entry`, `publication_data_matches_fold`, `alias_preserves_complete_publication` |
| Native owner application | `native_receipt_token_owned`, `native_received_encoding`, `native_received_supplies_admission` |
| Original local source application | `folded_generated_literal_membership`, `folded_name_constraints_from_binding`, `folded_generated_name_membership` |
| Conditional semantic Function step | `observation_child_transport`, `function_checking_constructor` |

## Unchanged and newly explicit residuals

Full original Kernel interpretation, whole Checking soundness, L4 recursive
introduction, complete native/source generated satisfaction and original
inference-soundness closure remain open. No source form or original challenge
is removed from those parent obligations.

`domainMeaning` and `observationMeaning` are explicit semantic recursive
induction hypotheses, not laws supplied by shape. Target Function guards and
captured fields still require their actual original source/provider facts.
Actual receipt-token identity does not establish semantic view presentation:
`viewReadback` and the complete current-event `eventReadback` are genuine
owner-based field equations. Later-event/lifetime compatibility remains
required. The raw current-state fold does not prove it.

The original LocalAdmissions and opaque data readouts still require authentic
source interpretations; arbitrary predicates/readouts are not validated here.
Name's full current-world certificate remains separate from installed-object
readback. App/Lambda registration does not instantiate every other original
source/client checking subject. General intermediate D_F alignment is now an
explicit application boundary rather than an invalid fixed-target shape law.

Ordinary L3 inclusion at completed Meaning is not arbitrary-candidate closure.
No naive up-to compatibility, same-Z closure or recursive-equation principle
is assumed. Full Checking soundness also must be indexed by an actual decoded,
mode-admissible generated occurrence: identity is available without an active
invocation, whereas ObservationMeaning is false there. The local Function
step opens and decodes its invocation explicitly.

## Verification

Initial15 calls are preserved. The authorized supplemental R1 stage consumed
7 of12 calls, numbered16–22, within the 1800-second bound. Every invocation
used pinned Lean4.35.0, one thread, `-j1 -M1024`, owned TMPDIR/cache and
120-second timeout.

Checks16–20 retain their actual failed normalization/elaboration/induction
logs. The final proofs use public sourceRules equations and explicit original
premises. Check21 compiled the repaired module with empty diagnostics. Check22
passed the fresh full originating census and all 13 probes with no errors or
warnings.

Five new R1 probes supplement the eight preserved scope/payload probes:
original App premise; nonconstant closure true/root7 versus Unit false/root23;
encoded invocation selecting the closure in both value/root; genuine Lambda
closure.finalRoot; and descriptor40/descriptor30 sharing one callable. These
are representation/source discriminators, not complete semantic model claims.

Fresh census: **753 originating declarations**, **289 theorem declarations**,
**76 public theorem roots**, all private/generated declarations and complete
types/axiom sets included. Every begin/end pair matches. No project axiom or
`sorryAx` is accepted. Actual axiom union: `propext`, `Classical.choice`,
`Quot.sound`.

| Frozen R1 artifact | SHA-256 |
| --- | --- |
| Lean source | `971f67a932a663981bc7f72eaeb818d558c4ab65ed7580057c2f0b2cfeb11f07` |
| Theory note | `bd637740fa5e5de73f6dad80cbbe8ba0a039ab026b7fbb548578af376557e9ee` |
| Checked olean | `5f81410b528aeea26b4fea939843195eb5d69a3ed7e3d9d01eaeaa6413f99efe` |
| Audit source | `fb4222727dd9549fb7c2eec7cb10b6c70112a6c189c906703e49c8fa660062f7` |
| Complete check22 census | `977ca2c089ce3eb7cca11337886b56d8ed17feaea3353219d714fca84edd867f` |
| Audit summary | `550bc7a70ec5f924d222204b9cafd6017599aa2101b82b894e221b49bb133906` |

The final-freeze manifest records all current outputs and retained evidence;
its own hash and this inbox hash are sent after writes stop, avoiding circular
hashes. This is an author freeze requiring fresh independent review.
