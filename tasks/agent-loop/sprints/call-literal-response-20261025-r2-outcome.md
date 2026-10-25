# LEAN-CALL-LITERAL-RESPONSE-20261025 — reviewed r1–r3 outcome

Status: **CLEAN formal literal/response component accepted by primary; Git integration pending.**
Baseline `3a1af4d9c1c31b13d4d6bbc5e12acf3d55b08484`, branch
`research/simple-sub-intrusion`. The original full Yulang semantics/type-inference,
source/native and Call/inference A/B goals retain their original domains and
quantifiers and remain **OPEN**.

## Before, construction and parent application

The preceding reviewed source audit identified a concrete representation gap:
Raw Literal contained eight kinds, but Original.Val could type only unit among
them. Native integer, Boolean and string responses could not supply the formal
closed response judgment at their corresponding base types.

CoreSyntax now represents all eight existing literal domains. Seven constructors
extend Val while unit retains its original constructor. Literal.base and
Literal.toVal preserve each payload and its existing base type. Val.raw produces
the exact existing literal atom. Bool/Int, bytes/path and char/string remain
distinct; no normalization, lexical validity or native encoding is assumed.

CoreSubstitution gains only the seven inert value cases in renaming, substitution,
their typed mutual proofs and their raw-commutation mutual proofs. All existing
theorem statements and computation/binder cases are retained. CoreExecution is
byte-unchanged and successfully rebuilt: arbitrary raw successor lifting and
finite raw-prefix safety cover the extended typed fragment.

CallLiteralResponse proves total literal typing, exact erasure, injectivity,
uniqueness of all typing and arbitrary rename/substitution invariance. Its two
actual-request applications construct the closed ValueTyped derivation from
the literal and explicit operation response-type equality. They do not assume
that derivation. The applications retain arbitrary actual prefixes, worlds,
metadata, typed literal suffixes and captured frames, the exact completed
request endpoint/length, response substitution and plugged-computation typing.
Thus the accepted request-boundary lemma is applied to concrete literal data,
including distinct integer responses, rather than left as an unused lemma.

The source authority is the existing literal rule at
`docs/yulang-operational-type-safety-ja.tex`:215. No language rule, compiler,
runtime transition, diagnostic, expectation or source-domain restriction changes.
The allowed typed external-host protocol at docs:1140–1174 stays intact.

## Two explicit amendments and preserved failures

R2 adds only the missing typedCallBind/typedCallAdapter cases to
ControlComposition.request_progress. FrameTyped has no constructors for those
frames, so both are discharged by inversion. The theorem and transitions are
unchanged. Initial row8 failed on these missing cases; repaired row9 passed.

R3 corrects the initial verification inventory: CallEntrySpineRepair is a
historical FAILED_VERIFICATION / UNACCEPTED candidate, superseded by the identical
completeCallEntry_typed proposition in accepted CallEntrySpineComposition.
The unchanged replacement passed row19 and is imported and queried in row33.
The failed predecessor's row20 consumer' diagnostics are preserved. Exactly five
historical candidates are excluded and unchanged: CallEntryTyping, CallEntrySpine,
CallStepTyping, CallUnwindTyping and CallEntrySpineRepair. No accepted theorem was
discarded. ForceAdmin/ForceCompletion are unchanged and outside this delta.

R3 also explicitly corrects the blanket r1 axiom condition. Exactly three
pre-existing generic Control theorems (resume_reusable, finite_trace_safety,
finite_prefix_control) retain their documented [propext, Classical.choice,
Quot.sound] dependencies. Their complete statements/proof bodies are byte-identical
to baseline. All other queried targets retain the strict [propext, Quot.sound]
subset; the new construction lemmas use no axioms and the two actual-request
applications use only propext. No additional exception, custom axiom or proof
hole is introduced.

## Verification and independent adjudication

The append-only JSONL contains all33 invocations, including failures8/20, with
commands, complete source text and output streams, start/end times, elapsed
monotonic time, exit/timeout, recursive input hashes and generated output hashes.
Total recorded Lean duration is19.340464230008365 seconds. The latest successful
rows cover all30 admitted modules; row33 checks38 signatures and38 axiom reports.
Every final source/import/output hash was revalidated, including reused rows.
The final query has23 explicit examples; the new module has10 more. General
lemmas cover all literal payloads and binder maps beyond these examples.

Checks used one Lean process at a time, `-j1 -M1024`, under the cumulative80-call,
240-second grant. Existing Control unusedSimp warnings and the unchanged
CallViewedForceReachability unused-variable warning remain in the receipt.
No warning-free, whole-package, native-runtime or independent-execution claim is
made. The five unaccepted historical files are not a green whole-package build.
`git diff --check` and the scheduling static check passed. Earlier57 tooling
unit tests were not rerun for this formal proof delta.

Fresh nonauthor `/root/call_literal_response_review_astra_r1` independently
inspected source, all8 literal domains, mutual proofs, raw safety, response
application/quantifiers, binder discriminators, final input/output chains and
both amendments. Verdict **CLEAN**, no blocking/major/minor finding. Primary
accepts that verdict for the frozen bytes below. The reviewer did not rerun Lean.
Author `/root/call_literal_response_astra_r1` and primary (two-branch repair,
verification and composition intake) are contributors and not independent
certifiers of this component.

## Frozen evidence

| Artifact | SHA-256 |
| --- | --- |
| r1 contract | `11487ebfcb1622d5313a201cf55fb8e068d616a2a93d087618e6eadecf25423f` |
| r2 contract | `387a53dd652d93bee6cfa7fa8b8e2b694b510a4b1dd0c1b922e9d953af58f809` |
| r3 contract | `e1f64274f1c6126abd1914dd2fd0e68784eb66ab060d74bcd6a6c6e1692cb45c` |
| CoreSyntax.lean | `c5a25cb7d935159b62f377b7fa88b3e92e4cdf429118d566e53f7859f6ea5375` |
| CoreSubstitution.lean | `ae1dfd4947d9e87c05dfa893b93067175d860ed3b5da000d61257d7789208b55` |
| CoreExecution.lean (unchanged) | `86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e` |
| ControlComposition.lean | `4e8e4cb4fdf106bbffa11e21cd9f7030bda1f296f14e1a554560ea802f02dc5e` |
| CallLiteralResponse.lean | `62cffcd2bcf5ce879c3c7b75ff6908b19470a27e5ca73e5973ec1affbeaac3fb` |
| Final query (.lake, full text embedded in row33) | `adfbfb535d6801a46ce2e17b20174f4707f6a5af3bb9df3f2837185094fd4726` |
| Verification checker (.lake) | `2501d5b134d04958b54a92b2d4f0f0cb8bf7ef759c8cd478a0760459d416556c` |
| inbox/20261025-call-literal-response.md | `c27af8b71ed5a59c4b28256a995183416478bb178bd010df3778a45410f27c56` |
| inbox/20261025-call-literal-response-r1-verification.jsonl | `4328e908b606fb5bd8cadb38a32daecfe3d59d92913fd39c95fcf816f046a763` |
| inbox/20261025-call-literal-response-r1-review.md | `33e922986e35103c73bac4d0814c2a5d912ed3b806ebe49e13339b7f90731417` |

Contracts/outcome are under tasks/agent-loop/sprints; inbox paths are under
tasks/agent-loop; Lean sources are under notes/theory/lean/YulangClosure.
The exact60 generated-output leases are r1's list minus the two historical
CallEntrySpineRepair outputs under r3. Generated files and scratch remain ignored.
The source handoff retains its historical candidate status; this later outcome
records independent acceptance without rewriting that immutable handoff.

## Remaining premises and resource/Git receipt

RESPONSE-ENCODING-1 is reduced: the existing literal representation is now
constructive, but faithful source annotation/native value readback and callable
types, code and captured environments remain open. RESPONSE-INSTANCE-1 still
needs one shared identity/type-instance interpretation across request, response
and template. RESPONSE-TEMPLATE-1 still needs frame/environment/owner/view and
nested-handle correspondence. Full source/native traces, Force source realization
and original inference A/B are not closed. All remain assigned to primary intake;
the preceding source audit locates their producers and falsifiers.

NO_SAFE_CODE_SLICE remains justified by the inspected native primitive_matches /
ResumeArgument and capture_template / enter_template owners: no runtime defect
or approved production change follows from the representation gap. Formal
implementation now consumes the literal construction at the actual request
boundary. Do not repeat Force's unchanged-constructor investigation without new
evidence. Consult the existing dispatcher at this completed component boundary
for the next original-parent construction.

Author and reviewer requested Astra/medium, effective telemetry UNKNOWN. Both
reported all writes STOPPED, no descendants or continuing processes; each full
300-second reservation is charged. Current-sprint dispatcher consultations total
240 seconds, STOPPED; earlier360 seconds remain separate (600 cumulative).
The1800-second envelope is retained: author300 + primary600 + Lean240 + review300
+ integration120 + dispatcher240. Failed invocations and grants were not reset.
Three legacy UNKNOWN reservations remain quarantined. Static scheduling checks
do not authenticate runtime identities or prove mathematical/source closure.

At freeze no literal-sprint commit/push has occurred. Only the four changed/new
Lean sources, three contracts, author handoff, verification receipt, independent
review, this outcome and current.json are intended for explicit staging.
CoreExecution and generated/scratch files are not staged. Primary will inspect
the entire outbound range and push without forcing; actual Git success belongs
in the subsequent compact-state receipt, not a prospective claim here.
