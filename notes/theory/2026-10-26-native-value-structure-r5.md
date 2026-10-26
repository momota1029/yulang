# Native Value outer structure and dispatch construction r5

Date: 2026-10-26. Author: `/root/value_structure_r5`.
Original baseline: `97788357754a57562607dd8ff41ac55ffcb3c9b8` (`yulang3`).
Status: constructed and kernel-checked component; fresh independent review required.

## Original obligation and exact contribution

The original parent is `MERGE-EXPANSION-COVER-1`, as retained in
`2026-10-26-native-merge-expansion-construction.md` §6, and ultimately the
unchanged original `SourceProblem.InferenceSoundness`. The accepted Context
construction forwards a complete Value request, while the independently reviewed
`NativeValuePorts` constructs four structured child vectors and their complete
Context/Flow/port admission and ordered enqueue loop. This module supplies the
missing outer selection between those constructors and the other native Value
branches. It does not replace the original source language or native inference.

`NativeValueStructure.lean` imports the exact reviewed `NativeValuePorts.lean`
whose SHA-256 is `f49bf12537633c65b4dbdcb4e739df5de5eee76cfb5ad845c8dba50cef4101fa`.
The isolated project contains the immutable baseline's Lean/configuration files
plus that one frozen module and this new module. No changing sibling module is
an input. The reviewed ValuePorts dependency was subsequently integrated by the
primary; its bytes remain identical. This worker did not edit it.

## Native source correspondence

All line locations below refer to the immutable original baseline.

| Native owner | Constructed Lean owner | Exact boundary |
| --- | --- | --- |
| `lib.rs:14432–14529` outer Value branch | `dispatch`, four `dispatch_*_iff` roots | Current-memo reuse precedes canonical rewrite, which precedes retained rewrite, incompatible-shape checking and constructor dispatch. Raw memo-current and retained readbacks remain supplied table observations, not completion theorems. |
| `lib.rs:16494–16523` incompatible shapes | `lowerShape`, `upperShape`, `incompatible`, `incompatible_exact` | Exact positive/negative tags and Tuple arity; BottomPositive and TopNegative are never incompatible. Raw malformed polarities remain represented, without asserting a native formation invariant. |
| `lib.rs:14515–14529` Bottom/Top | `operand_bottom`, `operand_top` | Exact local no-child shortcut, distinct from diagnostic acceptance. |
| `lib.rs:14530–14594` Variant | `operand_variant`, existing `variantChildren`, `variant_domain_iff`, `variant_all_payloads` | Every positive tag/arity must match; every matching negative entry contributes every payload, with duplicate entries and original three indexes retained. Missing domain gives a pending direct witness and no partial child vector. |
| `lib.rs:14595–14664` Record | `operand_record`, existing `recordChildren` | First-name lookup, optional absence, required absence, optional-to-required unavailability, original source/target indexes and complete child vectors. Missing/mistagged term reads give ReceiptMismatch. |
| `lib.rs:14665–14705` Tuple | `operand_tuple`, `operand_tuple_arity_mismatch` | Advertised arity mismatch is caught by the earlier incompatible-shape diagnostic. Native length/tag/lookup errors in the inner Tuple branch give IdentityExhausted. |
| `lib.rs:14706–14867`, `16452–16492` Function/fallback | `readFunction`, `functionOrFallback`, `operand_function` | Four exact children come from polarity-specific store tags. A malformed tagged Function is an `expect`/`unreachable` invariant violation, not a successful row fallback or ReceiptMismatch. |
| `lib.rs:14710–14791` extrusion/fallback | `extrusionRequest`, `copiedPair`, `finishFallback` | Actual requested polarity, endpoint, receiving row and level. Candidate changed-copy rewrite precedes application. Legacy application retains the original pair. No copying/aging result is assumed correct. |
| `candidate_extrusion.rs:1115–1150` candidate application | `selectBound`, `selected_bound_exact`, `fallback_selected_pair` | Post-extrusion canonical observation, reflexive return, both row/row level cases and rigid/row cases. A selected bound's directed pair is proved equal to that current observed pair. Insert/replay effects are still separate. |
| `lib.rs:14955–15054`, `candidate_context.rs:3511–3669` typed-drain loop | `executeChildren`, existing `drive`/`drive_success_readback` | Only candidate typed-drain mode uses these exact port admissions. Both native modes remain represented by the outer dispatcher; this adapter does not claim legacy execution uses candidate admissions. |
| `lib.rs:14556–14847` direct witnesses and diagnostic edge calls | `publication`, `edgeFor`, `diagnosticEdges` | Direct witnesses retain terminal pair/kind, distance zero, no first field/index. Function Value edges retain Argument/Result; Effect edges are excluded. Tuple indexes are retained; Record/Variant indexes are not fabricated as diagnostic tuple indexes. |
| `NativeContextExpansion.valueContext` | `afterContext`, `executeAfterContext`, `context_value_children_readback` | Successful Context forwarding retains the entire original request and derives identity transformer before computed outer selection and child admission. |

`DiagnosticEdge` lists describe calls in source order, before native edge interning.
They do not claim multiplicity in the final native memo graph. `Publication.pending`
means pending native memo publication, never completed diagnostics or a successful
source typing. The fallback projection explicitly waits for the extrusion owner
before its memo-publication stage.

## Executable construction and proved obligations

`Request.key` retains Value endpoints, the stored Context ID, optional source-set
ID, transformer and all five `ScopedDemand` fields: original Call, use instance,
root, output scope and input route. `request_key_whole` and `scoped_demand_whole`
make every retained field explicit. Neither reconstructs a Call witness from an
endpoint-only identity.

`dispatch` and `operand` are total executable definitions over every endpoint
constructor. Their results distinguish duplicate reuse, canonical rewrite,
retained rewrite, no-child shortcut, pending direct diagnostics, structured
children, fallback operation requests and availability/invariant failures. The
four routing iff theorems prove exact native precedence in both directions;
they do not assume a desired all-case coverage predicate.

The structured branch equations use actual polarity-specific raw term lookups
and call the already constructed child functions directly. They do not accept a
supplied list of semantically safe children. `variant_domain_iff` supplies the
additional nonvacuous domain obligation that a zero-payload positive alternative
still needs a matching negative tag/arity. `variant_all_payloads` combines the
actual successful scan with every matching negative payload obligation, retaining
all indexes and duplicate requirements.

`finishFallback` is a post-operation control projection, not execution of
extrusion. Its candidate application uses canonical representatives observed
*after* copying/aging, rather than pretending an old bound is still current.
`fallback_candidate_apply_iff` proves that application occurs only when the
candidate is enabled and the copied pair is unchanged. `fallback_selected_pair`
then derives the exact current directed bound pair. Legacy mode is a separate
original-pair application request. No predicate asserts the missing insertion,
replay or extrusion semantics.

The principal root is
`YulangClosure.NativeValueStructure.context_value_children_readback`. Its sole
operational premise is an actual successful computation of `executeAfterContext`
from the supplied raw stores, request, arena, queue and finite proof-side fuel.
It concludes identity incoming transformer, candidate typed-drain mode, the
actual structured branch and its exact child vector, no pending admitted item,
and one list of jobs in the original child order. Those jobs yield the exact
output queue and every complete `NativeValuePorts.AdmissionResult` in the same
output arena, with no Replay acknowledgement. All admissions refer to the same
original full parent key. Successful jobs remain pending semantic work; no theorem
labels their registered relation as completed.

The fuel is a finite execution-prefix index, not a new source/native resource
restriction or a termination theorem. A malformed/failed/other-mode result is
represented explicitly. Returning `none` from this *structured execution adapter*
does not reject a source program: the outer result still identifies the distinct
native branch and its owning continuation.

## Application and first remaining bridges

This supplies the actual decoded outer Value body selection that the accepted
Context forwarding and structured port construction previously lacked. It can
feed an installed Value graph body with its complete original key and exact
issued children. It does not by itself make that graph body current, returned,
committed or semantically valid. The original parent remains OPEN.

The first native bridge is authentication of these raw observations and emitted
operations in one actual execution: pair-current and retained memo reads,
canonical representatives, processing relation, term table/endpoints, source sets,
post-check Context, scope interners and arena formation. In particular the supplied
`Routing.current` observation must be connected to `pair_is_current`'s actual
memo-membership/current-generation/completed-processing test; a duplicate result
here is not itself a completed owner. Canonical and retained rewrite requests
need the actual diagnostic/Transport/Derived path and inherited processing key,
not a guessed rewritten Context key.

The remaining operation owners include actual structural/legacy extrusion,
candidate bound insertion/replay/merge and generation changes, old-slot/versioned
history, allocation/inventory/scoped-enabled/overflow/failure behavior, diagnostic
completion/acceptance, and the shared Context/drain acknowledgement/readback proof.
`NativeDrainOwnership` conserves issued work/tickets but does not supply the
semantic installed body; this module supplies child data without inventing that
completion. Malformed Function invariant failures require the native store
formation argument, not a proof-side coercion into ordinary unavailability.

Finally original `nu,K,D,eta0`, full Function/Call/method/annotation meaning,
record adaptation child contracts and the same original scoped source witness
remain independently specified semantic obligations. This is not whole inference
soundness, principality, termination, Rust binary verification or production
promotion. No input-language restriction, compiler change or root import change
was made.

## Verification and frozen evidence

Lean/Lake identify Lean 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Every ordinary invocation uses
one thread, `-M1024` and a 120-second total deadline. Checker/cache/scratch ownership
is `/workspace/scratch/c10e953a5453/value-structure-r5/` only. The initial normal
sandbox attempt failed Lake installation detection; subsequent exact commands ran
in the authorized normal environment. No installation/configuration change was
used to repair proof errors.

The all-authored-root checker is `check09`: all 33 roots pass with full printed
types and transitive axiom reports. `check11` is the complete originating-module
census, including private/generated declarations and rejecting originating axioms
or dependencies outside `propext`, `Quot.sound`, `Classical.choice`. Exact counts,
actual occurring standard axioms, full command receipts, hashes and theorem types
are in `tasks/agent-loop/inbox/20261026-native-value-structure-r5.md`.

Calls 01–05 retain the environment failure and ordinary elaboration failures:
reserved identifier `local`, equality direction/tuple destructuring, case splitting
and one quantified Variant branch. Check06 first passes the complete outer/Variant
construction; check07 passes Context composition; check08 passes exact diagnostic
metadata; check09 is the final root audit. Check10 exited zero in Lean, but its
large persisted log was truncated during output collection; this is retained as
a collection failure. Check11 repeats the exact audit with small hashed chunks;
all 1,007 declarations / 514 theorem constants and all 33 authored roots are
reconstructed to EOF and reconciled against their markers and counts. The
514-theorem axiom census is 395 none, 108 only `propext`, and 11 `propext` plus
`Quot.sound`; no `Classical.choice` occurs. No failure was discarded or
counted as successful proof. Source search and complete transitive axiom audits
reject proof holes, project axioms, native-evaluation assumptions and kernel
bypasses. Fresh independent review is still required.
