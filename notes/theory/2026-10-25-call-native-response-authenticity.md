# Native response authenticity: source audit and first representation obstruction

Status: candidate source/native evidence; unreviewed, no theorem or production promotion.
Author: `/root/call_native_response_astra_r1`; primary `/root` contributed the
independent representation/protocol observation incorporated below and therefore
is a contributor, not an independent certifier of this combined result.
Contract: CALL-NATIVE-RESPONSE-AUTHENTICITY-20261025/r1,
SHA-256 `e1e260369eb0ee55acd3bcf49759a45f56692e2cb3f9928d95d2338a0eb03f06`.
Declared baseline: `d1308e8b0612abf95f25d7adae137e9b769269db` on
`research/simple-sub-intrusion`; no Git command used to independently inspect it.
Requested Astra/medium; observed model/effort UNKNOWN.

## Original parent and concrete application

The unrestricted source/native safety and Call A/B parents remain OPEN.
`CallRequestBoundaryComposition.lean::actual_call_request_completed_response`
quantifies over every typed Call term, world, typed arbitrary suffix, actual
prefix, requesting operation/payload/continuation/observations, and completed
request prefix. It additionally takes
`hv : TypedCall.ValueTyped Original.emptyContext response op.responseType`.
Its conclusion preserves the exact operation, completed boundary and literal
suffix, and types plugging the response into captured frames. This audit supplies
neither the source-to-Call prefix encoding nor `hv` for all native responses.
No independent suffix/F1/FK1 quantifier is replaced by one local replay action.

The actual first obstruction is a missing faithful value/type representation,
even before proving native acceptance implies `hv`:

* `Original.Ty` (CoreSyntax:105) has base/thunk/union/intersection/top/bottom,
  but no callable type. `Original.Val` (:113) has var/unit/delay/injections/both/top;
  it has no int, bool or string value constructors. Raw literals exist separately.
* `TypedCall.Value` (:247) adds var/original/delay/view, not native closures.
  `TypedCall.Function` is a separate structure, not a response Value constructor.
* Candidate constructor-inversion observation: there is no derivation of
  `TypedCall.ValueTyped empty v (.base b)` for `b` equal to int, bool or string.
  A Value variable contradicts empty lookup; delay concludes thunk; original
  reduces to Original.ValTyped where only unit concludes a base and var requires
  empty lookup; view reduces to its subderivation. This is an unmechanized
  argument about the present fragment, not a source safety counterexample.
* Unit alone admits the concrete derivation `ValueTyped.original ValTyped.unit`
  for `.original .unit : .base .unit`. This can supply the response-typing
  subpremise once an interpretation maps the retained declaration's result to
  unit and native Unit to that formal value. That interpretation and source
  trace correspondence are not presently defined by these owners.

Consequently replacing every native response by formal unit, treating a callable
as a thunk, or using raw literal syntax as though it had a ValueTyped derivation
would change the required correspondence. A future faithful extension is not
ruled out; it needs a separately scoped proof packet. Ordinary inference and
accepted source semantics need no weakening to expose this missing construction.

The governing prose explicitly retains a typed external response protocol
(docs:1140–1174), including syntactically typed callback code and well-typed fresh
graph extensions. Eliminating that permitted premise is not a parent requirement.
Internal source callable safety cannot be moved into the host premise.

## Complete native acceptance slice in the inspected runtime

| Owner | Actual formation/acceptance evidence | What remains for formal typing |
|---|---|---|
| `machine::return_value`, ResumeArgument, :1006–1080 | Reads result of retained template declaration. Accepts primitive_matches OR exact_v1_function_response; passes the exact ReceivedValue into EnterTemplate. | Interpretation of value, result type, operation instance and closure environment; closed derivation. |
| `machine::primitive_matches`, :1769 | Requires Value interface, receiving view pointing at that same value handle, and matching Unit/Int/Bool/Str kind. | This is a native kind/identity check, not a syntactic typing derivation. The last three kinds cannot inhabit corresponding present formal base types. |
| `machine::resume_host_write`, :599 | Only current stopped UnhandledRequest, exact continuation/operation and program host capability, unused saved continuation, matching template declaration, string payload. Allocates Unit itself, ground view and Value role; resumes exact template. | Unit derivation above is available locally; operation and whole-state interpretation still missing. No arbitrary caller-supplied response is accepted here. |
| `lib::execute_program`, :278–326 | Public execution route calls resume_host_write only for program.host_write_operation; other unhandled operations terminate with error. | Public host execution is distinct from arbitrary protocol responses permitted by the prose theorem. |
| `program::exact_host_write_operation`, :1310; is_host_write_signature, :1349 | Resolved public std::io::console/out export identity, one operation identity, exact effect-free str -> unit declaration. | Identity-to-Nat and type interpretation, consistent with request instance and hole. |
| `machine::propagate_request`, :2100–2240 | Matching handler operation declaration ID, live installation, closed_primitive OR local_grant, primitive payload, one payload pattern. Continuation binder allows primitive result or exact v1 function route; capture occurs before selected handler is popped. | Formation of a typed captured context and response type, including all retained source constraints. Wildcard/no continuation abandons suffix and is not a response acceptance entrypoint. |
| `machine::Callee` continuation branch, :1211 | Actual executable continuation handle is copied into ResumeArgument; source response argument is evaluated through the ordinary delayed argument/execute path. | Source argument typing and closed environment realization. This is not a host injection route. |

Search for resume entrypoints in `tools/inference-playground/src` found the
crate-private host method, its public execution caller and tests; EnterTemplate
is assigned by the two acceptance routes above and by its own recursive entry.
No other production acceptance branch was found in this inspected runtime.
This bounded inventory does not claim all compiler backends are represented.

`receiving::matches_value` (:293) is precisely `views[view].value == value`;
it does not establish effect coverage, unknown=false, image provenance, ownership,
or a ValueTyped premise. `ground` (:196) does create unknown=false/no image for
its same value. Preserve these distinctions; do not collapse receipt lineages.

## Backward formation and exact v1 limits

Source operation declarations are constructed by HIR source_annotation.rs:330–380
from act member syntax with parsed Function signature. SourceOperationId consists
of family identity (module/declaration) and operation declaration key (:33–60).
The runtime Operation instruction retains the resolved declaration. Callee's
operation branch (:1337–1418) clones it, selects Value/Computation payload entry
from argument effects, and creates the request carrier via OperationPayload or
make_request_carrier. Request and template retain that same declaration Arc.
There is no native type-argument vector in SourceOperationDeclaration or
ResumeTemplate corresponding to all fields of formal OperationInstance
(operation Nat, typeArguments, payloadType, responseType). Monomorphic native
identity preservation is useful evidence but not a polymorphic instance proof.

The v1 producer has more evidence than mere occurrence coincidence:

1. `candidate_source.rs:907–946` joins request, arm continuation binder and a
   unique local response definition; its annotation must equal the declared
   response annotation. It checks a lambda initializer, callback application,
   callback family and expected result effect row.
2. `candidate_effect.rs:1120–1154` retains LicensedOperationFieldV1 and
   CallbackFieldRealizationV1, constrains the actual lower/upper effect edge,
   checks conflict and only then sets consumed. This is retained source and
   propagation evidence, not an independently proved full typing theorem.
3. `shadow_apply::operation_v1_field_bounds` (:2013) publishes only consumed
   records with final solver errors empty. `program::evidence_for_operation_v1`
   (:450) requires candidate/HIR identity and exactly one consumed receipt.
4. `program.rs:1120–1205` joins the actual operation label, response initializer
   through Forward nodes to Lambda, unique handler continuation application and
   local definition argument, callback in lambda body and response invocation.
5. `machine.rs:864` creates Closure with parameter/role/body/environment;
   Name at :831–840 records response-definition value/environment/site.
   ResumeArgument checks matching value/read site, actual lambda source root and
   occurrence, continuation application occurrence, Closure executable, Value
   role and same-value view. It does not derive body or captured-environment
   typing, nor compare a formal instantiated operation type vector.

These owners preserve meaningful construction evidence. Reusing their consumed
receipt as `ValueTyped` without an inference-to-source-typing theorem and native
environment interpretation would be an unjustified bridge. No solver or
Simple-sub generation, propagation, levels, extrusion, intrusion or generalization
was changed, bypassed or treated as dispensable.

## Template hole, ordering and forwarding

`capture_template` (:1841–1910) starts with exactly one Hole at index 0. For each
saved suffix entry it appends a node whose inner index is the preceding root,
then adds the containing Owner. No transition mutates this template. Ordinary
frames become Bind (GlobalRead/Root are rejected); RootCompReturn becomes View;
receiver/ambient boundaries become Owner; skipped handler boundaries become
ForwardHandler. Nested ResumeArgument retains its distinct existing template
handle, never merges its hole or declaration with the outer one.

Candidate structural lemma, directly by loop/entry inspection: every successfully
published template has one descending inner chain ending in its unique Hole.
Each successful enter_template step preserves exactly the input ReceivedValue;
Hole returns that value unchanged. Bind pushes saved frames while descending
outer-to-inner. If propagation popped frames f1 then f2, suffix is [f1,f2],
construction nests Bind(f2,Bind(f1,Hole)), entry pushes f2 then f1, so f1 runs
first on return. Administrative Owner/View/ForwardHandler steps must succeed;
this is not a theorem that every replay completes.

`propagate_request` skips nonmatching operation arms, then pops a nonselected
CatchReturn into SavedFrame::HandlerBoundary (:2305), later reconstructed as
ForwardHandler with fresh occurrence and resolved live owner. The selected
handler itself is popped only after capture, so is absent from that template.
This is the shallow/forwarding distinction specified at docs:444–456. There is
no TemplateNode::Skip constructor; skip is this propagation behavior.

The local identity/order lemma applies to the response-to-hole subobligation.
It does not identify this stack with `CallState.captureFrames`/plugResponse:
that still needs typed frame encoding, environment realization, owner/view
renaming interpretation and an actual source/native simulation, preserving
foreign continuations and arbitrary suffixes.

## Discriminating attempts and their limits

| Attempt | Source-backed discriminator and result |
|---|---|
| Different operation | Handler arm mismatch continues searching; host checks exact operation and continuation. Declaration is retained in captured template. No source path changing it found. Polymorphic argument correspondence remains unencoded. |
| Unrelated closure occurrence | v1 initializer/unique local join plus runtime lambda occurrence/root and read-handle checks reject the simple substitution. Multiple dynamic activations at one source occurrence still require environment realization; no malicious reachable activation established. |
| Matching value, wrong view | A view for another value fails matches_value. A different view of the same value passes this particular check; that does not prove a wrong view is source reachable or invalidate raw value typing. Coverage/hygiene needs its own premise. |
| Wrong template hole | Constructors publish one chain with one Hole and preserve response; unrelated private arena mutations are unreachable forged-state probes and were not used. Nested handles remain distinct. |
| Reversed capture order | The two-frame symbolic trace above restores correct stack order. No reversed-order witness obtained. |

Existing source fixtures at machine.rs:3018 and :3467 contain operation int -> int
and `k 11; k 23`. They are useful source inputs for a later authorized encoding
falsifier, not newly executed evidence of acceptance. No source-qualified safety
counterexample is claimed, and no runtime/test/Lean invocation was performed.

## Required next construction and mutual TODOs

RESPONSE-ENCODING-1 (Luna/proof owner): define faithful source annotation/native
value interpretation into the accepted typed core, first handling native literal
payloads/results and then callable closures with captured environments. Retain
the original parent and full case ledger. Minimal falsifier: attempt to produce
closed ValueTyped at `.base .int` for actual native integer 11 in the present
fragment, without changing its type or erasing its observable literal. Constructor
inversion above blocks it. Proposed future output is a separately leased checked
syntax/typing extension and source translation; this is not authorization here.
The minimal first candidate is an Original.Val constructor carrying the existing
Original.Literal, a literal-to-Base function and corresponding ValTyped rule,
with raw erasure to the existing literal atom. Its dependent substitution and
Call embedding cases need checking in that packet. This formalizes already
accepted literals; it is not a new language semantic decision. Callable types,
closures/environments and operation/template encoding remain separate later work.

RESPONSE-INSTANCE-1 (Luna/source-proof owner): interpret source identity and any
actual instantiated type arguments once, shared by request payload, response and
template hole. Falsifier: same spelling/different declaration or different type
instance maps to one instance, or payload/result use independent substitutions.
Inputs: SourceOperationDeclaration formation and source instantiation owners.

RESPONSE-TEMPLATE-1 (Luna/native-proof owner): lift the local unchanged-response
and order facts to frame/context encoding, preserving environments, forwarding,
Owner/View renaming and nested handles. Falsifier: formal plugging differs for
two distinct captured frames, nested continuation or skipped handler.

NO_SAFE_CODE_SLICE: inspected ResumeArgument/primitive_matches and
capture_template/enter_template establish local native invariants, while the
first bridge owner is the formal representation and encoding. No production
fix is justified by this audit. The host protocol premise remains allowed.

## Dependencies, reuse and receipt

Reused only the reviewed request-boundary theorem's stated typed-response
premise and exact boundary conclusion, source v1 receipts within their bounded
premises, and the governing prose's typed-host protocol. Rejected promotion of
kind/shape checks, existing tests, raw syntax, source IDs or effect receipt
consumption into an unrestricted ValueTyped/source simulation theorem. No
unchanged Force constructor investigation was repeated.

All eight contract direct hashes were inspected and match the frozen contract:

| Path | SHA-256 |
|---|---|
| docs/yulang-operational-type-safety-ja.tex | a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b |
| notes/theory/lean/YulangClosure/CoreSyntax.lean | dff3e5851c9ef971ec404f9542d684074a13623bb0820c3a5e4d5da072783ece |
| notes/theory/lean/YulangClosure/ControlSyntax.lean | 1f937e4c51b79d1a2dc4a2291a1e3f5797403eae5975a53a42d574867a1690f0 |
| notes/theory/lean/YulangClosure/CallRequestBoundaryComposition.lean | fed00f06cdbf2a5bdc1b3c18957acc33c7b281e890f277ca5bd1d20ece53ee76 |
| tools/inference-playground/src/runtime/machine.rs | b621ba8ec28d7819db881a4fd5bad0236edbf23e2aa92a879eb1dd211a30c46e |
| tools/inference-playground/src/runtime/program.rs | 6607c4371366739c0e593b29a5da96becbb0bd743b2618a3755653f1b0ac3907 |
| tools/inference-playground/src/runtime/receiving.rs | 57b1664e26f137e6425731dde2bb1f1559170d9914f5be7a0f17fae3a8555e26 |
| tools/inference-playground/src/runtime/continuation.rs | 194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3 |
| tools/inference-playground/src/lib.rs | 45bf78af436efa50e02ca97ba3b639c11f7dd88272d87c47f2822643786653d4 |
| tools/inference-playground/src/runtime/primitive.rs | eb0a53bfec8ce2854adbe6342c984d5140fd1585d91da5a8a9739d2ac96e8a85 |
| crates/yu-hir/src/module/source_annotation.rs | 409ce491bc216c6963bf76d20810790aa2756edf260ecc35e76d5cfc05d24b3f |
| crates/yu-solver/src/candidate_source.rs | 57b119592a6a8d4afd42aca10c5e2bb749cfdf0fb0fdea967dd437d552a1a04e |
| crates/yu-solver/src/candidate_effect.rs | 70c42056a1041d54f88f16d7712875e3acf9ef7649b99a34bc990ff19f04936f |
| crates/yu-solver/src/shadow_apply.rs | f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d |

Three substantive stages completed: acceptance slice, representation/parent
application, discriminators/freeze. Resource reservation is 300 active seconds;
charge the full reservation conservatively, no renewal. Read/hash inspection
only; no tests/builds/Lean/runtime probes, Git, nested CLI or external contact.
No descendants or persistent subprocesses. Only this artifact and the assigned
inbox were created; no scratch paths. Writer stops on final frozen handoff.
Fresh independent review and primary adjudication remain required.
