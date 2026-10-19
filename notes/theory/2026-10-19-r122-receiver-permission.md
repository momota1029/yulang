# R122: nested receiver views and the same-HIR caller seam

Status: **conditional finite source/runtime derivation; fresh review pending**.
Assignment `R122-PROOF`, revision 1. Sole author/writer
`/root/r118_proof_lane`; no coauthors or descendants.
Producer contract rev4 SHA-256
`f32806ec7b3a547809a456f18a68ee6d33802fb62d037481dc3529311819d467`;
Luna boundary clarification: R122 rev7 SHA-256
`b29680fb01e98032dcf4472487190af97ddc19f8a4377d405cc7c0e586763cfd`.
baseline `a1d04100f6b6d175f4ca0ec20831ccba3f5d7e0e`.

## Parent, exact sources and remaining premises

The parent is the original wrong/sibling receiver-permission hygiene obligation;
the source-formal role and static/runtime projection obligations remain separate.
This packet supplies one conditional nested-view contrast and a caller identity
subedge for R117-JOIN-1. It closes none of the six effect parents or original
Simple-sub/evaluator A/B, F1/FK1 including foreign continuations, method M/T/A or
R85 adoption. Original source domains, quantifiers and separate provider,
annotation-position, receiver, request, residual and witness lineages remain.

Positive P: 210 bytes, no final LF, specified source SHA-256
`765a89c4cee89ceaf4213663b1be8e3110d0f81f4026d2112ddf4ee2f9a23780`:

```yu
act io:
    our tick: int -> int
    our other: int -> int
my relay (thunk:[io] int) = {
    my helper (pending:[io] int) = catch pending { io::tick(p), _ -> p }
    helper(thunk)
}
my main = relay (io::tick 7)
```

Negative N changes only `catch pending` to `catch thunk`: 208 bytes, no final
LF, specified SHA-256
`e1b42dbbbd1141c35857a552123e78f4bb8fe69d55bdd2429aaa6614f135705c`.
Each preparation mints its own authentic identities; no opaque IDs are equated
across P/N or direct/public preparations.

**H:** actual exact-source parsing and successful retained HIR/LocalSource
formation supply the original braced local, own formal annotations, concrete
resolved io row, Int endpoints, operation declarations, original body/call
indices and lexical resolutions below. R96's exact-source conditional
construction is reused; its old unobserved preparation is not an acceptance
receipt. Unlisted parser/annotation implementation bodies are not read here.

**A:** ordinary candidate preflight/collection/solving succeeds without conflicts,
and full RuntimeProgram/start admission succeeds for that same HIR. Ordinary
source typing, compatible operation/arm and source/view correspondence retain
their independent premises. **E:** the traced authentic schema, value/view,
receipt/execution/observation, owner/installation and primitive checks succeed.
**B-Machine:** no identity/resource/I/O failure and the predicted direct
Machine outcome occurs within 30,000 transitions. This is not a bound for the
public CLI. The preserved CLI test independently runs each source with
`--steps 10000`; its actual result is a separate observation premise and is
not inferred from this finite Machine derivation. None of H/A or either actual
bounded outcome was observed by this author. Preparation failure in N would falsify the requested observation;
it is not the predicted HandlerEvidence result.

Charter §21 assigns entry roles from each own outer source annotation. §§14–15
govern this actual shallow match/arm consumer. These clauses approve no general
permission theorem, function-as-handler classification, fresh-receiver law or
language refusal. Top-level inference principles preserve ordinary generation,
accumulation, propagation, levels, extrusion, qualifying intrusion and
generalization; no source restriction or inference bypass is introduced.

## Authentic source → candidate → runtime role route

Let R be relay's actual definition source root, t its original thunk parameter,
h its local helper ID, d helper's own pending parameter, and beta this arm's
payload binder. These are constructor-returned objects, not values reconstructed
from spelling. Both t and d have source root R but distinct parameter identities;
d's lexical owner is local h.

| Original source fact | Current owning construction | Preserved consumer fact |
| --- | --- | --- |
| relay's own annotated t | module.rs::plain_binding_header (2916 onward) retains original identifier key/annotation; lower_plan (2080 onward) mints/records t; local_source::form (596 onward) keeps its own annotation and binds Parameter(t) | Candidate registers t as its own formal; RuntimeProgram Lambda(t) and Parameter(t) Name retain that ID |
| nested helper h and own annotated d | local_source::block (1236–1339) retains original helper initializer/body, mints h, calls parameter_id for d, records d's source key and local_parameter_owners[d]=h, parses d's own annotation with owner R | LocalSourceParameter(d) remains separate from t despite equal spelling of their types and shared source root; candidate annotation scope is Local(h) |
| helper initializer captures the outer environment | Work::Initializer (654–699) temporarily installs helper self/Parameter(d), emits Lambda(d,original Catch), and forms its body while outer Parameter(t) remains live | Runtime helper closure retains original lexical environment containing t; no use of helper self occurs, so the ownership walk does not mark recursion |
| final helper call after Publish | Work::Publish (700–707) restores initializer depth then installs Local(h); final CallTail carries the naked thunk Name | Callee resolves to Local(h), argument to Parameter(t); d does not leak into the caller's final expression |
| changed Catch scrutinee | Lexical latest lookup before module namespace (1007–1040); catch forms scrutinee before payload binder scope (1120–1191) | P scrutinee=Parameter(d); N scrutinee=Parameter(t). Neither is an unresolved name or spelling-based substitute |
| same original tick and payload binder | expression/pattern operation resolution retains original declaration; Catch constructs beta from R, actual arm key and payload ordinal0 | Main tick and arm pattern share the same resolved operation ID under H; arm Name resolves to CatchBinder(beta), wildcard continuation creates no k |

The private identities' source keys and original annotation owners are retained
through source_identity::record_parameter/record_local and staged publication.
No invented numeric ID/range or same-spelled top-level binding supplies a join.

Candidate emission (candidate_source.rs 826 onward) requires pointer-identical
HIR-owned LocalSource, correct receiver/root and owned occurrences. It registers
t and d separately (858–889). Their role classifier is Computation exactly when
their own annotation's outer effects field is Some; H gives that for both.
The block visits its initializer at the existing child level, installs h, then
visits the final expression. Lambda visits retain original parameter levels and
queue FormalEntry and FormalAnnotation for each original annotation (991–1034).
Parameter Names use their registered ID and queue FormalNameEffect (1220–1257);
the negative body uses t's registration, not d's. Local h follows ordinary Local
action; both Apply edges preserve original operands/endpoints/effects/cause/level.
Catch visits original scrutinee and arm. These are actual generation/action
owners conditional on H/A, not a proof that the whole solver succeeds or that
all native propagation/entry obligations are discharged.

RuntimeProgram::from_hir (414–516) keys roles and Name consumption by the same
actual formal IDs: both t/d are Computation, and their Names Execute. Local(h)
and CatchBinder(beta) Observe. Lambda passes each original parameter to
RootCompSchema::from_parameter, whose owner, explicit outer-effects and ground
Int checks succeed under H/E (receiving.rs 21–43). Equal source root R satisfies
those ownership checks but does not identify the two dynamic receivers/views.
Block, Catch, body labels, saved lexical environments and source sites remain
distinct source objects. Complete source/runtime admission remains A.

## Two distinct received views and authentic receipts

Use symbolic actual invocations uR (relay) and uH (helper), uR<uH; boundaries
bR/bH; distinct Delays D_R/D_H and views V_R/V_H; request event q.
Invocation order follows actual new_invocation monotone allocation, not a
global theorem that every saved span must create a fresh receiver.

1. Main obtains relay's closure and delays the whole `(io::tick 7)` in its caller
   environment. Computation entry creates uR, enters the original t schema and
   binds t to D_R with V_R. Its image is bR with no inherited boundary because
   this argument is not a direct formal Name. Unknown inherited coverage stays
   unknown. Entry records authentic `(uR,V_R,Some(t))`; no tick executes.
2. Relay's block materializes h as the original helper closure capturing t→V_R,
   completes its local binding, then obtains that closure for helper(thunk).
   Callee return constructs inert D_H for the naked Name(t). direct_formal_root
   (machine.rs 1478–1494) finds that exact Execute Parameter Name and initialized
   Comp binding, returning V_R without executing it. receiving.delay copies
   V_R's image dependency into D_H's distinct delay view (receiving.rs 115–130).
3. Helper entry creates uH, calls receiving.enter for own d schema, adds bH with
   parent bR, and binds d to D_H with **new** V_H. It records authentic
   `(uH,V_H,Some(d))`. The helper closure still separately captures t→D_R/V_R.
   No annotation or row is inherited from t to d, and entry is inert.
4. Both bodies install their original Catch under current live owner uH.
   In P, reading d creates `(uH,V_H,None)` and opens execution E_H; executing
   D_H reads original t in D_H's captured caller environment while executable
   owner remains uH. That read creates `(uH,V_R,None)`, opens E_R and executes
   D_R. In N, Catch reads captured t directly: it creates the same kind of
   genuine `(uH,V_R,None)` read receipt and E_R, then executes D_R. N never
   reads d and never executes V_H. A receipt at entry is not an execution.
5. Executing the operation evaluates integer7 inside its ordinary temporary
   invocation, which ends before OperationResultConsumer executes its request
   carrier. literal::integer confirms canonical `7` given the original token.
   Current owner is again uH when q records authentic observations: P has
   `[E_H(V_H),E_R(V_R)]`; N has exactly `[E_R(V_R)]`. The operation's Value
   argument adds no Comp-root execution. No foreign observation is present.
6. Propagation ends E_R, and in P E_H, saving their root-view delimiters until
   the helper Catch is top. It does not retire uH. Old observations/receipts
   remain authentic after those execution delimiters end; the query does not
   require the observing execution or receipt to be currently active. The
   candidate installation is validated against live actual uH.

The two retained Lambdas cause primitive::closed_primitive to return false on
both programs (primitive.rs 31–37). Neither can use that independent negative
certificate or treat missing inherited coverage as negative evidence. For the
matching tick arm the decisive branch is its actual local_grant query.

## Every local_grant eligibility and alternative

The following accounts for the complete function (receiving.rs 230–323), with
candidate owner fixed to the installed uH and family fixed to q's original io.

| Query branch | P | N |
| --- | --- | --- |
| Owner must be Invocation; indexed invocation must be active | uH is actual live Invocation, not ModuleRun | Same; this does not fail due to expired or wrong owner |
| binary_search finds candidate receiver's own boundary | bH exists from helper entry | bH also exists even though pending is unused |
| schema annotation exists, owner matches lambda source, outer row contains actual concrete family | d's own authentic [io] int satisfies these predicates | The same own schema/concrete permission satisfies them; matching family alone is not enough |
| Iterate observations; reject wrong event, observer beyond next_observer, or nonauthentic execution | Both q observations were minted by observe from genuine execution records | Sole E_R observation is genuine and uses q; no phantom E_H/V_H observation is added |
| observing receipt must name exactly observation.execution.view | Holds for E_H and E_R; its receipt is retained | Holds for E_R; an ended delimiter does not falsify it |
| Candidate receipt first key `(owner,view,None)` | Genuine read receipt exists for each V_H/V_R under uH | Genuine read receipt **does exist** for V_R under uH; the failure is not missing receipt |
| Only if first key absent, try `(owner,view,Some(schema.formal.id))` | V_H's genuine entry `(uH,V_H,Some(d))` is the allowed fallback; the actual read key wins | Entry `(uH,V_H,Some(d))` is authentic but its view is not observed V_R, so it cannot satisfy this key. `(uR,V_R,Some(t))` has wrong owner and formal. No `(uH,V_R,Some(d))` was constructed |
| No candidate: continue; otherwise verify owner, exact view and optional formal equal own d | Actual selected read receipts have owner uH, correct view and formal None | Actual `(uH,V_R,None)` passes. Some(t), another owner or another view cannot be substituted; there is no all-receipts scan that broadens these two keys |
| Per-query visited memo; repeated image ends that traversal | Does not block bH: V_H's first image bH has not been visited when considered. Even if V_R were considered first, only bR would be marked | Sole V_R traversal first visits bR; memoization cannot create a route to bH |
| Image receiver equal candidate: true | V_H's head is bH, so true immediately | V_R contains only bR, whose receiver is uR≠uH; equality never holds |
| Image receiver older than candidate: break | Alternative V_R route would stop at uR<uH; this failure cannot cancel successful V_H | Actual route stops at uR<uH. Its parent is None anyway; no newer boundary can be reached by following older parents |
| Otherwise follow parent; None ends traversal; after all observations return false | Successful V_H already returns true; independent failing alternatives supply no veto | No other observation exists. Greater-receiver, extra-parent, alternate receipt or unknown flag supplies no remaining success branch; final return is false |

The optional formal alternative is exactly d from the candidate's schema, not
an arbitrary same-family formal. Current source constructs the direct read key
in both cases. The observing receipt need not be the candidate-owner receipt;
the actual query joins them by the **same view** using its permitted keys.
Here both observing reads happen under uH anyway. Unknown flags do not enter
this query as an alternative grant, and historical boundary membership is not
renamed to make V_R contain bH. This exhausts the exact finite alternatives;
it is not a theorem that all unsupported source/profile cases are ineligible.

## Exact runtime and public outcomes, conditional on H/A/E/B

P: local_grant is true. Original operation ID, Int→Int signature, one payload
binder and primitive7 checks pass; wildcard continuation causes no capture.
Selection removes this exact Catch before arm execution, abandons the saved
view suffix, binds beta to q's actual payload in the saved Catch environment,
and evaluates original Name(beta) (machine.rs 1580–1680). Observe returns that
payload; ordinary helper then relay receiver returns lead to main's existing
root publication. No raw resumption or implicit recursive force occurs. The
Completed integer is7, and lib/main render exactly `7\n`, success, empty stderr.

N: closed_primitive is false and the complete local_grant query returns false.
propagate_request immediately returns HandlerEvidence at the current handler
site (1582–1593), **before** popping the Catch, binding beta, evaluating its arm,
or forwarding to an outer handler. Machine::step converts that Err into
`Stopped(Unavailable(HandlerEvidence(...)))`, not UnhandledRequest and not a
Completed value. Existing private arenas can contain payload7; that is not a
published result. lib::execute maps Unavailable to `runtime unavailable: ...`;
main emits its error to stderr, fails and prints no stdout. The protected public CLI test separately checks diagnostic containment with
`.contains("runtime unavailable: HandlerEvidence")`; this derivation does not
claim its 10,000-step run completes.
This runtime availability result is not a source-language refusal, a general
nonprotection theorem or permission to modify ordinary inference.

## Caller identity lemma applied only to R117-JOIN-1

At current lib.rs 266–344, prepare constructs one Arc<HirModule> via one
parse/lower call. Both solve branches receive `hir.clone()` (ordinary branch at
308 for the public flags). Arc cloning retains the same underlying artifact;
it is not cloning/re-lowering a module. After successful solve/conflict checks,
the function returns `(hir,candidate)`. No branch on that successful path
reassigns hir to another module. The candidate's internal success/source
ownership laws remain their own premises; this is the caller's argument fact.

execute (167–177) destructures that returned pair and moves **that same hir**
directly into RuntimeProgram::from_hir with default evidence. It makes no second
prepare, parser/lowerer call or HIR substitution. from_hir compiles retained
sources from its supplied Arc and retains it as `_hir` (program.rs 730–747).
The operation-v1-specific pointer guard is neither invoked evidence nor needed
for this caller dataflow fact. Direct test/CLI separately lowered modules are
not equated with one another.

Specialize the lemma to R117's original direct Catch-payload source, keeping
its own HIR H117 and complete original beta/arm/component/environment identities.
Whenever its current public prepare returns successfully, the candidate solve
argument and runtime constructor argument designate H117. Thus **R117-JOIN-1's
caller identity subpremise is supplied by this conditional static caller proof**.
R117's successful retained-source/admission premise, actual candidate actions,
compatible request/selection/native transitions and wider static/runtime parent
remain OPEN. This result neither certifies R117's historical runtime hash as
current nor re-proves its unlisted effect-action consumers. Its earlier binder
lemma is reused only within its frozen premises; source/admission success is
not inferred from the same-HIR wiring or any R122 output.

## Mutual TODOs, falsifiers and stop boundary

| Request / owner | Required next evidence | Exact falsifier |
| --- | --- | --- |
| `R122-SOURCE-1` / Luna source reviewer and HIR/candidate owners | Actual H/A for both exact inputs, original t/d/h/beta, own rows and naked helper argument | Wrong/merged formal or annotation, changed lexical capture, Group/Forward obscuring direct formal inheritance, unsupported/conflicting source or N failing before runtime |
| `R122-GRANT-1` / Luna compiler/source reviewer, receiving/machine owners | Authenticate both actual view/image/receipt/execution paths and complete branch table | N lacks the stated real read receipt; an additional eligible V_H observation/route exists; P fails bH reachability; substituted owner/view/formal, missed alternative or wrong terminal outcome |
| `R122-R117-JOIN-1` / Luna's R117 caller/parent owner | Consume only the supplied caller identity subedge, retaining original source/admission/runtime conditions | A successful caller path re-lowers/substitutes HIR or a claim closes full JOIN/parent from identity alone |
| `R122-OBSERVE-1` / Luna implementation/verification lane | Frozen paired direct Machine/public CLI cells; three CLEAN reviews, then only contracted command | P not Completed7 or stream mismatch; N preparation failure, any class other than Unavailable(HandlerEvidence), Completed receipt, stdout, wrong diagnostic containment, failure/timeout/exhaustion/non-admission |
| `R122-REVIEW-1` / Luna | Fresh compiler/source, spec and regression reviews of both stopped outputs | Producer/coauthor certification, source refusal invented from availability failure, broad permission/A/B closure or semantic adoption |

No production edit or enlarged dependency is requested. New code evidence is
only the separately authorized test-only observation. No additional in-envelope
writer step remains after freeze. Luna owns review, integration and all central
status decisions; these candidate results do not independently certify parents.

## Frozen dependencies, provenance and resources

All 26 input hashes from rev4 and its contract hash matched the frozen bytes.
The direct proof sources are recorded below; the complete immutable inventory
is rev4's manifest. No dependency body beyond its listed paths was inspected.

| Direct input | SHA-256 |
| --- | --- |
| charter §21/§§14–15 | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| inference principles | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| R96 source/conditional proof | `2e6026e77d04fa6385e82ecf62cf9f0e63448bcd7619fb6500f11ca2789fe9a9` |
| R96 proof handoff | `84b3302c61e4a20e882552c960c95dadb5e9cb14bae80a5e9e810815f18de583` |
| R96 implementation handoff | `fb99947f978ab905bc65e5f7291ff38f18a74c062b2bc1fe2c5f85113f69b2d6` |
| R117 projection proof | `efd4a06e222e5de2bb546e3eb2cde1db1eba8710e7b42bda65b8139b1aea708a` |
| R117 proof handoff | `36dda08e16d90bab40f87c92b969e8f4c7a4fcc0683c0658f0c7a7f05ec44f6a` |
| runtime/receiving.rs | `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9` |
| runtime/machine.rs | `fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46` |
| runtime/program.rs | `c2363ad42104b895519bb29a8eb9aeda545bd0176cebbd78750d3a2df90849ca` |
| runtime/primitive.rs | `97485b9439357497aaf3f19555b1d87eef4aabc955b3a2815f23cf49a65c0153` |
| runtime/literal.rs | `2fff177a7ba0cabb4930251e1facc8f9be701ff3ec7baa695ce4c182fa1da35f` |
| HIR module.rs | `153a23ecaa68fd150d8bd0cc0316f3723e1cb5d98a6e3026aadef2bfd08fd907` |
| HIR local_source.rs | `3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786` |
| HIR source_identity.rs | `7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3` |
| solver candidate_source.rs | `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c` |
| playground lib.rs | `bdf996d0264e252e345c05bc77b2adcf625120281244171f0054f1d87a8d1e1b` |
| playground main.rs | `75b38435f4634ee35b3e14a54fb4d021b78bda834b4fd53965302a73309e0100` |

Exact full paths are rev4's listed paths. Unused inventory body hashes are not
silently proof dependencies. R96 author `/root/r96_proof`, paired-test/handoff
author `/root/r96_implementation`; R117 author `/root/r117_proof`. Contract and
central status ownership Luna; source/charter byte authors UNKNOWN. Reading
prior artifacts supplies no new review or coauthorship. R96's original
preparation/outcome assumptions remain assumptions here, not fresh observations.

Actual runtime identity `/root/r118_proof_lane`; current-session rev3 grant was
acknowledged before work, writes paused at Luna's command-wording seam with no
outputs created, and the same session accepted rev4 after CLEAN delta review.
No cap reset: Luna charged100sec at reconciliation `10:04:55 UTC`, leaving500
of the original600sec. First clock `2026-10-19 10:03:22 UTC`; resume clock
`10:05:17 UTC`. Final accounting/hash receipt is in the handoff. Pre-clock and
pause interval remain charged. Exact CPU/memory and launch-start duration UNKNOWN.
Requested Sol/high; requested concrete model version UNKNOWN; observed model/
effort UNKNOWN/UNKNOWN. Static listed-input cat/sed/rg/sha256sum reads only;
no compiler/test/build/CLI/probe/formatter/Git, source/test/question edits,
external contact or delegation. Exactly this note and assigned inbox are new;
no scratch/generated paths or descendants. **Freeze rev1 and STOP after handoff.**


Luna rev7 clarification (2026-10-19): the 30,000-transition premise above
applies only to the direct Machine test. The protected existing CLI test uses
10,000 steps and asserts diagnostic containment, not a stable prefix. No CLI
completion is claimed until its separate one-shot test observation. This
clarification changes no source/runtime derivation or parent premise.
