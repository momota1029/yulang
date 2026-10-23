# Concrete callback permission: source/runtime obstruction

Assignment: `CALLBACK-PERMISSION-BRIDGE-20261024`, revision 1.
Author: `/root/callback_permission_prover`; no contributing descendants.
Status: unreviewed source-native evidence and provisional implementation TODO.
No reviewed theorem, implementation approval, production authority, or observed
compiler execution is claimed.

## Parent and bounded result

The parent is `SOURCE-SAFETY-BRIDGE`, with the original Simple-sub A/B claims,
quantifiers, accepted source domain, and native obligations unchanged. Contract
`CONCRETE-CALLBACK-PERMISSION-20261024` fixes the smaller outcome: construct the
actual annotation-to-request-to-same-Catch permission bridge for

```yu
act signal:
    our ping: () -> int
my relay(cb: () -> [signal] int) = catch cb() {
    signal::ping(), _ -> 1,
    v -> v
}
my answer = relay signal::ping
```

Approved annotation policy §§1.1–1.2 requires result `1`. The annotation grants
local handling permission; it is not a closed upper bound. Additional `write`
inflow remains outward. This is semantic authority, not an execution result.

**Actual result: the current runtime has no constructor for this nested
callback-result permission.** The source and candidate retain its exact
negative `[Result]` origin. `RootCompSchema::original_parameter` rejects this
formal because its outer `annotation.ty.effects` is `None`. Runtime Value
entry therefore creates no receiver boundary, and callback application opens
no corresponding execution view. The matching Catch requires such a positive
grant. The primitive certificate also rejects this program's Lambda. These
are identified missing source/runtime transitions, not an absence-of-protection
proof or a source-qualified unsoundness counterexample.

`NO_SAFE_CODE_SLICE`: no safe runtime patch follows from this obstruction
under the current lease. A proof-supported constructor/consumer for the
callback-result permission must first enclose the request-producing
`OperationResultConsumer`, and the frozen result needs fresh independent
review. The TODO below is provisional evidence for Luna's next contract seam;
it does not enable dependent code writes now.

The parent application is concrete: the earlier broad callback gap is reduced
to runtime program schema formation, Value-entry receiving evidence, and a
complete callback-result execution view through the result consumer. No missing
negative-concrete producer was found in the inspected HIR/candidate owners.
This does not establish whole-program candidate acceptance or a general
propagation theorem. The parent remains OPEN_REVIEW; independent F1/FK1 and
foreign-continuation quantifiers receive no discharge from this local trace.

## Source identities and actual constructors

Use symbolic identities bound to their real source constructors; no numeric IDs
were fabricated by parsing or executing a sample. Let `R` be relay's original
`SourceRootId::Definition`, `p` its `HirParameterId`, `L` the retained Lambda
occurrence, `A` the formal annotation position, `S` the `[signal]` row position,
and `E` the resolved nullary `SourceEffectId` for signal. The Lambda occurrence
`L`, annotation position `A`, and row position `S` are different coordinates.

| Step | Actual owner and evidence |
| --- | --- |
| Formal and annotation | `local_source.rs:1158–1184` retains `p`, original formal source, scope and parsed annotation in `LocalSourceForm::Lambda`. `parse_annotation_with_marker`, `source_annotation.rs:449–472`, retains owner `R` and annotation position `A`. |
| Nested type and row | `parse_type_source`, `source_annotation.rs:496–599`, returns outer `Function { argument: Unit, result: Int }` with outer effects `None` and result effects `Some(row)`. `parse_row:630–693` retains `S`, resolves signal through the effect namespace to `E`, and retains zero symbolic variables for this concrete row. |
| Operation identity | `SourceEffectId` and `SourceOperationId`, `source_annotation.rs:33–52`, distinguish resolved family and operation declaration. `local_source.rs::resolve_operation:2282–2294` resolves the same unique family namespace before the member; permission is not granted from spelling. This case has no family type arguments. |
| Candidate action | `candidate_source.rs:1274–1330` joins `p` to its allocated parameter position `k` and emits `FormalAnnotation { annotation, parameter:k, occurrence:L, scope }`. Outer effects are absent, so it does not emit the separate `FormalEntry` for this formal. |
| Negative concrete permission | `candidate_formal_annotation`, `candidate_effect.rs:1633–1694`, begins with negative polarity at the formal's actual level. Function argument polarity reverses and result polarity is retained at `1438–1486`. Thus the concrete row produces `FormalPermission(k,L,R,scope,[Result],S,[E])` at `1498–1530`. |
| Open inflow and constraints | The same negative concrete branch allocates a fresh live effect port and returns both polar views of that port. It does not impose `[signal]` as a closed bound. `candidate_formal_annotation:1672–1694` admits the two value links, retains the negative formal domain, and publishes the permission only after the normal construction succeeds. No alternative inference rule is introduced here. |
| Captured port projection | `shadow_apply.rs::CandidateGraphExport::formal_effect_permissions:2636–2698` filters the definition owner, follows the retained negative formal root, and selects Function `children[2]` for terminal Result. It requires an actual Effect Row. Export retains `L,S,[Result],[E]` and the open row, or fails the whole projection on mismatch. This is a captured static port, not a runtime receipt. |

The public projection's output has occurrence/row/path/permitted/open-tail
fields; it does not by itself construct runtime arrival, provider, request,
consumer, or handler-owner evidence. `FormalPermission` explicitly documents
this distinction at `candidate_effect.rs:232–246`. The source formal still
retains the information needed for a bounded runtime constructor; no solver
write is requested by this result.

## Actual runtime path and first missing transition

1. `program.rs:819–844` emits relay's Lambda with `parameter=p`, Value role,
   and `root_schema=None`. Role depends on outer `annotation.ty.effects`.
   `RootCompSchema::from_parameter_with_result_view` does visit Function values,
   but delegates to `original_parameter`, whose explicit outer-effects guard
   (`receiving.rs:44–59`) returns `None`. It does not inspect `result.effects`.
   `RuntimeProgram::from_candidate_world:319–449` has no import of
   `formal_effect_permissions`; runtime evidence carries no callback permission.

2. At the actual relay invocation `r`, `Frame::Callee` allocates an inert delay
   for the supplied `signal::ping` expression, creates `r` with
   `new_invocation`, and executes Value entry (`machine.rs:1162–1309`). The
   operation value is constructed by `Instruction::Operation:928–953` through
   `data:2589–2603`, which gives it an opaque view `v` with no image boundary.
   `Frame::ValueEntry:1382–1415` binds `p` to that value/view unchanged. It
   supplies neither a callback schema nor a receiving boundary owned by `r`.
   **This schema/entry cut is the first missing runtime premise.**

3. Evaluating the body Catch installs `h` with owner `Invocation(r)` at
   `machine.rs:954–982`. The `cb` read is a Value observation. `consume:2372–2401`
   creates a genuine receipt `(r,v,None)` and returns the same received value.
   That receipt cannot manufacture the absent permission boundary. An Execute
   read would require a Computation interface and is not a repair for this
   approved Value formal.

4. Applying that operation at the actual `cb()` occurrence `a` uses the
   operation arm of `Frame::Callee:1310–1368`. The delayed argument is `()`;
   `direct_formal_root:1931–1943` cannot supply a root from it. More generally,
   that helper recognizes only an Execute read of a Computation formal, not
   the callee's callback-result path. Callee processing never opens an
   `ExecutionView` for the received callback value `v` and its Result effect.

5. The operation call creates its own invocation `r_ping`. Stack order is
   `OperationResultConsumer`, then `ReceiverReturn`, then `OperationPayload`.
   Payload completion creates an inert Request carrier at
   `make_request_carrier:2264–2278`. `ReceiverReturn:1370–1380` then retires
   `r_ping` and restores relay owner `r`. **Only afterward**
   `OperationResultConsumer:1130` executes that carrier. Thus wrapping only the
   callee invocation would end too soon for this concrete operation callback.
   Callback call site `a`, provider source, `r_ping`, and handler owner `r`
   must remain distinct identities.

6. `execute_with_substitution:2454–2485` mints event `q` and authenticates its
   observations from the currently executing views. No callback-result view
   was opened by steps 1–5. In this isolated program no RootComp execution
   supplies an alternative positive boundary. Request bubbling retains the
   same `q` and observations rather than creating a new event.

7. When propagation reaches the installed relay Catch,
   `validate_handler_installation:1969–1982` authenticates active owner `r`.
   `propagate_request:2010–2047` compares the full resolved operation ID against
   the arm, then requires the primitive certificate or
   `Receiving::local_grant(observations,q,Invocation(r),invocations,E)`.
   `primitive.rs::closed_primitive:31–38` returns false for every retained
   Lambda, including relay. `local_grant:264–353` requires an active receiver,
   an actual receiver boundary, a matching concrete family in its schema,
   an authentic same-event execution observation, a genuine candidate-owner
   receipt of that same view, and image reachability. The missing boundary
   already defeats the query for `r`; a receipt alone cannot repair it.

8. On this missing evidence the matching-arm branch returns `HandlerEvidence`;
   it does not prove nonprotection or forward under a negative certificate.
   If a genuine matching grant existed, the following primitive payload and
   arm checks would permit the wildcard continuation arm to evaluate its
   integer `1` (`machine.rs:2048–2132`). This last statement describes the
   existing consumer after its missing input; it is not a completed bridge or
   an observed result.

## Minimal provisional implementation TODO for Luna

`CB-PERMISSION-TRANSPORT-1` — parent `SOURCE-SAFETY-BRIDGE`, bounded callback
outcome only. Inputs are this frozen source trace, policy §§1.1–1.2, and fresh
independent review. Proposed output is a reviewed bounded runtime transport
through the three already leased runtime files. This is an evidence request,
not authority to edit and not a selected new representation.

- **Program producer:** retain/authenticate `(R,p,L,A,S,[Result],[E])` from
  the actual annotated Lambda, without changing its Value role. A grant may
  not come from type compatibility, a static family name, or another formal.
- **Receiving entry:** the actual entry at `r` must create a permission-bearing
  callback receiving view of this supplied value, with receiver `r` and its
  original formal/source coordinates. Preserve inherited unknown coverage.
- **Execution producer:** the actual invocation at `a` must open the Result
  effect view of this received callback and keep it live through the result
  consumer that emits `q`. The route must authenticate the same received
  view/port and event. Preserve distinct invocation and handler owners.
- **Grant consumer:** the same Catch owned by `r` must consume the authenticated
  concrete permission and matching resolved operation family through that
  route. Existing event/receipt/activity checks must survive. Missing positive
  evidence continues to provide no negative protection certificate.

Exact falsifiers: a sibling relay invocation's boundary/receipt grants this
request; a different received view of the same raw callback grants it; the view
ends at `ReceiverReturn` before `OperationResultConsumer` emits `q`; a foreign
handler owner consumes `r`'s grant; type equality or the name signal replaces
the formal/occurrence route; a `write` request receives signal permission; or
the annotation introduces/removes inflow independently of ordinary constraints.

`CB-PERMISSION-REVIEW-1` — Luna owns reviewer assignment and adjudication of this
frozen result. No producer/coauthor independently certifies it. If implementing
the requirements needs another producer or write path, return to Luna for a
versioned contract before any such write. There is no in-envelope producer
successor after this obstruction/freeze stop condition.

## Prior work, proof limits, and omissions

The pinned prior audit correctly identified a nested-formal/runtime-root gap;
this inspection supplies its exact first guard and complete operation consumer
ordering at current bytes. That audit's older source-annotation and
candidate-source hashes are not reused as current evidence; current approved
read-only observations below replace them. Its author is
`/root/source_permission_review`, transcribed by Luna `/root`.

Policy §3's reviewed typed transport and owner/lifetime results remain usable
once real source-owned correspondences exist. They do not generate the missing
callback schema or view. The operational manuscript's decorated-plan Path
requires matching intermediate view **and port**, plus the same event and
handler owner (`531–692`); its supplied plan is not proof of current compiler
emission. The source manuscript's §15 `W-Eligible` remains an unadopted
candidate and is not used to repair this runtime. All three manuscripts list
their author as the originating session's primary agent, with sole construction
and self-inspection; this assignment supplies no independent certification.
The dot-selection manuscript is a neighboring pinned input, not needed to infer
this direct callback's permission. Historical raw-resume receiver renaming and
wildcard bypasses remain rejected within their documented premises.

Not established: general source/native coverage; original A/B; F1/FK1;
FIRST-RESULT-ADEQUACY; arbitrary callback syntax/aliases/structural paths;
wildcard or scoped release; computation-form thunk; foreign continuation
composition; polymorphic operation instances; inference soundness/principality;
actual solver acceptance of the whole example; VM/native execution equivalence;
or an executed result/residual check. In particular, retained open inflow and
family-specific grants are compatible with the `write` requirement, but this
packet does not prove its full static or dynamic end-to-end implementation.
No production code or ordinary Simple-sub generation, accumulation,
propagation, levels, extrusion, qualifying intrusion or generalization changed.

## Frozen inputs and runtime receipt

Baseline supplied by Luna: `5fbc2c2d9e3ab28032caf599ca024b8ba8b19778`;
not independently queried through Git. The initial eleven hashes matched the
contract. Luna explicitly acknowledged the four additional read-only local
owners after dispatcher consultation; no write lease or semantic expansion.

| Dependency | SHA-256 |
| --- | --- |
| `tasks/agent-loop/sprints/concrete-callback-permission-20261024.md` | `4a6b3a6e10d3c496640c015104d555c115e351dd41806f45c04fe6e20fa24f94` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |
| `docs/yulang-source-type-safety-ja.tex` | `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166` |
| `docs/yulang-operational-type-safety-ja.tex` | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |
| `docs/yulang-dot-selection-safety-ja.tex` | `47b7fcec1f501e7c326ab9859885e329aab2730066806ea79212e825ebb32b0b` |
| `notes/theory/2026-10-24-permission-implementation-bridge.md` | `f9c40e49dd8c4e9ec1c4ef01a0391940ad5c7fd21b27da1c0635501721b6aeed` |
| `crates/yu-solver/src/candidate_effect.rs` | `70c42056a1041d54f88f16d7712875e3acf9ef7649b99a34bc990ff19f04936f` |
| `crates/yu-solver/src/shadow_apply.rs` | `f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d` |
| `tools/inference-playground/src/runtime/program.rs` | `df58f9a1d60e39fafe6d85b1e50331b35fde2a9142a2eaea84ad028d3048fdb0` |
| `tools/inference-playground/src/runtime/receiving.rs` | `2170a3bcbc6710ce3fbf721a05129117f8266b9ecf21c67136db918815303551` |
| `tools/inference-playground/src/runtime/machine.rs` | `d993905eacc0c22f4f371a7a97cf3f3d4a48434fe1538976fba0739107e8f647` |
| `crates/yu-hir/src/module/source_annotation.rs` | `409ce491bc216c6963bf76d20810790aa2756edf260ecc35e76d5cfc05d24b3f` |
| `crates/yu-hir/src/module/local_source.rs` | `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1` |
| `crates/yu-solver/src/candidate_source.rs` | `57b119592a6a8d4afd42aca10c5e2bb749cfdf0fb0fdea967dd437d552a1a04e` |
| `tools/inference-playground/src/runtime/primitive.rs` | `eb0a53bfec8ce2854adbe6342c984d5140fd1585d91da5a8a9739d2ac96e8a85` |

Actual worker `/root/callback_permission_prover`; numeric session UNKNOWN.
Requested Sol/high; observed model/effort UNKNOWN. Launch receipt was sent
before any inspection, acknowledged by Luna, then active inspection began;
first instrumented timestamp `2026-10-23 23:45:43 UTC`. Final elapsed receipt
and this artifact's byte hash are in the single assigned inbox. Checks are
source inspection and SHA-256 matching only; zero tests, builds, runtime probes,
Git operations, descendants, or external contacts. Resource cap 1200 active
seconds; no heavy process. Only this artifact and the assigned inbox are new;
no scratch paths. At submission both outputs are frozen and writing has ceased.
