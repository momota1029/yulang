# CALL-NATIVE-RESPONSE-AUTHENTICITY independent review

Verdict: **CLEAN for the bounded source audit and representation obstruction**.
No blocking findings. This is neither a checked new theorem nor approval of a
syntax extension or production change. Original full source/native safety and
Call A/B parents remain OPEN, with their original quantifiers and source domain.

Reviewer: `/root/call_native_response_review_astra_r1`, fresh nonauthor and
noncontributor; assignment receipt is the primary's NEW_TASK for this identity.
Requested Astra/medium; observed model/effort UNKNOWN. Baseline supplied by
primary: `d1308e8b0612abf95f25d7adae137e9b769269db`, branch
`research/simple-sub-intrusion`; no Git commands used. Contract r1 SHA-256:
`e1e260369eb0ee55acd3bcf49759a45f56692e2cb3f9928d95d2338a0eb03f06`.

Frozen reviewed artifact:
`notes/theory/2026-10-25-call-native-response-authenticity.md`, SHA-256
`18519640506d193b75dbeef374e806b6b07e926043cfca3cada02ed43087da57`.
Frozen author handoff revision 1:
`tasks/agent-loop/inbox/20261025-call-native-response-authenticity.md`, SHA-256
`b1a67616066c1e1bcfc8df29d23f2b12b9b1c14b1f50b67c0ee107654c52dc35`.
Independent sha256sum inspection matched these pins, all eight contract direct
dependencies, and all six additional source dependencies recorded by the author.

## Source-first checks

1. Actual response entrypoints agree with the audit. `machine.rs:1006–1080`
   obtains the response type from the retained template declaration, accepts
   `primitive_matches` or the exact v1 closure case, and passes the identical
   ReceivedValue to EnterTemplate. `primitive_matches:1769` checks Value role,
   same-value view and Unit/Int/Bool/Str kind; it supplies no formal derivation.
   The v1 branch additionally checks the retained response-definition read,
   lambda root/occurrence, continuation application and Closure executable.
   `resume_host_write:599–657` accepts no caller-provided value: it validates the
   stopped request, continuation, capability/declaration, single use and string
   payload, then allocates Unit with a ground view. `lib.rs:278–326` calls it only
   for the configured host operation. `program.rs:1310–1359` authenticates the
   public export and effect-free str-to-unit signature. The three production
   EnterTemplate assignments are those two entrypoints and recursive entry.
   This inventory covers this inspected runtime, not every backend; the v1
   evidence API explicitly describes its route as research-only.
2. The retained source chain is real but is not a typing theorem. HIR
   `source_annotation.rs:330–380` builds declarations with family/declaration
   identity and parsed function signatures. `candidate_source.rs:907–946` joins
   the continuation binder, unique local response binding, matching annotation,
   lambda and callback family. `candidate_effect.rs:1120–1154` records and
   constrains the field edge before consumption; `shadow_apply.rs:2013` requires
   final errors empty. `program.rs:450` requires exact HIR ownership and one
   consumed receipt; its construction at :1120 joins the actual source labels,
   initializer and callback occurrence. Name/Closure formation and the Callee
   continuation branch in `machine.rs:831,864,1211` agree with the reported
   consumer. None interprets captured environments or a full polymorphic
   OperationInstance; declaration IDs and source occurrences cannot fill that
   gap. The report does not turn repeated activations or a same-value alternate
   view into an unestablished source-reachable counterexample.
3. `capture_template:1841–1910` creates one Hole, extends a descending chain and
   publishes only after validation. The sole production template push is here;
   no template mutation was found. `enter_template:1914–2027` carries the same
   response at each successful step and returns it at Hole. For popped frames
   f1,f2, entry pushes f2,f1 and return therefore visits f1 first. Administrative
   entry can fail; the artifact correctly does not claim replay totality.
   Nonselected handlers become saved HandlerBoundary/ForwardHandler nodes;
   selection captures before removing its own CatchReturn. Nested resume frames
   retain separate handles. These are local identity/order facts, not an
   identification with the formal captured context or arbitrary suffix proof.

## Formal and authority checks

`CoreSyntax.lean:105–191,247–280` supports the stated constructor-inversion
argument. Original.Val has no non-unit literals; Original.Ty has no callable
type. TypedCall.Value adds no closure constructor. At a closed int/bool/string
base, variable lookup contradicts emptyContext, delay has thunk type, original
reduces to Original.ValTyped with only unit producing a base, and view recurses.
This establishes the specific representational obstruction by inspection; it
does not refute source safety or exclude future faithful encodings. Unit has
the claimed local original/unit typing derivation. The boundary theorem at
`CallRequestBoundaryComposition.lean:66–96` explicitly requires the closed
response premise and retains arbitrary typed suffixes; the audit leaves both
native response encoding and source/native trace correspondence unresolved.

The proposed next literal constructor reuses existing Original.Literal and raw
Atom.literal. Governing prose :215 already assigns literals their corresponding
base type, and machine.rs:690 onward constructs native literal values. Thus the
proposal targets existing accepted syntax, not a new source behavior. Its
substitution/erasure/Call cases still require a separately scoped checked packet;
this review neither implements nor authorizes it. Callable/environment, shared
instance and template/context obligations remain separately OPEN.

Governing prose :1140–1174 explicitly allows typed external responses, typed
callback code and well-typed fresh graph extensions. The artifact preserves
that premise and correctly refuses to move internal primitive/source callable
safety into it. No source-qualified safety refutation or parent closure is
claimed. NO_SAFE_CODE_SLICE is supported by the inspected acceptance and
template owners: missing formal representation does not justify a runtime fix.

## Receipt

Three stages: frozen-input/authority inspection; independent source and formal
checks; report/freeze. Charge the full 300-active-second reservation
conservatively; no renewal. Only read/hash shell inspection and this exact report
write were performed. No tests, builds, Lean, runtime probes, Git mutations,
source repair, nested agent CLI, external contact or descendants. All inspection
shell calls completed; no active or persistent subprocess remains. Sole written
path is this leased report; all other edits preserved. Reviewer writes STOPPED
after report freeze. Primary adjudication/integration remains required.
