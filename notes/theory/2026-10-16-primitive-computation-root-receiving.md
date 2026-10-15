# Explicit primitive computation roots: uniform receiving construction

Date: 2026-10-16
Status: independently reviewed primitive-uniform source theorem and actual
matcher correspondence; local implementation verified, global parents OPEN.
Baseline: `ddda9bc67`; exclusive write lease: this note only.
Review: `checked_result_semantics`, pre-write mathematical/source CLEAN at
producer SHA-256 `5762f347035b021e7812501b5e4d57c07f7e0941b0c4d51f44c9c7b5eb1b35d0`;
the same independent reviewer accepts the actual implementation/test delta.
The primary adopts only this bounded handoff. Implementation and verification
are recorded in section8 and the linked gate; no global MODEL or eligibility closure.

## 1. Frozen statement, original binders and exclusions

Let A range over the four already supported rigid source ground value
constructors Unit, Int, Bool and Str. Fix authentic original Lambda L, formal t,
outer annotation a=`[S]A`, its original annotation/effect-row positions and
resolved declarations, original registered entry endpoints, and one shared
assignment xi=(nu,K,D). E is the actual open incoming computation effect;
S is the annotation's resolved concrete permission set, not an effect cap or
an assertion of actual inflow. Retain its symbolic variables/dependencies.
Assume the same compatible source typing, ordinary operation/response/arm
OpCompat and source-to-runtime transition premises as the independently
reviewed [receiving theorem](2026-10-15-runtime-receiving-view-construction.md)
§§1–3 and its actual bridge §§8–10. Raw continuation uses retain the reviewed
[template correspondence](2026-10-16-runtime-resume-template-correspondence.md)
§§10–12's current-configuration, typing and view premises. Neither raw HIR
formation nor runtime success proves those independent source premises.
Governing role/schedule clauses are [charter §21](../design/2026-09-29-scc-intrusion-redesign-charter.md),
[source scheduling §§1–2](../design/2026-10-02-source-call-scheduling-choice.md),
and [typed source-owner §§2–4,6](../design/2026-10-02-typed-source-owner-realization.md).
The [typed core §§2–3,6](../design/2026-10-02-typed-computation-core-elaboration.md)
provides the existing Comp/Value entry and designated-consumer construction;
its independent source-elaboration premises are retained.

Quantify over arbitrary actual argument code, finite current-runtime execution
prefixes, any finite chain of the existing whole resolved formal-Name forwarding
constructors, and every currently admitted repeated raw-template use/recapture.
There is no chain-length/termination requirement. Unknown inherited profile
coverage remains unknown. This is the original positive local RootComp theorem
with ground A made explicit, not complete inherited-profile inference.

Required conclusion: the source entry derives Protect(RootComp) and exactly
its source-permitted local grants; authentic entry/read/execution/Observe
construct the original same-view path and local Grant without an empty-profile
premise; forwarding and template reuse retain original boundaries/receipts and
current owner control; normal completion projects the consumed computation root
to no latent effect position of A. No A-specific extra proof premise is needed.
The one source-supported implementation change is the schema's ground matcher.

Excluded unchanged parents: Function or symbolic/unknown result shapes,
general adapters/wrappers/alias profile completeness, arbitrary new operation
ports, native residual adequacy, full source typing/soundness/principality,
general negative visibility and full-domain Resume. Existing unsupported cases
remain unavailable rather than unprotected. This theorem changes none of their
source quantifiers or acceptance policy.

## 2. Source-derived schema, independent of the primitive tag

The [reviewed root producer](2026-10-15-root-computation-profile-source-construction.md)
§§2–4 uses these source operands: original formal/annotation ownership, outer
Computation role and its one exposed RootComp position, original row position,
resolved concrete families, registered entry endpoint and original receiver.
Its application of the receiving default and contravariant annotation rule
never inspects the Int tag of the ground result. Apply the same derivation to
any A in §1:

```text
OriginalFormal(L,t,a); a = outer [S]A at original row position p
Role(t)=Computation(E,A); EntryAE(t)=e_t
----------------------------------------------------------------
RootCompSchema(L,t,a,p,e_t;xi):
  Protect(RootComp); Permit(RootComp)=concrete(S)
```

The independent policy owners are
[receiver-relative protection](../design/2026-10-15-callback-identity-forwarding.md),
“Direct clarification: protection relative to the receiving boundary”, and
[annotation integration](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–1.2. Those rules concern the annotated receiving effect position. Neither
adds an effect occurrence, closes E, grants a symbolic variable as a concrete
family, or performs handling. The ground tag supplies no extra effect position.
This is an instance of the existing policy, not a proposed profile schema for
Function leaves or an inferred directional seed.

Authentic source formation already distinguishes all four tags:
`SourceAnnotationValue` at `module/source_annotation.rs:85–97` has four
nullary ground variants and separate Variable/Function constructors. Parsing
retains outer effects separately (`:415–440,503–520`); Unit's `()` is a ground
type, not an omitted annotation. Thus `[S]()` has the same explicit outer
computation role as `[S]int`, `[S]bool`, `[S]str`. No shape inversion or
identifier-specific runtime dispatch is needed.

At actual retained entry u, the original whole argument carrier T is inert.
The existing source boundary introduction gives, under that same xi,

```text
b_u = fresh(u,t,RootCompSchema,original endpoints)
chi(V_u) = inherited_root_image(T) union {(RootComp,b_u)}
Receive(u,t,V_u,Id)
```

The local singleton is authentic even if T's inherited image is incomplete.
Consequently a same-view observation of q, a genuine candidate-owner receipt,
a matching currently live Catch owned by u, live original u, and permission
for q's resolved family establish Grant. The independently reviewed receiving
§3 derivation then gives the selected `!Protected || Grant` disjunction. No
universal incoming-profile decision is used. A different alias/event/path or
an expired original receiver cannot supply this witness.

## 3. The ground-result projection for each actual constructor

[Typed-boundary §6](../design/2026-10-02-typed-boundary-realization-draft.md)
defines matching typed-path image for the entire packet, with K unchanged,
original lineage retained, and D relocated only on matching paths. Force/result
transport removes the computation's result prefix; an emitted request observes
the computation's effect position. Consumed RootComp does not map to a result's
latent-effect path merely because its family equals some other family.

For the actual four ground constructors the complete case analysis is:

| Source result A | Actual ground constructor | Latent effect positions of its value signature |
| --- | --- | --- |
| Unit | Unit / implicit Unit, `RuntimeValueKind::Unit` | none |
| Int | Integer, `RuntimeValueKind::Integer` | none |
| Bool | Boolean, `RuntimeValueKind::Boolean` | none |
| Str | String, `RuntimeValueKind::String` | none |

The independently reviewed [primitive source theorem §2](2026-10-16-runtime-primitive-event-visibility.md)
also establishes this existing leaf-shape fact for all four constructors. Only
that fact is consumed here, not its closed-universe negative-certificate result.
Each is a rigid leaf; it contains no Function, thunk, nested computation or
child signature from which a latent effect path can be generated. String's
owned text storage creates no callable interface. Therefore for every b,
`M_result*(chi)(latent,b)` has no incidence from the consumed RootComp for all
four cases. This is the structural reason for the existing Int projection;
no arithmetic property of Int occurred in its proof. The earlier finite adapter
kernel's illustrative three-atom grammar in typed-boundary §3 is not a language
exclusion of Str; this argument applies §6's general matching-path operation
to Str's actual existing rigid leaf, with no adapter or new equivalence rule.

The actual returned primitive's value/root paths survive with their original
value correspondence. K remains the same ledger and still-live D/lineage
remain at their actual matching source paths or in their original pending
request/residual/continuation graph. Removing a RootComp incidence from this
result view never clears another stored view, captured environment or old
receipt. The local runtime representation implements only this RootComp
projection, not the full K/D ledger; that implementation limitation is already
explicit in receiving §8.5 and is not repaired or concealed by this extension.

Projection occurs when the *whole* received computation returns A. An
intermediate operation can have response type B different from A; its
continuation/suffix may calculate A later. Resuming q with B neither ends the
RootComp early nor attaches its profile to the ground B response. The pending
RootComp delimiter remains responsible for actual whole-computation completion.
Malformed/untyped HIR returning a closure from `[S]bool` would invalidate this
source premise for Bool just as it already does for Int. Widening a schema is
not a new dynamic type checker or a proof of such HIR's soundness.

## 4. Every current runtime consumer and the one actual gap

Frozen-baseline hashes are in §7. The audit searched production Int/Integer tests and
all schema, RootCompReturn, primitive matching and template View consumers.

| Owning constructor/consumer | Actual source correspondence; dependence on A |
| --- | --- |
| `receiving.rs:21–36`, `RootCompSchema::from_parameter` | Checks original annotation/Lambda source-root equality, original formal source-root equality and explicit outer effects. The final tag predicate currently accepts only Int: this is the exact missing constructor for Unit/Bool/Str. Widen only that predicate to the four rigid ground variants. |
| `program.rs:375–401`, Lambda | Explicit outer effects select `ParameterRole::Computation` independently of value tag. It retains the original formal, Lambda SourceSite and schema, and original body label. This already selects Comp for all four; Value/Function/Variable roles are not inferred from runtime values. |
| `machine.rs:650–733`, Callee/closure entry | Allocates one whole Delay(code,environment), inherits only the exact direct-formal dependency, creates the actual invocation, then enters the local schema if present and binds the same inert Comp ReceivedValue. No argument prefix, primitive check or extra force depends on A. |
| `machine.rs:1171–1184`; `receiving.rs:108–126`, whole-Name forwarding | Requires the exact resolved Parameter Name instruction in Execute mode and initialized Comp binding. Delay copies its image/unknown dependency without performing the Name read. Next genuine entry adds its own distinct boundary. Neither consumer examines Int. |
| `machine.rs:1497–1526`; `receiving.rs:160–220`, Name/execution/event | Read validates same underlying value/view, creates a receipt under actual current owner, and Execute opens the exact view/receipt occurrence plus RootCompReturn delimiter. Request execution allocates a fresh event and observes all current executions. No new receipt is fabricated from a runtime primitive tag. |
| `receiving.rs:225–318`, local Grant | Joins authentic event/execution and any genuine candidate-owner receipt for the same exact view/formal route; checks current receiver activity, original boundary image and annotation concrete permission. No ground-tag read occurs. Immutable view/image lineage, unique ordered original receiver and older-parent cutoff proofs are unchanged. |
| `machine.rs:601–605`, RootCompReturn | Ends the exact execution triple and makes a ground result view for the same returned value. No Int test exists. §3 justifies this operation uniformly under the original source typing premise. It is reached by actual completion, not by the runtime shape of an intermediate result. |
| `machine.rs:930–940`, primitive matching | Already accepts exactly Unit/Int/Bool/Str with their corresponding actual tags, Value interface and same value/view. It checks operation payloads and raw response values by *their declaration type*, not the receiving root's A. |
| `machine.rs:566–588,1268–1291`, raw response/selection | ResumeArgument reads the original operation result type and calls primitive_matches; continuation selection allows all four primitive declared responses. Payload compatibility, exact operation ID, handler owner/activity, shallow removal and actual arm code remain independent checks. Widening RootComp creates no new payload/response policy. |
| `machine.rs:1359–1362,1016–1020`; `continuation.rs:View`, crossed execution | Request unwinding ends the current execution and saves its exact execution witness. Capture turns that delimiter into View(original view/receipt), not a schema entry or a primitive-specific node. |
| `machine.rs:1153–1161`, template View entry | Authenticates original view/receipt, allocates a fresh execution occurrence, appends it to current ambient executions and reinstalls exactly its RootCompReturn. It creates no new boundary or Receive, rewrites no original receiver, snapshots no store, and does not inspect A. Repeated use and recapture preserve this invariant by the same node induction. |
| Owner/frame/store routes | ReceiverReturn, OwnerReturn, CatchReturn/value binder, ValueEntry, Local/cell publication, Root/GlobalRead caching, Forward/If/Block and ExpressionReturn retain the existing whole record/typed control or intentionally discard an actual ground result. No branch tests Int to carry a root view. Ground literal construction already uses ground_data for all four. Closure/request public views remain opaque and private captures remain separate. |
| `primitive.rs:33–39,185–213`, negative certificate | A Lambda still makes the closed-primitive whole-program certificate unavailable. Its primitive ground/payload predicate already has all four tags. No negative eligibility is inferred from a missing schema, Some schema, unknown flag or matcher failure. Existing `closed_primitive || positive local_grant` selection and whole-program coverage are unchanged. |

Normal return and request/Resume routes exhaust the root delimiter consumers:
its only normal completion is §3's projection; its only request crossing saves
it for template construction, whose only entry opens a fresh execution of the
same evidence. Ordinary nested frames carry the record/control without
reinterpreting its primitive signature. Thus there is no hidden Int-sensitive
owner, response or result consumer requiring a second semantic repair.

## 5. Uniform preservation induction and limits

Instantiate the original root-entry proof at each A using §2. It supplies the
same fresh local certificate, not a transported old receiver or a desired chi
premise. Identity binding/read and exact whole-Name/Delay/entry forwarding use
the same actual maps for every A and preserve all source tags, K/D and original
receivers under xi. Ordinary instruction transitions cannot inspect A through
the root schema; their ordinary typing contracts preserve A on final return.
For each request, actual event/Observe and the same-view receipt join establish
the same positive local Grant conditions. A nonmatching operation, unavailable
coverage or expired receiver has no newly invented Grant.

For captured suffixes, structural induction on the actual flat template nodes
uses unchanged Bind, Owner and ForwardHandler clauses and §4's View clause.
The current store/cells and currently admitted response are used; original
request/event/receipt/boundary history is retained independently. Re-entry
creates a new execution occurrence, never a new receipt or receiver boundary.
On final normal return §3 proves projection; on another request the induction
repeats with a fresh event and current activity. This covers every finite legal
reuse history, including a pending/infinite computation's finite prefixes;
it claims neither termination nor reuse of every future history.

For arbitrary argument code, the fresh local boundary/receipt/Observe proof
still applies without proving its inherited profile complete. Only exact whole
formal Names get the reviewed inherited identity map. The code's unknown flag
stays unknown on all other argument routes. This is a positive local theorem,
not a general certificate for returning functions, symbolic leaves, adapters,
unknown profiles, negative visibility or arbitrary raw continuation domains.

## 6. Proof-to-code handoff and verification obligations

A primary-authorized implementation may change only
`RootCompSchema::from_parameter`'s ground predicate from Int to
`Unit | Int | Bool | Str`, preserving all authentic-owner and explicit-effects
guards and retaining the original annotation/row/formal objects. Function,
Variable, absent outer effects and ownership mismatch must still return None.
No change to RootCompReturn, primitive_matches, saved frames, template nodes,
owner decoding, view reconstruction, result forcing or Grant policy follows.
The frozen baseline did not enforce this widened constructor; section8 records
the independently reviewed implementation.

Primary-owned focused obligations (no tests added or executed here):

1. Schema formation accepts the four explicit ground Comp formals, including
   empty/concrete/symbolic outer rows, and withholds Function/Variable, absent
   effects and owner-mismatch cases. Concrete permissions remain exact; a row
   variable alone grants no concrete family.
2. Actual source entries with Unit/Bool/Str roots handle their permitted request;
   a ground normal return projects the consumed root and preserves the value.
   Reuse the admitted type spellings `()`, `bool`, `str` and actual literal forms.
3. For each newly admitted ground root, exercise continued request execution
   and whole-Name forwarding, with a multi-shot or actual value-arm completion
   control. Helper observing-owner different from candidate
   receiver, genuine local/entry receipt alternatives, repeated use and expired
   original receiver controls retain the reviewed same-view behavior.
4. Raw continuation response matching uses the operation's own already supported primitive result
   type, including a response type different from root A; subsequent whole-root
   return and repeated capture/Resume preserve current cells and old boundaries.
5. Additional unhandled families escape unchanged, missing Grant/unknown inherited
   coverage does not become negative evidence, and selected-arm effects execute
   outside the exact shallow handler. Existing closed-primitive controls remain
   unchanged; no broad negative certificate is enabled by this patch.

These are focused conformance obligations, not claims of parser/inference/full
source admission or evidence supplied by successful runtime tests. Independent
compiler-referee review of this proof is required before production widening.

## 7. Direct frozen inputs, checks and commit packet

| Input | SHA-256 |
| --- | --- |
| runtime receiving.rs | `5443c8ca55e58a37b6d003cf5b2985214d37776094f02637adfbe30200cc36bd` |
| runtime program.rs | `b9798ac4c5d93e761582d712114615defa913f858d70e91f170471c8b8912748` |
| runtime machine.rs | `04024174d88223e252e1d093eaee96c17d9f43d4d32bea5c41631017c9da208c` |
| runtime continuation.rs | `194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3` |
| runtime primitive.rs | `97485b9439357497aaf3f19555b1d87eef4aabc955b3a2815f23cf49a65c0153` |
| runtime mod.rs | `64d208743793a03501a76f56bc2b511c50ed40cff3f789757a00b7d608fc846b` |
| reviewed receiving theorem | `ae05faea870634f7cd8cceac9515537d59427c08ae74940c7da70b1f89f45e8b` |
| reviewed primitive ground-shape theorem | `7b27f8cf1d8024e249cc7d8a433c77438e3f59e5543cfc46a96a1af278eb3f56` |
| reviewed raw-template theorem | `f3a4c925a197e63e5b7faf1ce1e1caf5736d76f1b86ba162c6acc85bfff8e7dd` |
| root source construction | `d98e1a4e5d93f807d77c88dcf6138924e7a2b0bd2f9af031caa58bd7c79047c0` |
| computation forwarding | `d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79` |
| typed core §§2–3,6 | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| typed-boundary §6 | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| annotation policy | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |
| receiver-relative policy | `c544ed3c7b83686a740aa43b1db92d901de31a3b197f81f90a4c9dbdae561134` |
| charter §21 | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| source scheduling §§1–2 | `7b2d2556f4b6a93d7beb73a78f476bfea7d0f94de0c5f77649f6cd15ff69a530` |
| typed source owner | `5cbd8110736ee4d43e0c65460fa9ecf700228bfdbe9fbaa7642ea0302d86f1aa` |
| HIR module/source_annotation.rs | `b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f` |

One bounded static prover lane. Normal configured Sol/high requested; observed
runtime model/effort metadata unavailable. No children, code/shared-record edits,
Git, Cargo, tests, executable probes or measurements. Static source/access
searches, direct hashes and note whitespace/fences/local links checked. The
anticipated matcher adds constant tag alternatives, no new allocation, runtime
scan or representation growth. Cost beyond the existing receiving algorithm
is unchanged; no performance measurement is claimed.

Commit packet: sole new path
`notes/theory/2026-10-16-primitive-computation-root-receiving.md`, baseline
`ddda9bc67`; dependencies unchanged at the recorded hashes. Producer theorem
and source audit ready for independent review; production widening and original
global parents remain OPEN. Next action: primary obtains fresh independent
compiler-referee review, then leases the exact matcher change and focused tests.
Suggested checkpoint: `research: derive primitive computation-root receiving uniformly`.
Primary retains shared-record integration/adoption; no new semantic decision
or global coverage status is proposed.

## 8. Actual matcher and focused verification

The [integrated local gate](../progress/2026-10-16-playground-primitive-root-receiving.md)
implements exactly the section6 predicate in `RootCompSchema::from_parameter`.
The original annotation/formal ownership and explicit-effects guards are
unchanged. The production matcher has no new allocation, traversal or field.
All previously audited consumers remain byte-identical; only the ground tag
alternatives changed. The schema unit test is additional cfg(test) code.

Independent semantic delta review is CLEAN at receiving SHA-256
`8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9`.
Integration tests were reviewed at `ab56360e...caabc`; the final
`f82399766a012383f12e7190744c397ce10d11b9730241d6f724fa254c9d06bf`
differs only by rustfmt layout of one newly added Unit table row. Existing
test assertions and names remain unchanged.

Primary verification: 18 receiving, 13 raw-Resume and three private receiving
tests pass, without warnings; three CLI cases resume Bool/Str/Unit computations
and print `false`, `"resumed"`, `()`. Frozen §7 hashes describe the proof
baseline; the gate records current hashes and commands. No solver/workspace or
unchanged broad package suite was repeated for this M1 local coverage slice.
Full source typing, general profiles, Function/unknown roots, full-domain
Resume and production/F5 remain separate OPEN obligations.
