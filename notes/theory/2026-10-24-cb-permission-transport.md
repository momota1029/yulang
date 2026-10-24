# Callback Result permission transport and delimiter construction

Assignment `CB-PERMISSION-TRANSPORT-20261024`, revision 1.
Author `/root/callback_permission_prover`; no descendants or coauthors.
Status: **unreviewed constructive candidate for a bounded runtime delta**.
The current source/runtime gap is still present; none of the new constructors
below is claimed to exist in production. Fresh independent review belongs to
Luna. This is neither production approval nor closure of the parent theorem.

## Claim, source domain, and application

The sprint targets only the approved direct operation callback:

```yu
act signal:
    our ping: () -> int
my relay(cb: () -> [signal] int) = catch cb() {
    signal::ping(), _ -> 1,
    v -> v
}
my answer = relay signal::ping
```

Policy `2026-10-10-annotation-effect-hygiene-integration.md` §§1.1–1.2 requires
local handling and result `1`, permits open additional effect inflow, and leaves
additional `write` outward. The original Simple-sub A/B, their quantifiers and
source domain, `SOURCE-SAFETY-BRIDGE`, F1/FK1, and native coverage stay open.
No general foreign-continuation theorem is discharged by this construction.

The previous obstruction identified two missing producers: a callback receiving
boundary at Value entry and a Result execution view enclosing the operation's
request-producing result consumer. This artifact defines both producers from
the existing source coordinates and proves their bounded frame behavior. The
next unresolved premise is **implementation of these constructors and their
consumer in program/receiving/machine, followed by independent correspondence
review**. It is not another unknown source profile. No solver write or
`continuation.rs` write is required by the construction below.

## 1. Common-origin mapping to the actual FormalPermission

Let `H` be the original retained HIR module, `R` relay's definition source root,
`p` its original `HirParameterId`, `L` its Lambda occurrence, `A` the formal's
annotation position, `S` the bracket row position at structural path `[Result]`,
and `E` the resolved nullary signal family identity. These coordinates are
distinct: no equality between `L`, `A`, and `S` is assumed.

The runtime schema constructor must consume **the actual retained
LocalSourceForm::Lambda parameter**, not a reconstructed inferred type. It
retains `(H,R,p,L,A,S,[Result],[E])`, checks annotation owner and
`p.source_root()` against `R`, and follows the actual annotation's Function
result field to its row. For this outcome the source shape is outer effects
None, Unit argument, Int result, and a nonempty concrete-only negative Result
row. The constructor reads the resolved `SourceEffectId`; it never resolves a
family spelling again. This bounded matcher neither rejects ordinary inference
outside the outcome nor creates permission for another type/position.

**Mapping derivation from inspected source owners.**

1. `local_source.rs:1158–1184` retains this original formal and annotation on
   the Lambda; `source_annotation.rs:449–472` records `R,A`.
   `parse_type_source:496–599` sets outer Function effects to None and parses
   result effects separately. `parse_row:630–693` records `S` and resolves `E`.
2. `candidate_source.rs::emit_candidate_source:1043–1068` requires pointer
   equality with `H.local_source_for(R)` and authenticates owned occurrences.
   At `1100–1111` the Lambda's `p` is stored in `parameter_recipes[k]` and
   `parameters[p]=k`. At `1313–1329` the action clones this same parameter's
   annotation and emits `(k,L,scope)`; it does not infer the annotation from a
   candidate type. Definition scope is used for this top-level relay.
3. `execute_candidate_action:2423–2427` dispatches that action to
   `candidate_formal_annotation`. The negative formal constructor retains
   result polarity, visits `[Result]`, and constructs
   `FormalPermission(k,L,R,scope,[Result],S,[E])`
   (`candidate_effect.rs:1438–1530,1633–1694`). It creates an open shared row,
   rather than a closed `[E]` upper bound. The source annotation coordinate `A`
   is not a field of FormalPermission; it is authenticated at the original
   HIR-formal join, not invented inside that solver record.
4. `CandidateInference::observes_hir`, `shadow_apply.rs:2006–2008`, checks
   pointer identity against retained HIRs. `RuntimeProgram::from_candidate_world`
   checks that relationship for its modules (`program.rs:326–330`) and lowers
   their original LocalSource Lambdas (`570–574,760–844`). Thus the proposed
   schema and the actual candidate constructor have the same input object and
   positional path. Cloning those original source IDs preserves this mapping.
5. The existing public static projection also reaches the same negative
   captured Function `children[2]` effect row and retains `L,S,[Result],[E]`
   (`shadow_apply.rs:2636–2698`). The runtime need not import its open-tail
   readback to discover source authority: the common-origin mapping above
   supplies that identity. Type equality is never the join.

This establishes a construction correspondence for this source schema when its
candidate annotation action succeeds. It does not assert that the whole sample
has been accepted by the current solver, or that `from_hir` alone proves a
typing theorem. Candidate failure/rollback cannot be advertised as a successful
FormalPermission publication. The runtime schema's authority is the approved
explicit source annotation, not an inferred permission from a green solver.

## 2. Defined runtime delta, confined to three owners

Keep RootComp schemas and their receiver-sorted boundary/image arrays intact.
Add a **separate immutable callback entry/use table** in `receiving.rs`.
This separation preserves the typed port distinction; it is not a new language
policy. A Value entry can occur after argument evaluation, so adding its older
receiver to the existing receiver-sorted RootComp vector would require another
ordering argument. The construction does not assume that ordering.

The table has two constructor-owned record forms:

```text
Entry c = (schema σ, original receiver r, supplied value f,
           incoming view v0, fresh receiving view v, formal receipt ρp)
Use   u = (entry c, source receiving view v, actual Apply site a,
           fresh Result-effect view w, actual-use receipt ρa)
```

Every view handle and receipt is allocated in the existing Receiving arenas.
`v` and `w` have underlying value `f`, preserve inherited unknown coverage and
existing image storage, and do not reinterpret inherited images as new
callback paths. `w`'s callback port is permanently `[Result]`; the entry's `v`
is not itself an executing effect port. The source route is explicitly
`(v,[Result]) -> (w,call.result.effect)` for actual Apply `a`.
The tables are immutable after publication. Store exact handles, never raw
value equality as a replacement for a view identity.

**Entry transition.** `program.rs` retains the source schema in its actual
Lambda, still Value role. `machine.rs` carries it through closure creation and
the pending ValueEntry frame. After ordinary Value argument evaluation has
produced `f,v0`, that actual ValueEntry allocates `c,v` and genuine receipt
`ρp=(Invocation(r),v,L,Some(p))`, then binds the original `p` to `f,v`.
It does not force the callback, create an event, change inflow, or open an
execution view. One actual entry creates one record. An ordinary unannotated
Value entry creates none.

**Actual use transition.** The `cb` read has the existing genuine receiving
receipt. When `Frame::Callee` actually selects the operation value held under
that received view, validate the callback entry, value/view match, and actual
source Apply site `a`. Allocate fresh `w`, the immutable route/use `u`, and a
genuine call-use receipt `ρa=(current owner,w,a,None)` as part of this real
source use. This occurs **before** the operation branch calls `new_invocation`,
so its current owner is relay `r`, not the operation's new invocation `i`.
It is not a receipt created by a grant query. Retain `u` in this
call's `OperationResultConsumer` frame. It stays dormant through argument
preparation; no execution occurrence exists yet. This rule applies by the
formal/view relationship and resolved declaration, not a special ping identity.
Calls without this source-owned callback entry retain their existing behavior.

**Consumer transition.** The operation call's existing invocation `i` prepares
the Unit payload and returns an inert Request carrier. `ReceiverReturn` retires
`i` and restores the caller owner. Only when its retained
`OperationResultConsumer { source:a, callback_use:u }` executes:

1. validate the exact immutable `u,w,ρa` and carrier/source use;
2. call `Receiving::execution(w,ρa)` to allocate fresh execution occurrence `x`;
3. push `x` onto `executing_views` and `RootCompReturn { execution:x }` onto
   the frame stack;
4. execute the actual returned carrier through the existing consumer.

Despite its historical name, RootCompReturn's inspected code is an execution
delimiter: it checks the returned value against **its own returned view**, ends
the exact execution occurrence, and preserves the returned ReceivedValue. It
does not require the result value to equal the callback underlying value.
No new frame or TemplateNode variant is needed. The callback use in the
pending consumer is ordinary cloned Frame data.

`Receiving::execution` validates callback effect views against their immutable
use receipt and selected Result port. Entry-only views cannot be executed as
effect views. `TemplateNode::View` can therefore reopen `w,ρa` using the same
existing API; its port is obtained from immutable view/use metadata, not from
the current owner or the raw value. Existing RootComp execution remains its
own distinct kind. These checks are required new Receiving consumers, not
properties claimed of the unchanged implementation.

## 3. Concrete positive-grant consumer and separation

Extend `Receiving::local_grant` with a callback branch. A callback grant holds
exactly when an observation of this same request `q` has authentic execution
`x=(w,ρa,occurrence)`, immutable use `u` joins that exact `w` to original entry
`c`, `c.schema` is the source schema above, the candidate Catch owner equals
`Invocation(c.receiver)`, that original receiver is active, the genuine actual
use receipt has that same owner/view, and the schema's resolved concrete family
set contains the request family. Preserve the existing matching resolved
operation-ID and active installation checks at the Catch.

Callback Result observations are **excluded from the RootComp branch**, even
if their stored inherited image happens to contain a RootComp boundary. They
cannot satisfy a root computation query or lend authority to argument force.
Conversely a RootComp execution is not a callback Result use. Query failure
remains failure to supply positive evidence; it is no negative protection
certificate and does not enable missing-grant forwarding.

For the target, `owner(h)=r`, `ρa.owner=r`, entry receiver is `r`, and request
family is `E`. The operation's retired invocation `i` is distinct from all of
these. Apply site `a` is a source occurrence, not an invocation ID. Equal type
rows, another received view of raw callback `f`, a sibling relay's entry, an
unrelated observation or a foreign Catch owner cannot satisfy this conjunction.
Another actual call through the same formal constructs its own `w` and use;
its own event may legitimately use the same annotation, but its observation
cannot be substituted for this event's observation.

## 4. Frame invariant and proof over finite transitions

At every successful small-step boundary maintain:

**F.** The bottom-to-top projection of live `RootCompReturn` execution delimiters
in `frames` equals `executing_views`, including exact occurrence IDs. Dormant
consumer uses and saved suffix/template nodes contribute no live occurrence.

**H.** All entry/use/view/receipt records are immutable historical evidence.
Each execution occurrence authenticates its own exact view/receipt. Observation
packets keep their original event/occurrence; closing a live delimiter does not
erase past execution authenticity.

**P.** A callback occurrence is opened only by its actual Result consumer or
re-entry of an already captured View node. Its selected port remains Result.
No argument preparation, Name observation, raw value lookup or grant query
opens it. A true callback grant always joins the same `q,w,u,c` and currently
active original candidate owner.

The empty initial state satisfies F/H/P. The following cases exhaust the
relevant constructors/consumers; ordinary frames preserve the projection.

| Transition | Preservation argument from actual machinery and defined delta |
| --- | --- |
| Formal Value entry and call selection | Allocate source evidence and dormant use only. Frames contain no new delimiter, executing_views is unchanged; F holds. Typed identities/port are fixed at constructors, giving H/P. |
| Argument preparation and operation receiver return | The use remains dormant in OperationResultConsumer below ReceiverReturn/OperationPayload. Any argument request observes no new callback occurrence. ReceiverReturn changes execution owner but not the historical entry/use or delimiter projection. |
| Result consumer opens | Allocate one fresh authentic occurrence, then append it and its delimiter together. The callback consumer runs after `i` retires; F/H/P hold without identifying `i` with relay `r`. |
| Request creation | `execute_with_substitution:2454–2485` mints fresh `q` once and `observe` records all authentic currently executing occurrences, including `x`. It changes no frame/view projection. Thus q has the exact w/use observation before any unwind. |
| Normal result | `return_value:1076–1085` pops the delimiter and `end_execution_view:1945–1955` requires the exact last view/receipt/occurrence before popping. Returned data retains its own actual view; callback permission is not attached to a future result. |
| Request bubbles across delimiter | `propagate_request:2180–2184` pops the delimiter, closes the exact x, and appends the already-closed frame to request.suffix. F holds; q and its immutable observations are unchanged. H lets the later query authenticate x even though it is no longer live. |
| Query at relay Catch | After that delimiter unwind the original relay Catch is exposed and r is still live. `validate_handler_installation` authenticates it. The callback conjunction above holds for q,w,u,c,r,E, so the existing ordered primitive payload/arm checks select its arm. No view needs to remain live during the query. |
| Nonmatching arm and further bubbling | Operation-ID mismatch skips that arm without consuming q. Popping other ordinary/receiver/handler frames retains the same q and observations; receiver retirement changes activity only. An expired original r can no longer authorize a later foreign handler. |
| Matching arm discards continuation | `propagate_request:2086–2095` removes the Catch after ordered checks and calls abandon_suffix for the wildcard continuation. The suffix's view delimiters were already closed during bubbling; abandon_suffix never closes them again. No dormant consumer is run, no view is reopened, and the arm runs outside this Catch and the closed callback view. |
| Capture of a popped view | `capture_template:1776–1779` converts the saved closed RootCompReturn to `TemplateNode::View { original:x }`, not a live Bind frame. It stores original w/receipt; no activity or receiver rewrite occurs. A still-dormant consumer captured during argument preparation is ordinary immutable Frame data, still unopened. |
| Replay of captured view | `enter_template:1913–1920` allocates fresh execution occurrence x' for original w/ρa, appends x' and its new delimiter together, then enters inner nodes. It does not replay original q: Hole supplies the response. Later newly executed requests get fresh event IDs and observations. Each replay has its own occurrence, so one delimiter cannot close another replay's live occurrence. |
| Replay owner resolution | Owner nodes may borrow a still-live owner or allocate a fresh execution owner (`1857–1890`); ForwardHandler resolves its current installation owner. They never rename c.receiver, w, ρa or u. If original r is dead, a fresh owner r' does not acquire r's permission. If r is still active, the same-owner conjunction must still hold; no automatic grant follows just from replay. |
| Pause, terminal evidence failure, or unsupported materialization | No completion is fabricated. A preserved live prefix retains its delimiters; a saved popped suffix has closed ones. Global/cache frames rejected by capture_template remain an explicit unsupported materialization case, not silently replayed. New constructors validate before publishing usable evidence or stop the private runtime safely. |

The normal/unwind cases use exactly the LIFO equality in end_execution_view.
Template construction iterates the inner-to-outer saved suffix and wraps its
root, so template entry reinstalls outer frames/views before their inner
continuation. The appended containing Owner node supplies current execution
control without altering original receiving evidence. Induction over this
finite transition list proves F/H/P for the proposed bounded extension.

In the concrete target, opening at the Result consumer gives stack suffix
`Catch(h,r) ; RootCompReturn(x)` and executing suffix `x`. Request emission
records `(q,w,x)`. Bubbling removes/closes x, leaving Catch(h,r) and unchanged
q observations; the callback grant holds. Wildcard continuation selection
discards the closed suffix and evaluates integer `1`. This is a constructive
derivation for the defined delta, **not an execution of current source code**.

## 5. Open inflow, residual write, scope, and falsifiers

No transition edits candidate constraints, levels, extrusion, qualifying
intrusion, propagation or generalization. The existing negative concrete
constructor keeps its open shared row; the schema introduces no new inflow.
The callback grant checks resolved membership in `[E]` on the actual request.
A request from an additional `write` family cannot satisfy this signal grant.
The signal Catch's operation ID mismatches write, so it bubbles that same write
event outward rather than consuming it. Closing a callback delimiter changes
neither request family/payload nor the returned value's view. This establishes
the runtime nonconsumption obligation for write in the defined construction;
the compiler's full static inflow/residual theorem is still not established.

The frame invariant handles the listed lifecycle transitions. It does not
assert a complete grant/forwarding decision for foreign continuations or prove
that replay under a fresh owner must return 1. Inactive historical receivers
remain inactive. General aliases/structural paths, arbitrary closures, operation
type arguments, thunk form, wildcard, release and global W-Eligible are outside
this bounded outcome. This uses the approved concrete permission, not adoption
of the source manuscript's unreviewed global candidate.

Exact falsifiers for implementation review:

- Source schema is reconstructed from equal types/names, loses A/S/L/p, or has
  no common-origin mapping to the original FormalAnnotation action.
- A callback Result view satisfies any RootComp query, or entry v is executed
  as if it were a Result-effect view w.
- An argument request observes the dormant callback use, or the view closes
  at the operation receiver return before its consumer emits q.
- Grant joins another event, use/view, formal, entry receiver or foreign owner.
- Bubbling mutates q's observations, discard double-closes/reopens a view, or
  replay reuses an old live execution occurrence instead of a fresh one.
- Replay renames historical boundary receivers/receipts or treats fresh current
  owner r' as the original r.
- Signal permission consumes write, closes its input row, or manufactures an
  effect contribution solely from the annotation.

## 6. Evidence, dependencies, resources, and handoff

Reused: the reviewed obstruction's exact HIR/candidate producer trace and
operation-consumer ordering, by the same author; that result's independent
review was supplied by Luna. The existing RootComp delimiter, immutable template
nodes and owner resolution were inspected directly here and applied only in
the cases proved above. Historical uniform receiver renaming and wildcard
bypasses remain rejected. Manuscript decorated-plan lemmas provide a port/view
discipline, not evidence that these new constructors already exist.

All owners below were hash-checked in this assignment. Source-code authorship
was not queried through Git and remains UNKNOWN; this artifact has one author.

| Input | SHA-256 |
| --- | --- |
| `tasks/agent-loop/sprints/cb-permission-transport-20261024.md` | `e3d2e8bdffb4cfda48057525b5e7da076acb248eee2c0c5ddaf384b478b18cd9` |
| `notes/theory/2026-10-24-callback-permission-bridge.md` | `c228ff45a272a52b92eaaccd91183272438bb8c3287dd39e7749d700ce919f4d` |
| `tasks/agent-loop/inbox/20261024-callback-permission-bridge.md` | `dddd305fb7d0aa6aca86b0868cf1a4806703e58e57f7c8b8e2e14ac0c5949335` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |
| `crates/yu-hir/src/module/source_annotation.rs` | `409ce491bc216c6963bf76d20810790aa2756edf260ecc35e76d5cfc05d24b3f` |
| `crates/yu-hir/src/module/local_source.rs` | `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1` |
| `crates/yu-solver/src/candidate_source.rs` | `57b119592a6a8d4afd42aca10c5e2bb749cfdf0fb0fdea967dd437d552a1a04e` |
| `crates/yu-solver/src/candidate_effect.rs` | `70c42056a1041d54f88f16d7712875e3acf9ef7649b99a34bc990ff19f04936f` |
| `crates/yu-solver/src/shadow_apply.rs` | `f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d` |
| `tools/inference-playground/src/runtime/program.rs` | `df58f9a1d60e39fafe6d85b1e50331b35fde2a9142a2eaea84ad028d3048fdb0` |
| `tools/inference-playground/src/runtime/receiving.rs` | `2170a3bcbc6710ce3fbf721a05129117f8266b9ecf21c67136db918815303551` |
| `tools/inference-playground/src/runtime/machine.rs` | `d993905eacc0c22f4f371a7a97cf3f3d4a48434fe1538976fba0739107e8f647` |
| `tools/inference-playground/src/runtime/continuation.rs` | `194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3` |
| `tools/inference-playground/src/runtime/primitive.rs` | `eb0a53bfec8ce2854adbe6342c984d5140fd1585d91da5a8a9739d2ac96e8a85` |

Contract-declared baseline is `a0dcc92b8f8b866f7ed2e06acf399a4c86057a3c`;
Luna's launch baseline is `5051a696f`, with the contract committed there and
identical pinned owner bytes. No Git query was made. Requested Sol/high;
observed model/effort UNKNOWN; numeric session UNKNOWN. Actual worker
`/root/callback_permission_prover`; launch acknowledged before inspection.
First instrumented work time `2026-10-23 23:58:40 UTC`. Budget ≤1200 seconds;
final elapsed/counts and frozen byte hashes are in the single assigned inbox
and final receipt. No tests, builds, probes, code writes, Git or descendants.

Mutual TODO `CB-TRANSPORT-REVIEW-1`: Luna assigns fresh non-contributor review
of this construction and pins its bytes; the author cannot certify it.
`CB-TRANSPORT-IMPLEMENT-1`: after accepted proof, Luna implements the defined
program schema, entry/use metadata, delayed consumer opening, kind-separated
grant and delimiter correspondence in the three existing runtime leases.
Review must use the falsifiers above; any new owner/semantic requirement
returns to Luna before writing. Full static residual and parent/native gates
remain open. No further in-envelope producer stage follows this freeze.

Only new paths: this artifact and
`tasks/agent-loop/inbox/20261024-cb-permission-transport.md`. No scratch paths.
At submission writing has ceased and both outputs are frozen; no commands or
descendants remain active. This is a research handoff pending review, not an
approved implementation checkpoint.
