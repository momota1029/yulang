# Initialization effect order: internal requests and outward observations

Date: 2026-10-16
Status: bounded source-kernel derivation and actual constructor trace;
initialization-order observation boundary unresolved. Independent review CLEAN.
Baseline supplied by primary: `31c3c6553`; initial runtime `35e87f844`.
The authorized late runtime boundary delta is revalidated separately in §8.
Exclusive lease: this note only. No implementation or source-policy authority.

Independent mathematical/source review: `runtime_semantic_review` returned CLEAN
at producer SHA-256 `d7fe8657b94fa9a97ca1903da9724a532cc4f79b803d664c7da3dd2fc4aff223`.
The pending observation question has separate semantic and specification CLEAN
prepublication review. These results select no source observation or scheduler.
Primary revalidated all dependency hashes at integration: the governing decision
has only an appended local-implementation checkpoint; its approved text prefix
is byte-identical to the recorded baseline. All other listed inputs match.

## 1. Frozen question and governing decision

Use the exact approved question1 / answer1 revision2 in
[initialization-context approved answer](../../questions/2026-10-16-forward-definition-initialization-context/approved-answer.md),
integrated by `885012b42`, and
[initialization order/global effects](../design/2026-10-16-initialization-order-global-effects.md).
Effect-producing lines cannot be exchanged with one another. This is neither
blanket dependency-first timing nor a rule making each such line immovable.
Effects escaping initialization are global or errors. The answer selects no
effect detector, uninitialized-reference outcome or arbitrary global-handler
registration mechanism. Internal initializer handlers retain ordinary semantics.

For the source below, derive the ordinary local computations and current
runtime frame path. Determine whether the selected ordering predicate counts
all internal Request events or requests escaping the whole initializer. Do
not infer initializer purity from Name purity, root-fetch classification or
an allowance. Distinguish a kernel calculation, an authentic compiled-graph
constructor trace and whole-source inference/admission.

```yu
act signal:
    our ping: int -> int
my first = {
    my x = later;
    catch signal::ping 1 { signal::ping(p), _ -> x, v -> v }
}
my later = catch signal::ping 2 { signal::ping(p), _ -> p, v -> v }
my main = first
```

The declaration denotes one original resolved primitive operation
`signal::ping : Value(Int) -> Comp(signal,Int)`. Keep the original declaration
and source occurrences distinct from its fresh dynamic invocation/request
instances. No operation name is interpreted as a builtin/global registration.
No parse, inference or execution probe is performed here.

## 2. Original local source derivations

Fix the original declaration environment and joint xi=(nu,K,D), ordinary
ground Int contracts, and well-formed original handler patterns/arms. Module
reference interfaces give later:Int, first:Int and main:Int at their original
binding roots. Forward reference availability/timing is not proved by those
interfaces. Write P_n for the complete source invocation `signal::ping n`.

### Complete primitive invocation

Literal n has Value(Int), normalization Return(n), and empty evaluation effect.
The operation value is inert. Call forms the original whole Delay(Return(n))
without executing it. Value entry establishes receipt, forces that carrier,
rebinds its Int result and returns MakeRequestThunk at native return.
The **declaration-derived result consumer**, after that return and inside the
complete invocation view, exposes

```text
P_n = Request(q_n, C_n, k_n),
q_n = (original signal::ping instance, payload n, source origin/event, K_n,D_n),
k_n : each admitted Int response/current state -> remaining Int result.
```

The complete source computation has result Int. A raw native thunk Return is
not this completed operation. These are typed-core §3/§6 and ordinary
computation package §§2–3's original clauses, not a new effect model.

### Later's handler image

Let H_L be the ordinary shallow handler at later. Its operation arm binds
p:Int to q_2's actual payload and discards the raw continuation (`_`). Its
body is Name p, hence pure Return(2) in that arm environment. Its value arm
binds v:Int and returns the same value. Both are ordinary Int branches.

The Catch image (§5 of the ordinary computation package) installs H_L around
P_2. The direct request has no supplied callback/protected-input boundary.
The matching operation/payload pattern selects, H_L is left, and its arm
runs outside H_L. It returns the payload2 without resuming k_2. Consequently

```text
Handle(H_L,P_2) = Return(2,C_L'),
outward request support at this whole initializer = empty.
```

Internally there was a genuine Request event q_2 and its selection. The
outward support is projected **after** the handler image, not before it.
Discarding k_2 does not restart it or create another request.

### First's body and its handler image

The original Name-role judgment gives a value-reference computation for
later, `Comp(empty,FreshUse(Int))`, once that value is available. It does
not execute or type later's initializer as part of Name. Given the returned
value2, original result Bind installs x:Int at that same post-reference
world. Let H_F's operation arm ignore q_1's raw continuation and return this
same x; its value arm returns v. Thus its complete ordinary body calculation is

```text
Return(2) >>= (x. Handle(H_F,P_1)) = Return(2,C_F'),
outward request support of that handler/body = empty.
```

The internal q_1 has payload1 even though the arm returns x=2. The value arm
is well typed but is not selected on this concrete Request branch. None of
these equations confuses operation payload, response or initializer result.

This is a local source computation derivation under the original module
interfaces and ordinary handler contracts. It is **not** a proof that an
empty later cache may be filled at this point under the new module-order
rule. The missing empty-global timing construction remains separate from
the pure Name/body derivation, exactly as the reviewed
[Name-role theorem](2026-10-16-definition-name-computation-role.md) requires.

## 3. Two exact projections of the same calculation

Instantiate the dependency-demand path actually present in the current
machine: while first awaits later's value, run later's initializer, then
continue first. This instantiation is characterized below; it is not selected
as an authorized source scheduling law by this note.

The resulting internal Request trace, attributed to the currently active
initializer, is

```text
[(later, signal::ping, payload2), (first, signal::ping, payload1)].
```

Their dynamic events are distinct: the first request created can have event0
with payload2, and the next event1 with payload1. Payload numerals are not
event ordinals. Both whole initializer images return2 and expose no Request
to their enclosing module consumer. In particular:

```text
InternalRequests(later) != empty;  OutwardRequests(later) = empty,
InternalRequests(first) != empty;  OutwardRequests(first) = empty.
```

This separates two existing source-observation coordinates. It is not a
counterexample to an already selected definition of “effect-producing line.”
That definition is the precise unresolved issue in §6.

## 4. Actual stable runtime frame trace

The following is static evaluation of the actual constructors for an
authentic program graph with the shown resolved operations, primitives and
bindings. It is not a recorded run or proof of source acceptance/parse
coverage. Name consumption is Observe for these module/local/Catch binders.
Let c_F,c_L,c_M be the original definition cells and x_F its local cell.
Omit only ordinary operation/Force frames where a row says so.
Line locators here refer to the initial observed machine digest `e30bb19c...`;
§8 records the subsequent boundary-only delta and its applicability check.

`program.rs:465–489` registers every definition value cell. First's nonempty
Block and later's Catch enter the source schedule, in the order first,later.
Bare Name main is not a computed root under that classifier; selection of
main materializes it after the ordered roots. The Act placeholder is accepted
only by the existing authenticated declaration-error branch at :187–218;
it is not a runtime computation root or a global handler.

| Step | Frames/demand and actual transition |
| --- | --- |
| 1 | `begin_root(0)` marks c_F initializing and pushes Root{cell:c_F,next:1}; evaluate first's body in environment0. |
| 2 | Block creates the pending Local frame/cell for x. Name later finds c_L empty. `machine.rs:444–477` marks it and pushes GlobalRead{cell:c_L,Observe,site:first's Name}; evaluate later's original body in environment0. |
| 3 | Later installs CatchReturn(H_L, owner:ModuleRun) above GlobalRead(c_L). The pending Root(c_F) and Local(x_F) remain below it. First's H_F has not yet been installed. |
| 4 | Operation evaluation creates an inert Delay of literal2. Its Value entry forces2, creates the request carrier, and returns across ReceiverReturn. OperationResultConsumer executes it and `execute:1556–1588` creates q_2. Current handler owner is again ModuleRun; nearest initialization demand is still GlobalRead(c_L). |
| 5 | `propagate_request:1225–1340` selects the original matching H_L. Payload is Int2; continuation wildcard does not capture/resume. Pop only H_L and discard its inside suffix; run Name p outside it, returning2. No Root/GlobalRead frame is crossed by this local selection. |
| 6 | `return_value:912–928` pops GlobalRead(c_L), caches later's returned value2, clears its initializing marker and consumes Observe. Returning2 reaches Local(x_F), installing x=2. Evaluation continues to first's final Catch. |
| 7 | Install H_F under the same ModuleRun owner. The operation1 entry/native-return/designated-consumer sequence creates q_1 only now. Select H_F, discard its raw suffix and run Name x, returning2. Nearest initialization demand is Root(c_F). |
| 8 | `return_value:903–911` caches first=2 and calls begin_root(1). Its scheduled later slot finds c_L already populated and skips it (`:1447–1450`); no second q_2 occurs. |
| 9 | At the end of the schedule, selected main is still empty. The existing fallback Root(c_M) evaluates Name first from its populated cell and caches main=2. Completion returns that selected value. |

The ordinary local handler guard is justified for this *graph envelope* by
the actual closed-primitive classifier (`runtime/primitive.rs:31–188`): no
Lambda/Resume, all operation signatures/values/patterns are primitive Int,
continuations are wildcards, names Observe ground values, and the dependency
graph main→first→later is acyclic. Its code/owner checks still require the
authentic HIR graph; this is not a claim that a source spelling alone certifies
it. Under that classifier H_L/H_F need no invented positive Grant. Their
installation owner is active ModuleRun at selection. Native operation return
precedes the designated request consumer (`machine.rs:768–785`), so the
transient operation invocation does not mismatch the installing owner.

Both requests are internally handled; neither reaches an escaping-initializer
global boundary, no global consumer is used, and no cache-bearing continuation
capture/publication law is needed on this wildcard-discard path.

## 5. Authenticate the active module demand without a registry

At q_2, the nearest module-demand delimiter is GlobalRead{cell:c_L}; at q_1
it is Root{cell:c_F}. The existing globals/definition table maps each cell to
its actual program.definitions entry and original DefId. Use that cell, not
GlobalRead.site.source_root: the latter is the source of the *read* in first,
not the initializer currently supplying its unavailable value.

This marker projection skips Call/Force/owner/handler frames. Such ordinary
internal calls and forces do not themselves change the enclosing module
demand. A nested empty GlobalRead supplies the new nearest marker until its
return, then the previous marker is exposed again. A direct expression has
its honest ExpressionReturn{root,next} delimiter and no fake definition cell.
Existing successful raw-Resume/owner machinery does not by itself introduce
a new module-demand identity. This observation does not override the separate
cache-bearing capture guards or prove all suspended initialization/resumption
cases source-correct.

ExecutionOwner::ModuleRun is shared by the two initializer spans and is not
their definition identity. Conversely a callback's provider SourceSite may
belong to another definition while the enclosing demand remains first.
The needed demand association is therefore already available in these actual
frames; it neither requires a new registry nor chooses an effect-order policy.

### What current static classifications do not prove

`BindingFetch`/computed-root classification distinguishes where code must be
demanded, not whether requests actually occur. An effect-free Catch/Block
is still computed. The reviewed Name theorem proves the reference's pure
value role, not E_init(d)=empty and not empty-cache timing.

`candidate_source.rs:1139–1167` keeps the initializer's actual body component
and passes its evaluation-effect component to a root annotation when present;
the stored definition root is its value interface. This does not create an
effect-order detector. The current Catch constructor (:870–888) conservatively
forwards scrutinee/arm effects to its result. It need not infer an empty row
for this exact empty **outward handler image**. A nonempty inferred may-bound
or declared allowance is not proof that an event actually happens, and an
exact outward-empty image is not proof no internal request occurred.

## 6. Exact unresolved observation boundary

The existing kernel fixes both sides of the separation:

- Ordinary computation §2 contains real Request events with source/event/K/D
  and raw continuations. Complete typed-view observation can retain a request
  before internal handler filtering; it is required for routing/hygiene.
- Its §5 defines the handler image and projects outward support **after**
  matching, selection and arm/resumption behavior. Both initializer images
  above have empty outward support.

The new approved answer says “effect-producing lines” in its ordering clause
and separately says effects **escaping** initialization are global/errors.
It does not explicitly identify the first phrase with either all internal
Request creation or the outward whole-initializer Request projection. The
effect-row judgment is a conservative bound on the latter computation view;
it is not an equivalence defining event occurrence. The full observation
retains more information. No consumed constructor equates these projections;
the calculation above proves they can differ.

Consequently the following interpretations cannot be distinguished by the
authority inspected here without an additional boundary interpretation:

1. Count both internal q_1/q_2 as the lines' relevant effects. Then the current
   nested initialization trace's effect-attributed sequence is later,first,
   reversing their source order. First began earlier: the initializers are
   interleaved, rather than two whole instruction blocks literally swapped.
2. Count only requests escaping each whole initializer's own ordinary
   handlers. Neither line in this example has such an effect, so this example
   supplies no effect-producing pair whose order the trace reverses.

This is **not** adoption of option2, a declaration that option1 contradicts
the user's intention, or a claim every order issue needs a new user question.
It pinpoints the missing source interpretation at the initialization owner:

```text
Which original initializer observation position supplies EffectLine(d),
the predicate consumed by the approved pairwise source-order rule?
```

Its introduction must state whether an internally selected Request is counted
at its creation/initialization demand or only after the initializer's handler
image. The escaping/global-consumer clause alone answers a different boundary
question. Nearest existing demand markers supply authentic ownership once
that source rule is fixed; their existence does not decide the rule.

No blanket dependency-first plan, purity detector, rejection of all computed
forward references, or uninitialized-reference outcome follows. In particular
the actual trace does not certify approved whole-source admission merely
because the machine can complete it.

## 7. Strict dependency plus two outward effects: exact abstract obstruction

There is a separate elementary scheduling obstruction when both effects are
independently known to escape and a genuinely licensed global consumer allows
both initializations to complete. Suppose source order is d_F before d_L,
and d_F strictly needs d_L's completed value **before** emitting its own
outward effect a. Suppose d_L emits outward b before publishing that value.
Preserving those source computations forces

```text
emit(b) < publish(d_L) < consume-value(d_L,in d_F) < emit(a).
```

If the approved line-order rule requires their effects in source order, it
also requires emit(a)<emit(b). No complete schedule satisfies both. Pure
prefix interleaving does not remove this strict dependency. This proves an
abstract incompatibility for those premises; it selects no resolution policy.

It is **not** a qualified counterexample from the current program/graph.
The concrete handlers above make neither request outward. Removing H_L can
cause an unhandled error before first ever emits a, rather than yield two
reversed handled effects. A premise that some global consumer handles b and
a must have its own authentic source/runtime justification.

Current `SemanticImports(())` admits only empty imports (`yu-hir/module.rs:109–116`).
Act formation registers operation namespaces/signatures; a local family named
`io` or `nondet` does not create a builtin/global consumer. The inspected machine
has the ordinary handler search and terminal UnhandledRequest branch
(`:1344–1362`), not an authenticated automatic global dispatch for those local
declarations. The approved answer permits automatic global handling but
certifies no current consumer. Hence neither an empty imports argument nor
renaming this Act supplies the missing independently licensed global premise.

## 8. Handoff and verification boundary

### Authorized late runtime delta

The machine initially matched the pinned `e30bb19c54b1a4ee07f3b1d2f0a5e88e57f2226fd055071a6d1ca5f1bdfd5e3a`
when the owning frame/handler constructors were read. Final hashing detected
concurrent authorized boundary repair. The primary supplied its exact scope:
after unchanged local Catch search, stop an escaping request at GlobalRead
using the existing unhandled outcome; normal Name/return/root and internal
Catch behavior remain unchanged. The current machine digest is
`04024174d88223e252e1d093eaee96c17d9f43d4d32bea5c41631017c9da208c`.

Narrow direct reinspection confirms local arm selection returns at :1344,
before the new GlobalRead check at :1350–1353. In this instance each request
selects its own internal H_L/H_F before reaching that check. Thus the new
branch is unreachable along the traced path, and the internal event order,
empty outward images and cache-return trace are unaffected. Escaping cases
now stop at that boundary and remain outside this instance. No claim is made
that this small delta proves effect-producing-line order or global consumers.
No Git diff, runtime edit or execution was used for this revalidation.

### Result and remaining owner

Established in this packet, pending independent review: exact ordinary local
handler/body calculations; the conditional authentic-graph actual frame trace;
separation of internal versus outward observations; active-demand ownership
from existing frames; and the abstract strict-dependency obstruction.
Not established: parsing/inference acceptance of this source, whole-program
typed admission, selection of EffectLine's boundary, source correctness of
the current empty-global timing, automatic global consumers or a new detector.

One next action for the primary: resolve/derive the exact initialization
EffectLine observation constructor against the approved answer and existing
source effect judgment. Then apply it to this separating instance before
choosing a scheduling/checking implementation. The demand-owner constructor
is already available; another Name-purity proof cannot select the boundary.

Only static reads, the sole leased note and dependency hashing. No tests,
builds, probes, Git operations, delegation, production or shared-record edits.
One bounded pass within the assigned 18-minute budget; no experimental or
performance samples. Requested normal configured prover/Sol; observed runtime
model/effort metadata unavailable. Fresh independent review and all authority,
integration and shared-status updates remain primary-owned.

Dependency digests:

```text
8e238cdbd185c9f3bdd6042d7bc536bb827e869def34e363b3e79f29d8c77c12  questions/2026-10-16-forward-definition-initialization-context/approved-answer.md
c33d0e601ea5152068d0bd8b52f02747964455d9d2e8518974ca9c83bf15e37b  notes/design/2026-10-16-initialization-order-global-effects.md
ab12b442f4f3d3d11565c89cda82c1cb25b17e943c2851b6bc937252410311e5  notes/design/2026-10-16-module-expression-source-owner.md
ee3f5cf8185d516775b8915b0fda6dbb07390c3ecad7ac028eb5995581dff917  notes/design/2026-10-02-ordinary-computation-semantics-package.md
0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e  notes/design/2026-10-02-typed-computation-core-elaboration.md
1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb  notes/design/2026-10-02-typed-boundary-realization-draft.md
a7f5181c65326c30e47b8288d7af9462c344f6027d23955bd9d0f3be56f96f0d  notes/theory/2026-10-16-definition-name-computation-role.md
efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38  crates/yu-solver/src/candidate_source.rs
2e0c579a525efd5ac4c7ce0f06189c568ed46c7382d4576698a0b8d846c2228e  crates/yu-hir/src/module.rs
b9798ac4c5d93e761582d712114615defa913f858d70e91f170471c8b8912748  tools/inference-playground/src/runtime/program.rs
04024174d88223e252e1d093eaee96c17d9f43d4d32bea5c41631017c9da208c  tools/inference-playground/src/runtime/machine.rs
97485b9439357497aaf3f19555b1d87eef4aabc955b3a2815f23cf49a65c0153  tools/inference-playground/src/runtime/primitive.rs
```
