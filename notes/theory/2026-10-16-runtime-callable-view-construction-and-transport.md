# Callable execution views: source construction and VM transport handoff

Date: 2026-10-16
Status: proposed algorithm and bounded source-to-VM correspondence; reviewed CLEAN within assigned scope.
No implementation, architecture adoption or production authority.
Baseline: `30e2594512636adb52f4d720063e8918b1e162f6`.
Exclusive output: this new note only; all dependencies were read at that baseline.

## 1. Frozen claim and boundary

Fix the original independently valid source derivation T, its actual producer
and entry interfaces, annotation/instance/binder scopes, shared xi=(nu,K,D),
and the concrete component

```text
receive(f:Unit->alpha+) = let g=f(Unit) in g(Unit)
alpha+ = ([ctrl]Unit)->[ctrl]Int.
```

Use the [selected receiving action grammar](../design/2026-10-16-receiving-profile-introductions.md)
only within its stated scope: this component and its original receiving
actions. Retain every original alternative, opaque indexed dependency,
private contract and actual source-typing premise. Other producers' original
independent interfaces remain inputs, without a guessed interpretation.
Quantify over finite compatible source executions and currently admitted
forwarding/capture/reuse histories. This includes arbitrary actual carriers
and compatible assignments; no pure-Unit restriction is imposed on argument
code. An input expression returning Unit can perform effects first.

Required construction: emit source-indexed entry and execution recipes;
open a received callable's complete view before actual entry Force or
retained binding; retain it through body and original designated result
consumer; at actual completion combine the two *tagged* Return inputs;
transport its nested Function paths with their original receivers; retain
the same view/port/recipe through saved contexts. Observation creates no
receipt or boundary. Removing a consumed computation root must not erase
the returned value's independent packet.

Claim class: a constructive algorithm and simulation argument for this
source-owned metadata extension, followed by an exact proposed VM handoff.
It is not a claim that the current VM performs the construction. The source
derivation T is the independently owned input of the reviewed
[source export theorem](2026-10-16-runtime-function-result-source-construction.md)
§§1–5, not a premise asserting that the desired runtime packet is already
correct. The clauses below compute that packet. Raw HIR/native inference
does not by itself supply T.

Excluded conclusions: initial-world admission, independent primitive laws,
foreign-kernel embedding, complete Catch/context correctness, general
negative visibility, all-source/native profile supply, general payload or
response support, soundness, principality and F5. No fixed primitive
interpretation or guard is changed. The source action selection supplies
no automatic runtime/API or production approval.

## 2. Actual owners and the current seam

The [typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
§§2–3,9 constructs X/V from original source derivation nodes, complete
ExecuteCallable, producer entry/body and the distinct operation result
consumer. The [typed-boundary rules](../design/2026-10-02-typed-boundary-realization-draft.md)
§6 distinguish typed Flow, execution Observe and the two-input result rule.
The selected [first-call constructor](../design/2026-10-16-known-function-first-call-profile.md)
supplies the explicit outer callable component; the selected introduction
grammar supplies the current carrier and matching nested result component.
These are the changed inputs since the earlier
[runtime obstruction](2026-10-16-runtime-function-result-view-projection.md).

| Original owner / current VM owner | Actual operands and present behavior |
| --- | --- |
| Source formal / `program.rs::Instruction::Lambda`, `RootCompSchema::from_parameter` | Original Lambda SourceSite, HirParameterId, LocalSourceParameter and annotation owner/row. Current schema accepts only explicit Comp Unit/Int/Bool/Str; Value(Function) has no corresponding schema. |
| Source Call / `Frame::Callee` | Callee's actual ReceivedValue, original argument code/environment, caller site and selected executable producer. Current dispatch uses the callee value and drops its view as an execution delimiter. |
| Actual entry / `ValueEntry`, Comp branch, `OperationPayload`, `ResumeArgument` | Fresh actual invocation, whole delayed argument and original role. Current Comp-root entry emits boundary/receipt; Value entry forces then binds without the complete Function profile. |
| Elimination / `consume`, `execute`, `RootCompReturn` | Original Name consumption and view; request emission observes the executing vector. Normal RootCompReturn currently calls `ground(received.value)`. |
| Result / `Local`, `ReceiverReturn`, `CatchReturn`, cache frames | Actual returned ReceivedValue and original binding slot. Current storage usually preserves that one view; it does not combine a consumed callable view's result input. |
| Complete operation / `OperationResultConsumer` | Original declaration-selected one-layer consumer after native return. Current consumer passes only the value handle to `execute`. |
| Saved source View / `capture_template`, `TemplateNode::View`, `enter_template` | Current template retains only root ExecutionView and recreates execution from its old receipt. There is no callable port/result recipe or continuation answer-interface field. |

`RuntimeEvidence` currently contains only Name consumption. The retained
HIR and original source records give identities/annotations; they are not
an existing independent typed-action export. A source-plan import must be
added at this owner if the handoff is selected. Calling an annotation parser
a complete semantic exporter would leave the old supplier premise untouched.

## 3. Emit the plan at original source constructors

Preallocate one plan node per original derivation/interface node of T, then
fill edges using the original constructor, without unfolding recursion.
All references below include original scopes and the *same* substitution;
row/guard fields are not independently freshened. The proposed records are
a presentation of selected source outputs, not new semantic assumptions.

```text
EntryPlan = (original entry/formal/annotation/slot,
             carrier Force node, result-value schema, actual future inputs)
ExecPlan  = (original execution action, operand slot, exposed port,
             producer entry/body/declared consumer, result edge/ReturnSlot)
ReturnPlan = (original dependent return binder,
              ActualValue input map mu, ConsumedView result map rho)
```

### 3.1 Entry formation: concrete positive rule actions

For `receive`'s original annotated formal f, validate annotation owner and
formal source root against its actual Lambda. Emit these source instructions:

```text
Enter(r,e,f,Tcarrier,actual_beta,actual_annotation)
  fresh original boundary b_r
  E = In(e,f).force                         permission: none
  O = In(e,f).result.F0.call                 permission: none
  N = In(e,f).result.F0.result.F1.call        permission: original F1 Ctrl row
```

The three labels name local origins, not a replacement inventory for
inherited profiles. E follows from actually receiving the current carrier;
O follows from the original explicit outer Function complete invocation;
N follows from its matching explicit Function result. Their original
annotation scopes remain distinct. The outer omitted result row supplies
no concrete permission. The nested Function's declared result computation
does not create an additional returned first-class computation Force.
O/N name complete J_call positions, including entry and designated consumer;
neither position is an AE coordinate or merely the provider body's row.

Emit both original future-input instructions, retaining their whole
interfaces. They execute only when the actual later producer receives the
actual carrier, at its actual entry u1 or u2. Use that provider's real formal,
annotation and typed map. An actual retained `[ctrl]Unit` formal can introduce
its own root permission there; the checked positive `[ctrl]Unit` domain of
alpha+ is not that permission. No domain instruction stamps old r onto a
hypothetical input. Preserve any old-r incidence actually arriving through
an antecedent packet. This is the selected grammar's owner decomposition,
not exclusion inferred from positive variance or observation coverage.

### 3.2 Transport and return emission

At Name/alias/capture/instance, reference the actual stored packet and emit
that constructor's original typed map. Preserve the one instance for Alias;
retain the real substitution for an actual instantiation. Do not re-generalize
a captured packet. A Delay references the *whole argument computation's*
plan and lexical cells. Its entry-boundary result schema is not copied into
all captured private values. `direct_formal_root` remains an optimization
for its authentic direct Name case; it is not the general map emitter.

At each original elimination c, generate edges `(c,effect)` and `(c,result)`
from that operand derivation. Its matching result action is syntactic:

```text
rho_c((c,result).q) = q
rho_c((c,effect))   = undefined.
```

At a Call, the provider's original decomposition exports its complete port
and invocation-result recipe. Closure: actual formal/entry, body and return.
Operation: actual declaration instance, native-return delimiter, then its
designated declared-result consumer. Raw continuation: actual response-entry
interface and saved-context completion, with the original **answer** return
slot. An operation response B is not the saved continuation's answer type.
The source handler/control constructor owns that answer slot; the current
Template declaration alone does not encode it. Unknown producers keep their
original interface/action reference; no closure recipe is reconstructed from
an assigned Function shape or a runtime tag.

At each actual Return z, its executed source Result constructor supplies
the first packet W_z: literal descriptor, stored Name, actual Lambda/operation
descriptor, actual selected branch/arm, or completed child Call. It also
supplies its actual value correspondence mu_z. The plan already retains
the consumed operand V_c as the second input. Construct

```text
J_z = Image(ActualValue(z), mu_z, W_z)
      union_tagged Image(ConsumedView(c), rho_c, V_c).
```

These tags survive even when endpoints or boundary IDs coincide. The
ReturnSlot is filled by the current actual return/world; it stores no old
returned value. Nonidentity source conversions retain their own actual maps
in their original position. Symbolic or recursive endpoints retain scoped
edge references instead of enumerating assigned shapes. Apply these actions
to profiles and carried dependency incidence; retain original K, nu,
contracts, lineage and unrelated request/residual graphs at their owners.
The two edges share that one z/current-world witness and its original guards.
They are not separately witnessed provider choices. A saved recipe binds a
new actual return on each execution occurrence while preserving its original
source binder/scope; it does not instantiate inherited shared fields anew.

The join from source instructions to VM code is also generated here: original
Name occurrence/resolution to its binding map, original Lambda/formal to its
EntryPlan, each original Apply occurrence to its callee/argument/full-Call
ExecPlan, and the original sequential binding to its actual ReturnSlot.
For this component these include the distinct f-read/c1, g-binding and
g-read/c2 occurrences. SourceUpperUse/full IF supplies each original use map;
the explicit annotation supplies no ProtectedVarAt/omitted-formal seed.
No map is selected by matching the eventual f or g runtime shape.

### 3.3 Why this is construction rather than a supplied-view premise

Each emitted entry node is an explicit selected Enter/Val/FutureInput action
on the original annotation/formal. Each transport edge comes from the
actual source rule; each result edge/return binder comes from its elimination
or complete invocation. Actual W is furnished by the executed Result rule.
The source export theorem §§3–5 proves this extraction and erasure; the new
selected grammar supplies the previously missing entry profile actions for
this component. No `LawfulCompleteView` or desired output packet is assumed.

Opaque inherited interfaces still require their original independent laws;
formation neither proves those laws nor discards their guards. A producer
without an independently supplied interface cannot acquire one by this
algorithm. Thus the construction closes this metadata-emission subgate for
the fixed T/component, while native-to-T supply remains a different gate.

## 4. Proposed finite VM representation

Use flat immutable arenas for source plans, runtime views, introduction
origins, tagged transport nodes and execution occurrences. A view records
its underlying ValueHandle and original typed source endpoint. Origins store
original receiver, entry/formal/annotation slot and path-specific permission.
A transport node references its input view, original typed map and input
tag. A result node has the two edges in §3.2. Unknown inherited coverage
remains an indexed original dependency/interface reference, never `false`
or an empty remainder. References can represent an unbounded future path
family without unfolding it. This is a proposed layout, not an adopted API.

The existing `View.image: Option<usize>` root chain, scalar `unknown` and
one `Boundary.schema` cannot alone encode result union or O/N permissions.
A compatible generalization must decode to the selected source graph.
Eager indexed images and an immutable mapped-input DAG are alternative
representations of the same source output; this note proposes the latter
because it preserves both tagged operands without profile enumeration.
No correctness conclusion depends on approving that storage choice.

For a positive local Grant query, start from the authentic event observation
and its *specific* view/port. Follow original typed-map preimages and tags to
an actual introduction/antecedent incidence. Join the genuine candidate-owner
receipt through its original typed route, the matching original permission
slot, exact family and current original receiver/handler activity. Success
on any authentic route supplies the existing disjunction's Grant; another
observed profile is not a new veto. Unknown branches cannot certify absence.

The root implementation's receiver binary search, single outer-row lookup
and older-parent cutoff do not establish this multi-path query. Replace or
justify them for the richer graph; retain memoization keyed by image/path/
scope state only after receipt/guard authentication. Do not memoize a negative
result from an unmatched receipt. Work is proportional to actually visited
mapped-image states and required guard/row checks, not automatically constant;
the implementation owner must bound allocations and query amplification.
No full semantic K/D solver is claimed to exist in `receiving.rs`.
Source registered recursion remains a reference rather than eager expansion.
Completeness/termination of a general symbolic guard or path query is not
proved here. A consumer lacking the authentic decision evidence remains
unavailable; it cannot replace that evidence with a negative answer.

Execution authentication must separate an original source execution action
from receipt production. Proposed `open(view,port,ExecPlan)` checks the exact
original source action/operand mapping and creates a fresh occurrence.
`Observe` records that occurrence and fresh event; neither operation creates
Receive. The old root receipt can remain evidence for its original root
action, but a new callable scope must not invent a receipt merely to satisfy
the current `execution(view,receipt)` API. Callee use does not make the callee's
new invocation the recipient of its own public view.

Genuine entry, Value-entry result rebind, local ResultBind and executed Name
bindings export their own source receipt/typed correspondence. Preserve that
route when the result view handle changes; exact-handle indexing alone is
not a proof of the source Path relation. Use the actual current executable
owner for a new receipt, never a dead saved original owner. A receipt adds
no profile. Capture, cache copying, query and observer restoration alone
are not executed receiving actions.

## 5. Concrete frame algorithm and scope placement

Generalize `RootCompReturn` to `ViewReturn(execution,ReturnPlan)` and add
complete callable instances of the same delimiter. The following order is
bottom-to-top; newly pushed producer frames are above the callable delimiter.
Opening occurs after actual callee evaluation and before actual entry.

| Selected producer | Frames above the callable ViewReturn, in push order |
| --- | --- |
| Closure Value entry | ReceiverReturn; ValueEntry; carrier ViewReturn; execute the original whole Delay once. Carrier completion projects before ValueEntry rebind/body. |
| Closure Comp entry | ReceiverReturn; Enter and bind the inert whole carrier, with genuine receipt; run body. Open a carrier view only at its actual designated consumption. |
| Operation Value entry | OperationResultConsumer; ReceiverReturn; OperationPayload; carrier ViewReturn; execute Delay once. |
| Operation Comp entry | OperationResultConsumer; ReceiverReturn; actual Enter/binding of its inert carrier under its independently valid declaration action; make native request carrier. |
| Raw continuation | ReceiverReturn; ResumeArgument; response-carrier ViewReturn; execute response expression once. ResumeArgument validates the original response interface, then ResumeReturn and EnterTemplate run the saved context. |

Each actual entry runs the applicable EntryPlan before its Value Force or
retained binding. For receive, carrier E is therefore present during Force,
with O/N latent at the matching result paths. ValueEntry binds J_z from
that carrier completion and records the actual source receipt/route. The
callable delimiter remains below ValueEntry, body and ReceiverReturn.

For operations, native ReceiverReturn ends that invocation before the
separate declared consumer, exactly as in current code. The complete callable
delimiter is lower than **OperationResultConsumer**, so its observation remains
through that consumer. Retain the whole ReceivedValue and its declaration-
selected execution recipe there; replacing it with `execute(value)` loses
the consumed view input. This introduces one source-selected elimination,
not recursive force-until-data or permission from a result tag.

For raw continuation, the complete delimiter remains through response entry
and saved-context completion. Retain the original source answer-result
recipe separately from the operation declaration's response B. Current
primitive B validation remains in force. No Function payload/response matcher
is widened by this algorithm.

Normal `ViewReturn` first obtains this completion's actual ReceivedValue W,
then constructs §3.2 with its retained consumed view and original result
recipe, closes exactly its own execution occurrence, and returns J_z. A
consumed root maps to nothing through rho; it does not erase W. This replaces
`ground(received.value)` at the owning completion, including a computation
whose actual result is callable. No latent result execution occurs.

At first f use, the entry carrier projection sends O to F0.call and N to
F0.result.F1.call, removing only E's contribution through that edge. Name
supplies its genuine receipt. The first full Call opens F0.call, so O is
applicable before entry. Its Return uses actual W_1 plus the original
result-prefix image: O has no image there; N reaches g's F1.call with the
same b_r, nested row and original admission slot. Local ResultBind stores
that J_g and current world without another boundary. The second Name/Call
opens g's F1.call before its entry, supplying N's second-use applicability.
Any independently r-marked W_1 contribution also survives; neither O's
removal nor N's presence determines that independent input.

## 6. Suspension, restoration and every current runtime path

At request emission, `execute(Request)` remains the event owner: fresh event,
observations of all actual executing source views/ports, then candidate
selection. Forwarding keeps that event's observations. A new arm event gets
its own observations; no retroactive eligibility repair is permitted.

When unwind crosses ViewReturn, close that occurrence and save its immutable
view, port and ReturnPlan as a TemplateNode::View. Uncrossed ambient views
stay active. On entry, create a fresh execution occurrence and restore that
same delimiter/recipe in the existing frame order. Replay neither Enter nor
receipt. The current use's actual W fills its ReturnSlot; no saved W is
reused. ReceiverReturn/OwnerReturn may resolve executable control by existing
borrowed/fresh rules, but that control map never rewrites original b_r or
annotation receivers. Expired origins stay expired. Repeat this argument
for forwarding, reuse and recapture. Flat arena references preserve the
existing avoidance of recursive owned context destruction.

| Current path | Required metadata action; unchanged operational boundary |
| --- | --- |
| Unit/Int/Bool/Str, implicit Unit | Source literal packet has no new latent positions. `ground_data` is justified here; do not generalize it to arbitrary completion. |
| Lambda/Operation/Continuation data allocation | Attach the original source producer/descriptor packet and executable recipe. An opaque inherited input stays opaque; do not declare it empty from a runtime tag. |
| Name / GlobalRead completion | Same binding packet and original typed map; genuine executed consume supplies receipt. Existing one-layer Execute/Observe distinction remains. |
| Local / ValueEntry / actual value-arm binding | Store actual J_z/current world and its original binding route; genuine binding evidence only, no new boundary at g. |
| Forward/group/ascription | Original source forwarding map; no extra Force or invocation. Current bounded runtime has no registered adaptation implementation. |
| Condition / selected branch / shallow value arm | Retain the actually chosen child's packet and original checking map. Boolean test/discard-to-Unit genuinely discards its value, without deleting unrelated packet graphs. |
| Direct formal forwarding / Delay | Existing exact Name map is a valid special case. Other argument dependencies come from the actual computation plan, not an environment scan or guessed root identity. |
| ReceiverReturn / OwnerReturn / ResumeReturn | Preserve returned view; end only the designated executable owner. Callable ViewReturn remains at its source delimiter. |
| OperationPayload / request carrier | Retain whole actual payload packet and original declaration consumer recipe, including opaque dependencies. Request construction is inert. |
| OperationResultConsumer / RootCompReturn | Consume the exact declared port and use two tagged Return inputs; do not erase the view through value-only execute or ground. |
| Root / GlobalRead cache publication / ExpressionReturn | Preserve original current-store publication/discard behavior. No new capture/materialization support; current rejected initializer-crossing cases remain rejected. |
| Handler payload/k binding and selector | Preserve original primitive OpCompat checks, source guards, actual packet bindings and shallow delimiter. Attach k's actual source control/answer recipe; selection itself creates no profile. |
| Budget suspension / unhandled event / unavailable path | Retain live state and existing errors. No synthetic normal completion, receipt, export witness or negative certificate. |

## 7. Correspondence proof and applicability boundary

Use a relation between the original source execution and the proposed
metadata-enriched machine: underlying code/environment/store/control are
the existing related ones; every live runtime view decodes to its actual
source packet/endpoint; every active execution occurrence corresponds to
one original source View(view,port,context); each pending ReturnPlan points
to that context's original dependent return binder. Origins and scoped
symbolic references are identical, not merely equal by family/type.

Construction induction establishes the relation at emitted source nodes.
Entry follows the selected Enter/Val actions, preserving antecedent packets.
Name/capture/store transport follows the actual typed map. Call pushes its
View below every producer-specific frame, giving the complete source scope
before Force, across body and after native return through the designated
consumer. Request therefore records the correct currently executing port
occurrences. Normal completion follows the actual Result constructor for W
and the syntactically generated result edge for V; the tagged union is
exactly the selected two-input rule. Branch/arm picks the original selected
child, without manufacturing an alternative packet. Capture/restoration
uses §6, with a fresh occurrence and the same recipe/current return. Induction
over finite steps and finite reuse histories proves these metadata clauses.

Erasing the **source export/plan** recovers the original typed source actions
by the reviewed extraction theorem. This does not prove that erasing a
proposed implementation yields identical *current VM eligibility*: the
current VM lacks these scopes/profiles. It is precisely the integration
being proposed. Full execution transport still requires the original
independently valid producer/entry/guard/OpCompat and source-to-runtime
premises; the metadata induction does not prove primitive validity, Initial,
handler correctness or their availability from HIR.

The [primitive RootComp theorem](2026-10-16-primitive-computation-root-receiving.md)
§§1–4 justifies its actual explicit Comp entry and ground-result root
projection. For its four rigid leaves, rho has no latent result incidence;
the richer algorithm specializes to that projection while retaining W and
unrelated live dependencies. Its unknown-coverage limitation remains.

The [closed primitive event theorem](2026-10-16-runtime-primitive-event-visibility.md)
has a different source-domain/profile premise, including no native operation
Value-entry profile in its proof table. The selected new constructor is
scoped to the concrete two-Call component. There is no established
source-qualified contradiction between them here. **If** a future VM change
applies the new current-carrier Enter action at primitive operation entries
covered by that old classifier, its old empty-profile premise must be
re-established or the negative-certificate consumer revised at its actual
owner before integration. The current classifier alone supplies neither
proof. A nested Catch/operation trace without exact admitted Lambda/entry/
event/slot/maps for the selected source domain is only an applicability
discriminator, not a runtime/source counterexample. No such authenticity
or full Catch bridge is established by this note.

## 8. Executable handoff and unresolved owners

| File / operation | Proposed implementer responsibility and required invariant |
| --- | --- |
| `runtime/program.rs` export/import | Join original formal/annotation/instance IDs to source Entry/Exec/Return plans; validate missing/foreign plans explicitly. HIR Name evidence is insufficient. Preserve source scopes and actual typed operand maps. |
| `runtime/receiving.rs` | Port-indexed introductions, tagged mapped inputs, original unknown references, execution authentication distinct from receipt, exact source Path/Grant query. No inferred negative profile result. |
| `runtime/machine.rs` Callee / entry / completion | Preserve callee view; install full delimiter in §5's order; actual Enter before Force/retention; use current W plus retained V; authentic binding routes; whole view at operation consumer. |
| `runtime/machine.rs` allocation / store / event | Attach source descriptor packets, preserve private capture references separately, observe current source ports; no receipt at Observe. |
| `runtime/continuation.rs`, capture/entry fold | Retain exact view/port/ReturnPlan plus original continuation answer interface; fresh occurrences only; executable-owner mapping never touches provenance. |
| `runtime/primitive.rs` and selector | Retain existing supported matchers and guards. Revalidate the negative classifier if its actual entry domain changes; do not assume this note widens its theorem. |

Concrete proposed assertion/verification obligations for the primary's sole
verification owner: entry Force occurs under E and complete callable views;
OperationResultConsumer runs inside the complete delimiter but after native
receiver return; f completion drops O's result image while preserving N and
independent W; g's second use retains original r and nested Ctrl row; later
carrier u2 has only its genuine new origin plus real antecedents; observer
opening creates no receipt; unrelated permission paths never grant; restored
dead receiver remains dead; second template use reads current W/cells; no
initializer-crossing capability is added. These are requested checks, not
tests run or proof of the missing native supplier.

First missing executable owner: `RuntimeProgram::from_hir`
imports no independently typed Entry/Exec/Return plan. The construction
above explains what that owner must emit/import and why the selected source
rules provide this component's fields; it does not pretend the current API
already does so. Continuation source-answer metadata and general source
typed-map transport are further explicit representation seams. Architecture
may choose a source-plan import versus an independently checked export in
the compiler, and DAG versus eager mapped storage; neither choice authorizes
inventing source/primitive validity or dropping unknown fields.

One next action: obtain fresh independent mathematical and source/authority
review of this plan/emitter/frame handoff, then lease the bounded original-
formal Function Entry/Return import against this component, keeping its
native supplier and every affected eligibility consumer OPEN until reviewed.

## 9. Pins, checks and commit packet

Every dependency read used `git show 30e259451:<path>`. Runtime files are
byte-identical to the parent's unchanged runtime snapshot. SHA-256 pins:

| Dependency | SHA-256 |
| --- | --- |
| receiving introduction design | `401ac9eee69f27a863cd08ea24eea6fbbd3388ada9d5366bd5818ee966d73b6f` |
| introduction grammar/proof | `ec3375229f956d678c64003a43bdb68c70a77c6b8e614e9348bdca6bde9d5a8c` |
| prior runtime obstruction | `e7d2464fb90d70a1c69dc0a2210d27833e22901ecc6fd68d26ac06a5a9e4e79d` |
| source result/Call export | `bfec4f6aad05711b580ceac69b242de502342c31bc09fabc701ad17c583c4961` |
| selected first-call design | `b779ba779b66515eddb7e44ba1d0772a6853e69a1aa13a6c4528dbd8ea0852a1` |
| first-call proof | `7051eafe3221b97229a760e52639f6a5c329860175ded210e7953a77a395e42a` |
| typed core | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| typed boundary | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| primitive RootComp theorem/integration | `a043c69eb9fd82127bb7ad59d797abf3f10c5edf83bd80316183074f48c28606` |
| closed primitive event theorem | `7b27f8cf1d8024e249cc7d8a433c77438e3f59e5543cfc46a96a1af278eb3f56` |
| template correspondence | `f3a4c925a197e63e5b7faf1ce1e1caf5736d76f1b86ba162c6acc85bfff8e7dd` |
| runtime/program.rs | `b9798ac4c5d93e761582d712114615defa913f858d70e91f170471c8b8912748` |
| runtime/receiving.rs | `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9` |
| runtime/machine.rs | `04024174d88223e252e1d093eaee96c17d9f43d4d32bea5c41631017c9da208c` |
| runtime/continuation.rs | `194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3` |
| runtime/primitive.rs | `97485b9439357497aaf3f19555b1d87eef4aabc955b3a2815f23cf49a65c0153` |
| runtime/mod.rs | `64d208743793a03501a76f56bc2b511c50ed40cff3f789757a00b7d608fc846b` |

Checks: bounded pinned source/constructor trace; all 17 table SHA-256 pins
reproduced at the baseline; all 8 local Markdown links resolve; fences,
tabs and trailing whitespace clean. One misspelled read path was rejected and
corrected to `2026-10-16-primitive-computation-root-receiving.md`; no empty
pipe digest was accepted as a dependency pin. No code/shared-file writes,
Git mutation, build, test, executable probe, network, child or benchmark.
Assigned wall cap 25 minutes; approximately 15 minutes consumed through final
integrity check; CPU/RAM uninstrumented; no measurement samples
or processes. Requested Sol/high; observed model/effort metadata unavailable.
No escalation. Primary remains the sole verification/integration owner.

Commit packet:

- Sole changed path: `notes/theory/2026-10-16-runtime-callable-view-construction-and-transport.md`.
- Baseline: `30e2594512636adb52f4d720063e8918b1e162f6`; dependencies unchanged
  by this leaf, pinned above. Primary revalidates later dependency changes.
- Review: fresh mathematical review CLEAN and source/authority review CLEAN
  after correcting the `RuntimeProgram::from_hir` owner locator. The reviewed
  bytes before that one-name correction had SHA-256
  `b2dc96de4f9225e9c0eea54a70752e5a4a026ba6591883b627a742dc4aead714`; the
  correction does not change a construction clause, premise or conclusion.
  Original executable/all-source parents remain OPEN.
- Checks already run: source trace, dependency SHA-256 and local note integrity;
  no executable verification. Writing stops at frozen handoff.
- Proposed checkpoint: `research: derive callable receiving view VM handoff`.
- Shared deltas left to primary/curator: record concrete source emitter,
  frame/result/template handoff and exact import/eligibility residual owners;
  adopt no runtime representation or production status from this note.
