# Receiving-owned profile introduction for the concrete two-Call source graph

Date: 2026-10-16
Status: independently reviewed source-definition construction and scoped proof.
Independent mathematical capture_math_review and source/authority
capture_source_review are CLEAN at producer SHA-256
`21170e396926575487953e2e4a1cc4c3a5e4e1606b55a134cd2b89a65353402d`.
Selection: [receiving-owned profile actions](../design/2026-10-16-receiving-profile-introductions.md).
Baseline: `2140859b13b4450303dc4873a8cdb299e59169eb`
The primary reports the direct inputs unchanged at `6443656ef`.
Exclusive lease: this new note only; no production implementation authority.

## 1. Statement fixed before construction

Fix the authentic resolved source graph

```text
receive(f : Unit -> alpha+) = let g = f(Unit) in g(Unit)
alpha+ = ([ctrl] Unit) -> [ctrl] Int
```

Keep its original formal/Lambda/annotation identities, scope `S`, shared root
`R_f`, static slot `beta`, original two Name/Apply occurrences `n_1,c_1,n_2,c_2`,
and original parameter, result and checking endpoints. `ctrl` retains its
resolved declaration and type arguments. Use one coherent original
`xi=(nu,K,D)` and its original instance substitution. Omitted rows remain
distinct open coordinates. Nothing identifies a fresh Apply result with its
annotation endpoint merely because they are compatible.

Construct a finite **introduction/action grammar**, before a particular
challenge `d_0`, for the complete profile contributed by this receiving source
component. It must include the incoming whole carrier's current Force, the
outer callable, its returned explicit callable, and deferred actual receiving
actions for their future arguments. Preserve every antecedent packet and
opaque indexed dependency by its original reference, rather than enumerate
or erase it. Derive both actual Call-use maps and introduction inversion.

Operational interpretation quantifies over each independently valid source
entry/development, arbitrary compatible actual providers and carriers,
pending responses and finite reuse histories. Formation neither assumes nor
proves an initial world, primitive Sigma validity, fresh-run theorem, global
environment membership, successful inference/MODEL, or actual provider
acceptance. These remain the independent premises of an actual execution.
All original counterfactual carrier/private/future domains remain unchanged.

The target is the complete **new receiving contribution and its compositional
actions**, with full inherited interfaces retained. It is not a claim that
three local atoms enumerate the profiles of arbitrary opaque providers.
The all-source/foreign-kernel and production parents retain their original
scope and status.

## 2. Authority and the missing definition being completed

The [selected KnownFunctionReceive](../design/2026-10-16-known-function-first-call-profile.md)
constructs the outer complete-call component; it explicitly does not close
the rest of the inventory. Its [producer proof](2026-10-16-known-function-first-call-profile-construction.md)
is reused without strengthening its old claim.

The [receiver-relative default](../design/2026-10-15-callback-identity-forwarding.md)
protects effects associated with an actually received argument inside that
receiver's boundary. [Annotation policy](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–1.2 distinguishes local negative permission, positive allowance and actual
inflow. [Typed-boundary §6](../design/2026-10-02-typed-boundary-realization-draft.md)
supplies boundary introduction, indexed transport, receipts, observations and
current activity. Its general profile remains an input; it does not decide
the omitted whole-carrier/future-input introduction cases by itself.

This proposal completes those **source introduction cases** under the existing
definition permission in [contextual Function §1](../design/2026-10-08-contextual-function-membership-definition.md)
and [source Generalize §1](../design/2026-10-08-source-generalize-definition.md).
It uses [typed core §§3,6,9](../design/2026-10-02-typed-computation-core-elaboration.md),
the [actual source IF constructors §§4–5](2026-10-08-call-source-interface-construction.md),
and [source result/Call exports §§3–5](2026-10-16-runtime-function-result-source-construction.md).
The [directional rule §§2–3](../design/2026-10-06-directional-inferred-effect-protection-addendum.md)
and [callback B](../design/2026-10-03-callback-context-delivery.md) retain their
existing premises and role/entry meaning.

This is a new explicit constructor definition, not a claim that previously
selected clauses already proved the complete inventory. In particular,
neither positive polarity nor observation coverage is an exclusion rule.

## 3. Source ownership and distinct port families

An entry has an original invocation binder `rho`, actual receiving event
`e`, source parameter slot `s`, and whole inert argument binder `T`. These
are supplied by the source Call/entry constructor, before the argument runs.
Its current computation position is `In(e,s).force`; its value result is
`In(e,s).result`. A Value formal binds the result after one designated Force;
a retained formal binds the same carrier before any explicit later Force.

These are tagged original **entry-carrier** ports. They do not change the
written Value(Function) signature or identify its endpoints with the incoming
computation's effect endpoint. The full receiving schema retains this entry
interface together with the original beta value interface and their actual
result correspondence. Its boundary profiles are typed in those original
port namespaces; lifting a beta component into `In(e,s).result` preserves its
original beta slot. The actual entry origin/receiver is shared, rather than
being reminted at rebind or at a later result.

For the fixed value signature, name its two explicit Function occurrences
`F_0` and `F_1=F_0.result`. Their complete invocation positions are
`F_0.call` and `F_0.result.F_1.call`. These are constructed from the original
Function occurrence and producer entry/body/native-return/designated-consumer
interface. Neither is an AE coordinate or a body-only effect row.

The input interfaces of `F_0` and `F_1` name **future whole carrier binders**,
not carriers already received by `rho`. At an actual call, source Call forms
its carrier and actual producer entry binds it under that entry's invocation
`u`. The source declaration's argument type exists before that event; the
actual incoming carrier and receiving occurrence do not. Retaining the full
dependent input interface does not fill its carrier field or assert a
receipt by `rho`.

The following distinctions are therefore structural source-owner facts:

| Port | Receiving event that owns a fresh default introduction |
| --- | --- |
| Current whole carrier passed to `receive` | Its actual entry `e_r`, receiver `r`. |
| Callable `F_0` and its matching returned callable `F_1` | The original `beta` value/result interface received at `e_r`, transported through its actual result edges. |
| Actual whole carrier later passed to `F_0` or `F_1` | That actual producer's later entry `e_u`, receiver `u`; preserve all antecedent carrier profiles. |
| Copy/read/capture/ResultBind/Observe of an existing view | No new receiving event; its actual typed correspondence or observation only. |

The second and third rows do different work: the received callable's
complete execution is associated with `beta`, while receipt of its future
input is an actual new source action. A request can be observed at both
ports without identifying their introductions or receivers.

## 4. The finite formation and action grammar

The grammar outputs references and instructions indexed by original source
fields. It is not a second runtime, solver, or primitive membership relation.
`Ante(i)` always means the **entire original indexed packet/interface/action**,
including profiles, K/D, contracts, witnesses, scopes, lineage and opaque
fields. It is never a default-empty profile. Ordinary atoms below describe
only the absence of a *new local introduction* on inert scalar data.

### 4.1 Actually receiving a whole carrier

Define the missing entry output at its actual source owner:

```text
Enter(rho,e,s,T,P,ann_actual)
  produces fresh boundary b=(rho,e,s,original annotation/endpoint references)
  retains Ante(T) and every original input/checking interface
  introduces default protection at In(e,s).force
  local permission there = concrete outer row of ann_actual, if present
  introduces the received result-value schema at In(e,s).result
  records the source entry receipt with its actual view/correspondence.
```

The current root is introduced because **this actual computation carrier is
being received**, independently of whether entry subsequently forces it or
retains it. This is the receiver-default instance at the owning computation
position, rather than a conclusion from the result's Function shape. A Value
formal without an outer computation annotation has no concrete permission
from that absent row. The root stays an open computation position, not a
closed effect cap. An actual retained Comp formal uses its own written outer
row and original formal/annotation identity, as in the existing
[RootComp source introduction §§2–3](2026-10-15-root-computation-profile-source-construction.md);
the same carrier remains inert until its consumer runs.

Receipt and profile introduction remain separate projections of this entry.
A subsequent receipt-only operation creates no profile. For the current
`receive` formal, the local root permission is empty; its callable annotation
and nested Ctrl rows do not supply a root-Force grant.

### 4.2 Received value/result schema

Form the following instructions from the **original explicit source value
constructors**, keeping the same receiving binder `rho` and boundary:

```text
Val(Unit or Int, p, rho) = scalar node + all original Ante references

Val(Function(P, Comp(E,A)), p, rho) =
  KnownFunctionReceive at p.call, with the direct E row's local permission;
  ResultEdge(p.result, Val(A,p.result,rho));
  FutureInput(p.argument, complete original P interface,
              on actual entry (u,e_u,T_u): Enter(u,e_u,actual_slot,T_u,
                                             actual_P,actual_ann));
  all original declaration, checking and antecedent references.
```

`ResultEdge` is an original producer result-interface edge, not an execution
or a claim that a result exists. The default at an explicitly declared
returned callable is introduced on that **matching latent result path** of
the received value. It uses the same original `beta,rho,b`, not a boundary
minted at local result binding. It is the receiving default on that supplied
value's declared future behavior. When an actual return supplies the value,
the original two-input result rule makes that latent incidence available at
the returned value's corresponding port.

`Comp(E,A)` in this Function clause is the producer's declared result
computation, so E supplies the call-position annotation policy. It is not
silently reinterpreted as returned first-class computation data, and adds no
second latent Force port. Such data requires its original separate source
introduction/elimination derivation. Here the final result is Int.

`FutureInput` retains the full argument interface, with positive Ctrl
allowance where prescribed. It emits an **actual-entry instruction** with
its own event/receiver binder. It does not execute that instruction at the
original `receive` entry or synthesize an old-`rho` incidence at a future
carrier port. The actual provider retains its original role and annotation;
the checked positive argument row cannot become a local permission for that
provider by relabelling it. A provider's independently genuine Comp-formal
annotation supplies its own local RootComp permission at its own entry.

This distinction follows from the actual carrier-binding owner: future
argument binding is performed by that source Call's actual producer entry,
with its actual carrier argument. It is not a binding of that hypothetical
carrier at the earlier `receive` entry. Conversely, if an older `rho`-marked
packet is actually supplied along a typed route, `Ante(T_u)` and transport
retain it; `FutureInput` does not prohibit an old mark at a positive port.

### 4.3 Remaining source actions

| Source action | Profile action and original owner evidence |
| --- | --- |
| Name, immutable capture, alias, environment/store read | Project the same actual binding packet and apply its original typed map. The original receiver and annotation slot are unchanged. A genuine executed read adds its actual receipt only. |
| Result / Value-entry rebind / sequential ResultBind | Combine actual returned packet and matching callee/carrier result packet by their two tagged maps, then bind that same return/world. There is no new receiving boundary at local `g`. |
| Inert Delay / value construction | Retain actual source computation/capture dependencies without execution or a receipt. A scalar introduces no latent callable profile. Existing inherited fields remain in their own packets. |
| Actual Call | Form original SourceUpperUse and full IF, delay the whole argument, open the actual callee's complete view, and invoke its actual entry. Only the actual entry executes Enter; view opening creates no boundary. |
| Existing Dir-Protect | Require the authentic ProtectedVarAt and original SourceUpperUse under the original scope; emit its one original outEff conclusion. This does not mint an omitted-formal seed or reverse protection into a provider lower. |
| Callback literal B / actual Lambda formation | Retain original expected-context role selection before body synthesis, independently generated endpoints and final inequality. Entry/default actions belong to actual later receiving events; literal formation creates no active old receiver. |
| Observe | Record fresh event and executing view/port occurrence. It introduces neither a profile nor permission nor receipt. |
| Request capture / forwarding / raw re-entry | Save crossed original views/ports/result recipes and actual pending suffix; retain profiles. Re-entry makes a fresh execution occurrence, no receipt/boundary, and never rewrites original receivers through executable-owner remapping. |
| Original declared opaque action / admitted adaptation | Retain its whole declaration/instance/typed-action reference and all original alternatives/guards. Its actual source receiving and forward actions retain their own origins; no new beta profile or semantic success is inferred from a slot or an opaque predicate. |

The last case is parametric in the original independent contract and source
action. It does not select a foreign interpretation, delete an alternative,
or assert its local law. On an independently valid source development its
original typed action supplies its own constructor/transport evidence.
Formation retains that interface before any such validity is established.
An unprovided foreign embedding/local law remains an original parent
obligation, not a reason to shrink its carrier or future domain.

## 5. Derive the concrete schema by executing formation

Apply Enter to the actually incoming carrier of the Value formal f. Applying
Val to its original signature visits `F_0`, its result `F_1`, then Int.
Its argument interfaces remain the two FutureInput nodes. The resulting
**local original-r receiving-default origins**, in incoming-carrier coordinates,
is derived as follows:

| Original origin slot | Protected local component | Local concrete permission |
| --- | --- | --- |
| `E = In(e_r,beta).force` | Actually received current carrier | none; formal has no outer computation row |
| `O = In(e_r,beta).result.F_0.call` | Selected explicit outer Function invocation | none; direct outer result row omitted |
| `N = In(e_r,beta).result.F_0.result.F_1.call` | Matching explicitly returned Function invocation | original nested result-row Ctrl |

This table is the output of the entry/value/result/future-entry grammar,
not its input. The full schema additionally contains original antecedent
packet/action references, both complete FutureInput interfaces with their
deferred own-receiver actions, and existing guarded directional-use actions.
It is therefore not an assertion that the entire profile is a three-element
set independent of those inputs.

For `F_1`'s `[ctrl]Unit` argument, the positive argument row remains an
allowance in its original complete input contract. Its future current Force
is represented by the FutureInput/actual Enter action. It is not omitted
from the schema, equated with `F_1.call`, given `r`'s local grant, or assigned
an empty antecedent image. Both `F_0`'s Unit argument and `F_1`'s Comp argument
are whole future carriers; their actual Value/retained entry behavior belongs
to the actual producer. No pure-Unit restriction is imposed on the original
independently admitted challenge domain.

There is no new omitted-formal seed at explicit f or the local result g.
Consequently neither source site gets an unconditional Dir-Protect conclusion
from annotation absence. Retain the two actual guarded rule schemas at c_1
and c_2: for each independently authentic ProtectedVarAt witness at that
exposure, use its original scope and designated outEff(U_i). This also covers
a genuinely certified antecedent produced during the source development;
it is not limited to facts known before entry. These guarded contributions
are retained, not fabricated or declared absent. Their inference targets
are not identified with AE or a complete-call observation port without the
original typed correspondence. They make no new receiving boundary solely
from a domain row and do not convert a source seed identity into b_r.

## 6. Owner inversion and the default-policy argument

**Introduction inversion, within this completed source grammar.** Every
profile witness has one original receiving/annotation/directional origin
and a finite typed forward derivation from that origin, or is the retained
original contribution of an antecedent interface/action with its own original
evidence. Receipt and Observe are not additional possible origins.

Proof is by the last constructor of the actual profile derivation:

1. Enter introduces its own fresh receiver/event/slot and the current root.
   Val's Function and result cases introduce only the original matching
   call/result coordinates for that same event and boundary. The scalar
   case has no newly received latent operation to introduce.
2. A FutureInput introduction inverts to its **actual** Enter action and
   therefore to the receiver of that future carrier. If that receiver is u,
   its new boundary is owned by u, not the earlier r. The original result
   and input source binders are different; merely knowing their type does
   not substitute one for the other. An older r incidence can still be an
   antecedent contribution and is followed through the actual map.
3. For a typed copy, capture, ResultBind or rebind, expand the indexed-image
   equation and invert the same source-tagged antecedent. Recursing yields
   its original introduction without changing its receiver or grant slot.
4. A Dir-Protect conclusion inverts to its genuine seed/use pair and original
   target; the inference rule cannot be replaced by a fresh annotation or
   Name-derived seed. Callback B preserves its actual source introduction
   and subsequent receiving actions instead of stamping a provider lower.
5. An original opaque/action reference is projected at the same whole tuple;
   its own original typed source derivation supplies the relevant case under
   actual execution validity. This uses no shape, successful query or new
   foreign law. Formation alone claims no origin theorem for an unprovided
   primitive action.
6. Request/control/receipt/Observe cases preserve profiles or record other
   evidence, so invert to their packet antecedents. Saved completion recipes
   take the current actual return on each reuse, not a stored old return.

These cases exhaust the original source constructors in the fixed graph,
their entry/return/receipt actions, and the explicit retained input/action
interfaces. No additional local introduction can be obtained by changing
port variance, observing one event twice, aliasing an endpoint or inspecting
an effect-family head. This is an inversion result for the constructed source
rules, not a global axiom declaring every desired incidence already lawful.

**Why this implements the already fixed receiving default.** The current
whole carrier is literally obtained by the receiving entry, so its root
effects have that entry's source association and default. The supplied
callable's complete execution and actual returned latent callable are obtained
through that received value's original call/result interfaces, so the same
boundary applies at their matching positions. This association is retained
when the value is returned, captured or stored. A later input is actually
obtained by a later provider entry, so that receiving action gets its own
default while every older actual packet association survives forward flow.
There is no default derived from the earlier receiver's knowledge of a domain
type alone.

This argument uses source receiving/binding/result ownership positively. It
does not derive the input case from positive variance, an absent rule or the
fact that a complete call already observes its requests. Complete observation
is a separate consequence: an input Force event inside `F_1`'s invocation can
also be observed at the r-owned `N` call view, while its carrier view retains
its own u-owned default and older profiles. Multiple observations do not
duplicate or identify the profile introductions. Local Grant retains its
existing event/view/receipt/original-slot/current-activity conditions.

In particular, a matching receiver-local Grant at the complete-call port
still suffices under the existing `not Protected or Grant` rule. Another
applicable carrier profile does not become a new veto. Thus accounting for
the carrier's genuine own-entry default does not duplicate an AE permission
check or weaken the selected local capture rule. Neither positive allowance
nor missing coverage is promoted to a Grant or a negative certificate.

## 7. Actual first and second use maps

At r's Value entry, the current carrier is forced once under its E view;
the callback components O/N remain latent. Actual return uses both original
tagged packet inputs. Removing the carrier-result prefix maps

```text
O -> F_0.call                  N -> F_0.result.F_1.call
E -> no result image
```

This removes only E's contribution through this particular result map; an
independently r-marked actual return packet is preserved through its own
input. No result is fabricated when entry requests or diverges.

The first actual Name/read supplies its genuine receipt and identity map.
SourceUpperUse/IF at `c_1` opens the original complete `F_0.call` view. O
therefore supplies first-use applicability. The first actual provider entry
receives its whole argument with its own invocation/entry identity u_1 and
preserves all incoming packet fields. No O mark is copied into that input
solely by constructing its domain slot.

At an actual first Call return z/current C_z, construct

```text
J_g = (mu_z)*W_z union_tagged (rho_1)*V_F0
rho_1(F_0.result.q) = q
rho_1(F_0.call) = undefined
```

The N incidence maps to `F_1.call` in J_g with **the same b_r, original N
admission slot and nested Ctrl operands**. O does not become that latent
incidence. Actual-value input W_z retains every independent profile/private
contract, including any matching r incidence with a different source tag.
ResultBind binds that same J_g/current world; no second boundary is created.
Name g/alias uses its original binding instance and typed identity action.

The displayed result map is the matching source result-prefix action. Any
original admitted nonidentity conversion/checking correspondence is retained
and composed at its actual source owner; it is not replaced by identity.
Apply-owned A_1 and its logical checked view remain distinct from alpha+.
Each original alternative keeps its actual return-provider/future map and
guards. An opaque alternative supplies no additional N path without its
original matching map; no missing link is manufactured from the result's
printed type. All of its actual-value and independent packet contributions
remain in the retained alternative interface.

At `c_2`, the actual source Call opens that same g view at `F_1.call`, before
actual entry Force or retained binding, through body and designated producer
result consumer. This constructs the second applicability route for N.
The later actual whole argument carrier has its own entry/default u_2;
its positive `[ctrl]Unit` contract stays an allowance at the original r-side
domain position. A genuine actual Comp-formal annotation at u_2 can provide
u_2's own RootComp permission; the checked positive row alone supplies none.
Every old r-marked input actually transported to that carrier remains there.

An event can now have distinct observations at the g complete view and an
executing carrier view. N's local Ctrl permission can be used only with its
matching original receiver r and path/receipt at the actual candidate. It is
neither a cap on incoming effects nor permission for a different owner u_2.
Fresh executable-owner resolution in a raw continuation never renames b_r;
expired receivers remain expired. Full current-world membership, OpCompat,
handler selection and whole-source Catch correctness are not inferred here.

## 8. Formation, coverage and integration boundary

Formation follows the fixed annotation/source constructor graph: Enter,
two Function nodes, three scalar value leaves (two Unit, one Int), two
FutureInput nodes and actual Name/Call/ResultBind references. It allocates
bounded local instructions and retains original dependency references.
Request/private/future carrier families remain parametric at their original
event binders; no enumeration of their values, worlds or histories occurs.
Opaque declaration interfaces retain their entire original alternatives and
actions, not merely three local profile fields.

The same coherent substitution transports the original source IDs, row
operands, shared binders and every input/result edge together. It does not
freshen a receiving boundary on Name use, promote a logical check to installed
evidence, merge outer/nested permission slots, or infer a reverse provider
edge. Each rule retains one original actual provider/world tuple. The finite
schema therefore precedes d_0; actual entry/return binders are filled by later
events under their own original validity premises.

The owner/action grammar is the changed proof method: it supplies the
previously absent positive current-carrier and deferred future-entry cases,
then derives the local support table by inversion. It does not repeat the
failed argument from annotation coordinate counts. No claim is made that
both an old-r introduction and its arbitrary exclusion satisfy all selected
laws; the conditional semantic-decision trigger was not established.

Both required reviews are CLEAN; the primary selects only the linked bounded
source definition. Independent source bootstrap/Lambda/Initial and primitive law
construction are owned by another lane; none was read, assumed proved or
reconstructed here. The actual Comp-entry case above is a formal handoff to
that owner, with actual parameter annotation and receiver retained. Native
profile construction, source-to-runtime import, full initial world, primitive
Sigma, all-source/foreign-kernel embedding, MODEL, soundness, principality
and production/F5 remain OPEN. No code or runtime representation is selected.

The reviewed actual Comp-entry and deferred receiving actions are handed
to the declaration/bootstrap owner. That integration must supply its actual
entry/annotation/map operands, without assuming foreign action embeddings.

## 9. Pins, checks, resources and commit packet

All source reads used `git show 2140859b1:<path>`; no live other-lane artifact
was read. SHA-256 dependency pins:

| Linked source | SHA-256 |
| --- | --- |
| selected first-call design | `b779ba779b66515eddb7e44ba1d0772a6853e69a1aa13a6c4528dbd8ea0852a1` |
| first-call proof | `7051eafe3221b97229a760e52639f6a5c329860175ded210e7953a77a395e42a` |
| result/Call source export | `bfec4f6aad05711b580ceac69b242de502342c31bc09fabc701ad17c583c4961` |
| typed boundary | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| typed core | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| receiver-relative default | `c544ed3c7b83686a740aa43b1db92d901de31a3b197f81f90a4c9dbdae561134` |
| annotation policy | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |
| directional rule | `f11c6594e43c29fbfdbca1638b5c548cecc12a5beb192cac743e60f022c1cc73` |
| callback B | `df4941d4c66e4f3147257024a35e7041a2c51dd528657cc80efaf3d0db62fed5` |
| contextual Function permission | `0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0` |
| source Generalize permission | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| source IF construction | `278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98` |
| RootComp source introduction | `d98e1a4e5d93f807d77c88dcf6138924e7a2b0bd2f9af031caa58bd7c79047c0` |

Checks: bounded source-owner/constructor reads, pinned hashes and local note
whitespace/fences/link checks. No Git mutations, code edits, builds, tests,
probes, measurements, network or children. At most two lightweight read
commands per batch; one verification owner remains with the primary.
Assigned wall cap: 25 minutes; CPU/RAM uninstrumented. Requested Sol/high;
observed model/effort metadata unavailable. No escalation.

Commit packet:

- Exact sole lease: `notes/theory/2026-10-16-receiving-profile-introduction-grammar.md`.
- Baseline: `2140859b13b4450303dc4873a8cdb299e59169eb`; dependencies unchanged
  by this worker, all reads pinned. Primary revalidates later changes.
- Status: independently reviewed and selected bounded source grammar/proof;
  original all-source/foreign/native/runtime/production parents OPEN.
- Checks already run: static source trace, SHA-256, note integrity; no
  executable verification. Writes stop at handoff.
- Proposed checkpoint: `research: construct receiving-owned profile introduction grammar`.
- Shared deltas accepted by the primary: record the reviewed owner/action
  completion and bounded selection, then hand off actual
  Comp-entry/default and deferred future-receiver cases to the source owner.
