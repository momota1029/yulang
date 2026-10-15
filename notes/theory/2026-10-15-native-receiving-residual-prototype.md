# A source-qualified receiving/Catch residual prototype

Status: research-only constructive finite source-completion proof and proposed
native consumer contract; independent finite-proof review passed; native implementation OPEN
Production baseline: `266da3dd6cf73b4b6267919384cce9389d653f46`
Dispatch HEAD: `cdfdb58bb244fecf0c895a6a1d65b2bdee06548c`
Lease: this new note only; leaf; no production writes, delegation or Git mutations
Method: derive the exact finite source control/receipt/observation schema, prove
the suppression predicate for every completion it represents, then locate its
first actual native output/consumer

Independent review: `callback_feasibility_review` checked the original finite
source theorem and the pre-admission consumer contract at artifact SHA-256
`7e33df36efe40f7914170f0d1443dc2cedc4e81c1fd5124898f16fbba6a69f5e`
with no findings. This closes only the qualified source lemma, not its native
implementation or the universal parent.

## 1. Frozen original invariant and bounded claim

For every originally supported source Catch H, every contribution x represented
on its scrutinee-to-result edge e, and every original joint source completion w
represented by x at e, suppression requires the **same** event, typed path,
receiving owner, current activity, matching/selection and continuation witnesses.
At the actual yielding boundary its candidate h must satisfy

```text
Active(h,C) and Active(owner(h),C)
and Covers/Match/OpCompat for that original event
and (not Protected(q,h,C) or Grant(q,h,C)),
```

and the operation must actually be selected/consumed on this Catch edge.
Suppressing x must preserve other contributions, operation/value-arm effects,
raw continuation semantics and all source/provider/attachment/residual lineage.
No endpoint equality, family equality, source spelling, ScopeState or lexical
Lambda membership substitutes for those witnesses. One source assignment
`xi=(ν,K,D)` and original binder/quantifier scopes are fixed throughout.

The parent remains universal over its original source domain. This packet proves
one **source-qualified call-use subcase**, not generic suppression on relay's
generalized interface. It also constructs a no-suppression control and reuses
the established expired-owner falsifier. This experimental envelope neither
rejects other supported source nor closes Value(Function) callback B, complete
Call, all-source hygiene, soundness, principality or native runtime realization.

At the native boundary, an unresolved private residual edge is retained before
propagation, with its dependent result unpublished. It is never implemented by
sending the unconditional bound and later retracting it. This is the primary's
selected provisional consumer contract; it is not a new whole-compiler rollback
or source-rejection requirement.

## 2. Existing authority and actual retained source operands

Authority/reused results:

- Annotation integration `notes/design/2026-10-10-annotation-effect-hygiene-integration.md`
  §§1/1.1 explicitly selects the Computation relay example returning 1 and
  allows an additional write effect, which must remain outward.
- `notes/theory/2026-10-15-root-computation-profile-source-construction.md`
  §§2–4 derives RootCompSchema/ReceiveComp from actual parameter syntax and
  original Name/consumer/Delay/Argument maps; §§5–6 supplies the independently
  reviewed expired-owner obstruction to lexical-only deletion.
- `notes/theory/2026-10-15-computation-formal-permission-construction.md`
  §§2–4 derives RootPermit/NamePermit and records the total-arm, actual-owner,
  original-raw-continuation obligations of the paired consumer.
- `notes/theory/2026-10-15-computation-forwarding-preservation.md` §§2–4
  establishes the positive generated-root forwarding invariant with original
  views, current owners and pending suffixes. It is not a native execution claim.
- Typed boundary `2026-10-02-typed-boundary-realization-draft.md` §6 gives
  Receive/Observe/Path/Inc/Grant/Visible and receiver-local grant despite
  independent inherited protection.
- Typed core `2026-10-02-typed-computation-core-elaboration.md` §§3,6,9 gives
  whole-argument Delay, Computation retained entry, designated root elimination,
  operation's native-return/declaration-result consumer, and state-threaded Bind.
- Source owner `2026-10-02-typed-source-owner-realization.md` §§2–4/6 gives
  actual owner/handler lifetimes, ordered matching outside the selected image,
  raw re-entry and the fact that receipt replay does not rebind old boundaries.
- Top-level inference principles §§1/1.1,3–5 require construction-supported
  native inference and necessary private failure safety.

Use the already selected source, with exact supported pattern syntax:

```yu
act signal:
    our ping: () -> int
my relay(thunk: [signal] int) = catch thunk {
    signal::ping(), _ -> 1,
    v -> v
}
my answer = relay signal::ping()
```

The checked-in controls `candidate_computation_laziness.rs` use the same
retained formal/Catch form with `io::tick(p)` and a discarded continuation;
they also retain the two raw-resumption controls. These are syntax/admission
locators, not executions or proof premises. No control was run here.

Actual constructor operands at the pinned production source:

| Source owner | Retained information used by the construction |
| --- | --- |
| `yu-hir/src/module/local_source.rs::catch`, 939–1007 | Original Catch index, exact scrutinee, ordered original arms, resolved operation declaration, Unit payload pattern, wildcard continuation, original arm body/binders. `_` is explicitly a Catch wildcard here. |
| `candidate_source.rs`, 566–578/699–715 | Original Lambda/parameter/annotation, Computation role, formal registration and FormalEntry action. |
| `candidate_source.rs::initialize_candidate_source_levels`, 1175–1198 | Registration-to-original-parameter validation and actual entry-effect row e_t; the native root remains a Value term, not a receipt. |
| `candidate_source.rs`, 913–932 | Direct original parameter Name; FormalNameEffect links its computation effect to that registration's entry effect. |
| `candidate_source.rs`, 738–783/843–859 | Exact Catch operation/continuation inputs; current unconditional scrutinee slot-51 inclusion and separate arm slot-51 inclusions. |
| `candidate_effect.rs::candidate_formal_entry_annotation`, 1170–1183 | Actual annotation/family/registration operands; concrete permission is currently retained but has no receiving-entry implementation. |
| `candidate_effect.rs::candidate_operation/signature_value`, 800–819/1466–1689 | Resolved declared operation/source origin and nominal family; signature is not itself an event occurrence or active owner. |
| `candidate_effect.rs::candidate_catch_operation`, 820–884 | Original scrutinee and declaration, exact payload/continuation fields; used raw continuations retain the unfiltered original scrutinee effect. |

Unit arm coverage follows from **both** the retained Unit pattern and the
resolved declaration's Unit argument. Empty parentheses alone do not establish
payload coverage. The operation arm is first for that exact operation, has no
guard, returns Int, and discards its raw continuation by the actual wildcard
constructor. The value arm is a separate original source route.

## 3. Derive a finite source-owned receiving/exposure schema

Freeze this original complete call use a, its actual provider expression
`signal::ping()`, relay L/formal t/annotation a_t/root row position p_t,
the original Catch H, and one joint xi. The schema has the following source
nodes. Names r,b,h,o,q below are **bound by those source nodes**, not supplied
arbitrary owner/activity premises or allocated live objects during inference.

| Node | Owning source constructor and generated consequence |
| --- | --- |
| A0 | The outer call evaluates relay, then constructs its whole argument D as Delay of the original ping application; this executes no ping code. |
| A1 | Actual relay Invoke introduces fresh owner r and its ordinary return delimiter. Retained entry binds D without forcing it. RootCompSchema from `[signal] int` instantiates fresh b=(r,t,Γ,endpoints), Γ protects RootComp and admits exactly signal; Receive(r,t,V_r,Id) retains the original incoming packet plus this source-tagged b. |
| A2 | Relay's actual first body constructor installs the shallow Catch h under current r. There is no preceding body effect, guard or other control transfer. |
| A3 | The actual Name thunk loads t's original received V_r into output view V_n by identity RootComp transport; the source load supplies Receive(r,read-slot,V_n,Id). Normalize on the Computation tag selects elimination of this exact RootComp. |
| A4 | Executing that root opens D and reaches the original ping application. Its Unit argument is inert/pure; actual operation invocation o creates its declared request thunk, returns natively, then its declared result consumer emits its sole signal request q. No unrelated family or earlier request is generated by these source nodes. |
| A5 | The request is exposed through this same executing V_n.RootComp: Observe(q,V_n,RootComp). Identity Name/Delay/root-consumer paths carry b's original profile there, with the same r receipt; q's source/operation/response/K,D and pending suffix remain original. |
| A6 | At q's actual yielding boundary h and r are still active. The exact signal/Unit operation arm is first and total, Grant from b is local to r, and ordered source matching accepts that arm. This consumes q at this Catch. |
| A7 | h is removed as selected shallow handler; its wildcard discards the captured raw continuation. Arm body returns original literal 1 outside h. This result reaches relay's original completion; no discarded suffix executes. |

This is a finite schema with symbolic activation/event binders. Repeating the
source call instantiates fresh r,b,h,o,q through the same constructors; it does
not copy activity facts from an earlier invocation. No new runtime receipt
primitive is postulated: A1 and A3 are the existing source entry/load rules.

The incoming packet can contain additional valid source-tagged profiles; A1
does not erase them. The newly instantiated local signal grant is sufficient
under typed-boundary §6's no-origin-veto rule. This does not grant signal at an
unrelated path or in a nested helper with a different receiver.

### 3.1 Universality for the completions represented by this source use

Consider every finite execution/completion of the **actual assembled source
nodes A0–A7**, in any valid ambient typed owner context and every xi permitted
by the original source declarations. The actual source argument/provider and
the source continuation route are fixed; an arbitrary other provider is not
silently substituted for that expression. This is a per-source-use proof,
not a claim that relay's open formal row denotes only this provider.

Induct along the source constructors rather than assuming the desired activity:

1. Before A1 there is no relay activation. Entering A1 freshly establishes r
   and b; retained entry executes none of D. Existing source contexts outside
   this call cannot already contain r's future raw continuation.
2. Between A1 and A4, the only operations are Catch installation, direct
   immutable Name load, designated root opening, Unit construction and the
   declared operation's carrier production. Their source rules emit no request
   or abrupt owner exit. Thus neither search unwind nor raw re-entry can end r
   in that interval. A normal return cannot precede its uncompleted body.
3. The declaration's actual first yielding event is q of signal, not an
   arbitrary member of an inferred row. A3/A5 generate matching receipt and
   observation for the very same V_n/RootComp. Hence

   ```text
   Path(q,r,b,RootComp),
   Active(h,C_q), Active(r,C_q), Active(b.receiver,C_q),
   Inc_Cq(q,h,b,RootComp), Protected(q,h,C_q), Grant(q,h,C_q).
   ```

   The activity follows from steps 1–2 and h's installation, not from a
   ScopeTransformer, static Lambda id or historical receipt.
4. No source handler lies between this root yield and h inside relay; the
   operation's native invocation has already returned. Extra ambient handlers
   are outside h. Grant discharges inherited protection for this exact local
   candidate. Its exact nominal operation and declaration-typed Unit payload
   match the first total arm; there is no effectful guard/pending match. Thus
   `!Protected || Grant` is true, matching selects this arm, and q is consumed.
5. The wildcard exposes no raw continuation to the source program. Therefore
   no later completion of this source use can re-enter the discarded suffix,
   reinstall h, or reach a second q through it. The pure arm introduces no new
   event; normal/abrupt ending after consumption cannot retroactively change
   the already established yielding-boundary selection.

These cases exhaust the source control paths. A prefix before q contributes
no hypothetical event to suppress. For every represented q completion, the
actual same-event selection condition is established. If a primitive's local
contract or a source dependency admits another pre-query effect/control path,
this enumeration no longer exhausts its completions and cannot certify
suppression. Source reachability forbids inventing an externally accessible
raw continuation of r before the source has produced one.

**Bounded theorem, pending review:** the scrutinee contribution generated by
this original direct ping application can be suppressed on this original H
edge for every completion of that qualified assembled use. The source result
is the selected arm's 1 with no escaping signal from q. This matches the
explicit user decision, but the proof above derives its receiver/path/control
premises instead of using that expected result as a premise.

## 4. Controls, invalid generalization and exact preservation

### 4.1 A direct unhandled operation

Add resolved `act write: our put: () -> int` and use `relay write::put()`.
The declaration/entry/Name path is the same with its own original q_W.
RootComp default protects this associated write, but Γ_b admits signal only.
The Catch has no write operation arm, so Covers/Match for q_W fails and no
local selection occurs. The source handler forwards the same q_W with its
original pending continuation. The annotation is open; no `[signal]` cap
rejects write and no signal permission deletes it. This derives a Forward
case for that source contribution, independently of family-row coincidence.

If a signal arm itself emits write, that event is a separate arm computation
outside the selected h and reaches the result by its ordinary arm-effect
edge. It is not in the scrutinee residual. Likewise a value arm emitting
signal is unaffected by suppressing the scrutinee's q. Independent
same-family contributions retain their own source/event witnesses.

### 4.2 Why the generic relay edge is not certified

The reviewed root-profile note §§5–6 gives an admitted source completion with
a **body pause before the direct Name**. An outer keep boundary remains live
and protects io without granting it to relay's new owner r'. The original
relay receiver r has expired. Raw re-entry installs a fresh io handler under
r' and the actual later Name load gives its matching receipt, but it does not
replay the old entry or rebind b_r.receiver. The exact query has

```text
owner(h')=r', Active(r)=false,
Inc(q_I,h',b_keep)=true, Inc(q_I,h',b_r)=false,
Protected=true, Grant=false, Visible=false.
```

This already proved source completion refutes suppressing merely from
`same Lambda + annotation + direct Name + total discard arm`. It does not
refute §3's assembled direct-provider, no-pre-query-yield source schema.
Nor does a signature family list prove A2–A4's control exclusion for an
unknown argument. The earlier argument-pause report with unproved post-resume
receipt is not reused as a counterexample.

A selected shallow handler also stays absent on raw resumption. If an arm
exposes/invokes k instead of discarding it, the remaining source suffix and
its unfiltered original scrutinee effect are retained. The discard proof A7
then fails; suppression of q alone is not permission to suppress the events
of k or its future handler/view context.

## 5. Smallest native constraint-consumer contract

The current source collector emits the scrutinee effect inclusion at
`candidate_source.rs:844` using local slot 51. Arm-effect inclusions at
`:852–853` use the same slot number on their **own original arm occurrences**.
The prototype replaces only the scrutinee-to-this-Catch edge with an owned
residual action/template. It must not keep the unconditional inclusion in
parallel and must not filter arm edges or the original formal/entry row.

Retain/refer to operands the phase actually knows:

```text
original H source index/occurrence and original edge cause;
original scrutinee Name and its exact Parameter(t) registration;
original Lambda/annotation/row position and resolved permission family;
ordered original operation/payload/continuation/arm source descriptors;
raw scrutinee effect position and this Catch result-effect position;
original call/use/provider source and source-completion/control schema;
all source relation/dependency/continuation lineage carried jointly.
```

These are references to retained source constructors, not a global inferred
permission bit or proof reconstructed from equal endpoints. The finite A0–A7
schema is produced by matching those actual constructors and declaration
signatures; its symbolic owner/receipt/observation nodes are justified in §3.
For an open/generalized source formal it remains a parameterized residual
template until its actual provider/use/control completion is represented.
The direct ping source proof cannot be applied at collection of relay's
generic body merely because answer later happens to call it.

In particular, deleting slot 51 and capturing only the remaining row/bound
graph would lose the input-to-result dependency and could export a spurious
empty result effect. Capture and every FreshUse must retain/remap the latent
residual template's original input/output/source dependencies jointly, or the
affected connected source component must remain private until its actual
source-call assembly is available. An open private source template is not a
completed callee result. Do not wait for a finalized callee result to discover
the very argument needed to finalize it: the immutable source contains the
actual resolved call/argument independently of solving. A provisional assembly
can join those exact source nodes before interpretation, without choosing a
typing or equating their value endpoints. No proof of a general incremental
publication/suspension algorithm is claimed here.

For each **original source contribution with all its represented origins**
on this edge, the consumer has three possible results:

| Result | Required justification and native action |
| --- | --- |
| Suppress on e | Every represented completion is covered by the same-event source derivation in §3, or an independently justified extension. Admit no positive outgoing copy of that contribution on e; retain the original raw contribution and consumed-source lineage. |
| Forward on e | Source construction establishes no local consumption, as in §4.1. Admit the ordinary contribution-to-result bound with its original provenance and pending control, only on this edge. |
| Pending e | Some event/path/owner/activity/matching/completion coverage premise is unresolved. Retain the residual continuation and dependencies without admitting the unconditional bound or publishing the dependent result. Independent meaningful source/solver work may continue. |

The universal condition is over every completion represented by this qualified
contribution, **not** separate existential marginals. If native interning has
merged several source origins at one endpoint, take their joint source-tagged
coverage; one proved origin does not license omitting an unproved origin.
Alternatively keep the source residuals distinct so their outputs join only
after the per-origin consumers. Fresh uses retain separate original-use/owner
schema binders even when a nongeneric row is shared.

This yields a monotone constraint-emission contract: no already propagated
bound is withdrawn. New origins/lower contributions have their own source-
qualified residual admission; they cannot silently enlarge an already
certified origin's completion set. If a dependency changes that certified set,
the owning component must be invalidated/unpublished before any affected
certificate is used; the prototype must not cache a stale universal result.
No speculative solve or alternative-typing retry is needed.

Raw continuation constructors retain original E_S, as current
`candidate_catch_operation` does at slot 65. That route is not replaced by
the filtered Catch result. Operation/value-arm effects and one-shot binding
effects remain ordinary independent source edges. Suppression changes neither
an incoming carrier nor the operation's nominal family or stored K/D.

## 6. Exact current implementation gap and executable next cut

The first missing owning output is at the actual Computation entry:
`candidate_formal_entry_annotation` has all RootCompSchema operands but does
not emit the source-owned retained-entry/received-view instance schema.
FormalNameEffect emits the authentic scalar e_n=e_t linkage, while the native
pair/row does not itself supply the same received view and current-owner load.
Catch formation retains source arms but emits only the unqualified scalar
slot-51 edge. ApplySourceInput retains actual argument source indices; joining
those to the qualified entry/Name/Catch source schema is the next consumer's
responsibility. ScopeState and scoped observation logs do not fill this gap.

The finite proof makes an actual provisional cut possible: construct this
root residual template from the actual FormalEntry/Name/Catch nodes, retain
it before slot-51 propagation, and instantiate/consume it only through the
exact source-call/provider assembly covered by A0–A7 (or the Forward control).
For the smallest prototype, assemble that whole connected source use before
admitting its affected edge; this avoids pretending the existing graph capture
already preserves a new residual template. A later modular capture/FreshUse
implementation needs its explicit preservation proof.
Unknown assemblies remain Pending, with production/cutover gates OPEN. The
primary owns authorization, representation choice, implementation and checks;
this note neither edits code nor certifies an absent consumer. A source observer
that merely prints r or the family is insufficient: the actual outgoing bound
must be gated by the proved schema before admission.

One next action: primary assigns the provisional source-owned residual
constructor/consumer on those exact owners, with the Suppress/Forward/Pending
contract and the root note's expired-owner falsifier. This consumes the finite
invariant; another general transport lemma or unconditional family filter
would leave its actual consumer untouched.

## 7. Dependencies, checks, resources and commit packet

SHA-256 frozen at this pass; source basenames are under `crates/yu-solver/src/`:

| Dependency | SHA-256 |
| --- | --- |
| candidate_source.rs | `90db34173d366ed826b34492da0fb2f1c5422b1b41e43fcda14892ec8415e7ab` |
| candidate_effect.rs | `deee5a0892b02bc9ee23a1f2a35c76175094c558ed7dfb2cf55a7e115ac54225` |
| candidate_context.rs | `9f71c8c40d6850bffccb27d7393bf6219f0ceca5cf1fe1e738073ea943706083` |
| candidate_scope.rs | `9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a` |
| candidate_scheme.rs | `436687cbc8c4ea372d0066f3f8a8e46cfc28223ade163f49864cd3c5039c60e6` |
| shadow_apply.rs | `270ee70b331e4095f404fafafdf0731b57dd451c130cdf251aea2b5944d7cc6c` |
| lib.rs | `b0f7778934a37ec9c642f7e6232cb61e37a1b0768f6af92556cf873f6b2a69f7` |
| `yu-hir/src/module/local_source.rs` | `53e3b324cac9364ac7313e44f9cc739d876427c9018df2a22e5a88119c46c1f9` |
| Root computation profile source construction | `d98e1a4e5d93f807d77c88dcf6138924e7a2b0bd2f9af031caa58bd7c79047c0` |
| Computation formal permission construction | `7766aff08cedde1ebc796b8927cd1d44f459df72a632e0c0d35d4bfcd28d335e` |
| Computation forwarding preservation | `d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79` |
| Typed boundary | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| Typed core | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| Typed source owner | `5cbd8110736ee4d43e0c65460fa9ecf700228bfdbe9fbaa7642ea0302d86f1aa` |
| Top-level principles | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| Computation laziness fixture | `df5d567dca1b8d0569e1afacfda0992baf11b848205a0c7c38c449609270e5b2` |

Commands: bounded static cat/sed/rg reads and SHA-256, read-only Git HEAD/status,
apply_patch on this lease, final whitespace check/hash in handoff. No production,
tests, expectations, shared records, Git index/refs, builds, executable probes,
measurements or children. One bounded static proof pass within the assigned
25 minutes, zero heavy processes/samples; RSS/exact elapsed time unmeasured.
Requested normal Sol/high; observed effective model/effort unknown; no Astra
or reload claim. Independent review/verification/integration remain primary-owned.

Commit packet: exact lease
`notes/theory/2026-10-15-native-receiving-residual-prototype.md`; production
baseline `266da3dd6cf73b4b6267919384cce9389d653f46`; changed dependencies none;
hashes above. Research-only bounded source theorem/prototype contract,
independent review pending; native and original universal parents OPEN.
Proposed checkpoint: `research: derive a source-qualified receiving Catch residual gate`.
Shared-record delta for primary/curator: record A0–A7's universal per-use
Suppress case, independent write Forward case and generic expired-owner
limitation; assign actual entry/Name/Catch residual output, keeping source
coverage/native/cutover separate. No shared record was changed by this leaf.
