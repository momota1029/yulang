# Raw continuation capture: source fields and the first support seam

Date: 2026-10-16
Status: independently reviewed complementary static characterization; original gates OPEN
Primary baseline: `ddda9bc67`; SourceCatch owners unchanged by the integrated code fix
Lease: this new progress note only; concurrent source/proof work preserved
Review: mathematical `capture_math_review` and source/authority
`capture_source_review`, CLEAN for the stated conditional source/control scope
at producer SHA-256 `5ab9bbcc33c381a89dc5de787d929ae1797b2cbed0ee917e2ac645876a88d7a5`.
Primary accepts this bounded evidence, not a full typed-source witness or
installed-interface introduction.

## 1. Objective and bounded result

Audit the actual source-generated raw continuation in the original
`receive(f:()->alpha){my g=f();g()}`. The selected response descriptor is
`alpha = () -> [ctrl] int`. The supplied f performs `ctrl.choose()`; an outer
shallow arm binds its raw continuation k, constructs zero and h, and resumes
k with h. The body of h resumes that same k with zero.

**Result:** the ordinary source equations give a terminating control trace
which genuinely passes h through the first f return and installs it as g.
The source capture contains the pending Bind suffix and its OLD typed lexical
environment, together with actual crossed computation views. It contains no
already installed `g:Value(A1)` at the initial request.

The public response/result/effect ports do not decide fixed support. The
first unresolved source field is the **complete raw-suffix contract J_raw
installed on k**, including its captured View packets and original
description/checking scopes. Existing source rules bind k at
`B_theta => J_raw`. If this installed contract freely substitutes A1, h's
ordinary capture of k gives a genuine Established path. If A1 occurs only in
a legally bound description-owned future proof, that is a different field.
This audit authenticates the owner of that distinction, but does not prove
which substitution the unfinished concrete source-capture constructor emits.
No qualified counterexample or universal no-free theorem is claimed.

The new raw-continuation projection theory being produced concurrently was
not read. This audit does not certify that construction or change source
meaning.

Governing sources: [source owner/capture rules](../design/2026-10-02-typed-source-owner-realization.md),
[typed views and full packets](../design/2026-10-02-typed-boundary-realization-draft.md),
[ordinary shallow control](../design/2026-10-02-ordinary-computation-semantics-package.md),
[operation/continuation binding](../design/2026-10-02-operation-instance-binding-package.md),
[SourceGeneralize fixed closure](../theory/2026-10-08-source-generalize-definition-and-proof.md),
and the [selected ResultBind projection](../design/2026-10-16-source-result-bind-projection.md).

## 2. Concrete source construction and completion trace

The term tree uses existing source constructors only:

```text
declare ctrl.choose : Unit -> alpha
receive(f : Unit -> alpha) = Bind(g, Call(f,Unit), Call(g,Unit))
f(u : Unit) = Call(ctrl.choose,Unit)
zero(u : Unit) = Return(0)
outer shallow Catch(Call(receive,f)):
  choose(Unit), k ->
    let zero = the closure above
    let h = closure(u : Unit) { Call(k,zero) }
    Call(k,h)
  returned v -> Return(v)
```

This is a resolved-source constructor presentation, not a claim that new
surface text was parsed, compiled or executed. The operation response is the
callable alpha, not the final Int result of the entire raw suffix. Source
operation binding retains those distinct coordinates.

Let q be the initial choose request at which the original outer handler is
eligible and selects its operation arm. Such selection is an explicit source
premise, not inferred from family equality or four native ports. The selected
handler exits and passes its RAW continuation to the arm. For the actual
saved suffix, write S(r,C) for:

```text
complete the pending choose/f result with response r in current C;
perform the pending actual ResultBind g := r;
execute Call(g,Unit);
complete receive and the raw capture root.
```

Ordinary state-threaded Bind and shallow selection give the following trace:

1. The initial `f()` suspends at q; g has not been installed.
2. The outside arm constructs zero, then h capturing the existing k binding.
3. `k h` enters S(h,C_h). The pending first f invocation returns h, producing
   its actual first-return witness z_h. ResultBind installs that same h as g.
4. The saved `g()` calls h. h executes `k zero`.
5. This second invocation enters the SAME saved suffix S(zero,C_0), using
   the current resumed state. It does not execute choose again. The pending
   result now returns zero at a distinct event z_0; its ResultBind installs
   zero and its `g()` evaluates to 0.
6. Only the inner capture root returns 0 to h's current resumer. h then
   returns 0; the outer saved `g()` and receive finish; the outer capture
   root returns 0 to the arm. The arm returns 0.

Thus this candidate does not merely escape a handler by returning h from
the arm. It actually exercises the first result and subsequent g call.
Multi-shot invocation does not identify z_h with z_0. In particular W_z_h
and its matching F_R,z_h cannot be replaced with the zero return's packets.
All current worlds, response binders, owner occurrences and receipt events
remain distinct where the source constructors distinguish them.

The control derivation uses ordinary-computation §2's two Bind equations,
§5's outside shallow arm, and typed-source-owner §2's reusable saved context
with a single root ResumeReturn. It presumes lawful response admission.
Complete alpha membership of h/zero and full raw-suffix preservation still
require their actual source typing evidence; the trace alone does not prove
source acceptance. Those obligations cannot be discharged by h's scalar
result Int or an empty support observation.

## 3. Captured-field census from positive source constructors

| Captured field | Actual source constructor/read | Support decision available here |
| --- | --- | --- |
| Response hole and operation instance | ordinary-computation §2; operation-instance binding §§2,7 | Retain the original operation, response alpha, instance substitution, current response/state and original K/D. A source local map is not re-instantiated on raw resume. |
| Pending source suffix F_g | typed-source-owner §2, lines 45–76 | F is actual defunctionalized source code plus its typed lexical environment. It contains the future result/rebind and g call, not an already installed g value. |
| Old lexical bindings and aliases | typed-source-owner §4.2; typed-boundary §6 | Retain f and every genuine stored view/reference/contract with all private free dependencies. No existing Mono is reclassified as an own-component closure. |
| Source code labels, original result/check positions | typed-source-owner §2; selected ResultBind projection §2 | They are actual static positions, not automatically dictionaries containing the value assigned to Desc(A1). Their logical typing dependencies must nevertheless be retained. |
| Captured Owner and pending completion fields | typed-source-owner §2, lines 81–143 | Preserve nested completion and current owner resolution. No store snapshot, receipt replay or resurrection of a receiving boundary. Completed children are not re-executed. |
| Crossed View(v,p,K) | typed-boundary §4, lines 441–459 | Preserve original typed packet and port; each resume gets a new executing occurrence under the resumer's ambient context. Neither owner resolution nor a flat control template may rename this packet. |
| Each View's complete `(v,t,chi,K,D,L)` | typed-boundary §6, lines 704–760 | Profile and dependency incidences use their authentic typed maps; K remains the original shared predicate ledger, and L retains original identities. Exact free descriptor support of these original fields is the remaining source-introduction input. |
| ForwardHandler | typed-source-owner §§2–3 | Retain only actual crossed forwarding wrappers. The selected outer shallow handler contributes no wrapper and is not restored by either resume. |
| k's installed response/raw-suffix interface | operation-instance binding lines 77–88,311–317 | k is bound at `B_theta => J_raw`, with the COMPLETE raw suffix, not the arm's output or the public Int port. Its exact output telescope/substitution is decisive. |
| h's captured k binding | ordinary Lambda capture; SourceGeneralize §3.3 | A genuinely installed Mono(k,Contract_k) is external to this later closure capture. Its whole free contract is Established; a new raw/proof split cannot silently discard a free contract parameter. |
| Later actual g entry | selected ResultBind projection §§2–4 | At Return, preserve the actual packet and private contracts, with hereditary A1 membership in its proper logical proof component. That later introduction supplies no retrospectively installed g field at q. |

The context may be displayed as an outer receive-owner context containing
`Bind(K_f,F_g)`, where K_f retains the actual unfinished f/consumer completion
and the crossed View nodes in their original order. This display does not
commute View past Bind: `Bind(View(...),F)` and `View(...,Bind(...,F))` have
different executing scopes (typed-boundary §4, lines 454–457). The census
therefore does not erase nonidentity views or infer their order from owners.

## 4. Exact candidate fixed path and the single missing source law

The strongest candidate path is:

```text
actual returned h
  -> h's actual captured binding k
  -> Mono(k, Contract_k)'s installed complete rawSuffix J_raw
  -> captured View packet / dependent Bind continuation interface
  -> original A1, IF that occurrence is a free installed parameter
```

SourceGeneralize §3.3 and §5.1 would follow this ENTIRE path if it is real.
The selected ResultBind projection neither adds nor removes support already
present in Ret_z. It cannot neutralize this path by placing a separate
membership proof beside the fixed field.

Conversely, the occurrence `g:Value(A1)` in the hypothetical continuation
typing does not prove the final edge. Future Check/EventProof witnesses can
have an A1 parameter without being actual installed Mono/Shared evidence.
Nor do source-position t, raw code, a reserved runtime cell, or a pointer to
the original description graph establish a chosen A1 dictionary. An arbitrary
schema H(delta) would supply no actual installation law here.

The single missing source input is therefore the **SourceCatch/capture
introduction's complete installed Contract_k telescope**, with its actual
substitution into J_raw and classification of each captured View/lexical
field versus its description-owned future proof. It must tell whether A1 is
free in a real installed field or retained only at its original logical
description/proof binder. This is narrower than asking for all private-field
semantics. It concerns the actual continuation constructed from this source
Bind/Call/Catch, whose code and prior environment are known.

Typed-source-owner takes a decorated descriptor graph Omega as input
(§1, lines 20–33). Typed-boundary §4, lines 390–398, explicitly leaves
elaboration of executable typed views from raw source as an input obligation.
Their transport laws preserve the stored packet once supplied; they do not
provide this source-capture field classification by erasure. An explicit
constructor may complete that owner under existing permission, retaining
the original complete J_raw and all observable views. Replacing J_raw with
the public Function4/Int result or rewriting an independently fixed foreign
kernel would not be that completion.

## 5. Native/runtime owner cross-checks and limits

Native SourceCatch at `candidate_source.rs:770–805` retains the original
scrutinee endpoint/effect, declaration, arm occurrence and continuation
binder component. `candidate_effect.rs:826–883` constructs paired response
interfaces in ONE declaration environment, then a raw-k Function whose result
is the original scrutinee and whose RE conservatively includes its FULL
effect. Entry effect is separate. This correctly distinguishes alpha from
Int; it supplies no captured typed-environment or installed J_raw telescope.
That observation is a source/native correspondence boundary, not a
missing-field-implies-loss argument.

The implemented control path corroborates the concrete pending fields:
`runtime/machine.rs:1002–1070` captures ordinary frames, owners, forwarding
handlers and executing views; `continuation.rs:13–43` retains the declaration
and original event. `Frame::Local` stores block/next/environment/cell/recursive
(`machine.rs:212–218`). `begin_local:1528–1556` reserves an empty cell before
the initializer, while the Return transition `:828–852` installs the received
value/view and extends the environment. The reserved cell is not evidence
that source g or a Mono(A1) contract already exists at q.

Current runtime receiving views retain positive RootComp evidence and unknown
coverage (`receiving.rs:42–83`); they are not the complete source packet
theorem above. More decisively, raw response checking at `machine.rs:565–577`
calls `primitive_matches:930–939`, which supports only Unit/Int/Bool/Str.
Thus the current runtime path cannot authenticate execution of this callable-
response example. No runtime experiment was attempted, and this limitation
is not a source rejection or a new semantic restriction.

## 6. Outcome, next action and verification

Established bounded evidence: the actual control completion trace, absence of
an installed g at capture, full positive-constructor field census, and the
precise installed raw-suffix-contract path which a projection must classify.
Unestablished: the final free A1 edge, complete typed acceptance of this
candidate, universal A1 eligibility, native copy applicability and all original
FIRST-RESULT/soundness/principality/production parents. No gate is closed.

Recommended next action: consume the independent source-capture constructor
at exactly Contract_k/J_raw and its captured View/Bind substitutions. Require
it to handle h's subsequent ordinary capture of that same k binding. If a
free A1 occurs in an actual installed contract, apply the existing fixed walk;
if it belongs to the proof region, exhibit its original binder and legitimate
scope. Keep both same-z packets, original xi, all private contracts, pending
responses and compatible future configurations unchanged.

Checks: bounded `rg`, `nl`, `sed`, `cat` and SHA-256 reads; one leased note
creation. No compiler execution, test, build, executable probe, Git operation,
children, code or shared-record edits. One leaf within the 20-minute ceiling;
CPU/RAM unmeasured. Static source rules are the evidence, with their stated
decorated-input and response-admission premises; no checker/oracle is claimed.
The concurrently produced raw-capture proof was not read.

Frozen input hashes:

```text
5cbd8110736ee4d43e0c65460fa9ecf700228bfdbe9fbaa7642ea0302d86f1aa notes/design/2026-10-02-typed-source-owner-realization.md
1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb notes/design/2026-10-02-typed-boundary-realization-draft.md
ee3f5cf8185d516775b8915b0fda6dbb07390c3ecad7ac028eb5995581dff917 notes/design/2026-10-02-ordinary-computation-semantics-package.md
1eb2cbdb49368b0839d839d6a5e72698bb06252813b00200098e70371645c7c9 notes/design/2026-10-02-operation-instance-binding-package.md
e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240 notes/theory/2026-10-08-source-generalize-definition-and-proof.md
36592df8bc0d0315bbef836438391559ae6e23bfcd44074d7d542c9ea91912a2 notes/theory/2026-10-16-first-call-result-binding-projection.md
f943e28a57e1a18cb22ec3e63a892f08711a3422293a240b168ea6dba5a082aa notes/design/2026-10-16-source-result-bind-projection.md
efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38 crates/yu-solver/src/candidate_source.rs
44ee33d077c61c9dea6359299ca49218afc6ca1b5b6807690838309b25c731c9 crates/yu-solver/src/candidate_effect.rs
04024174d88223e252e1d093eaee96c17d9f43d4d32bea5c41631017c9da208c tools/inference-playground/src/runtime/machine.rs
194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3 tools/inference-playground/src/runtime/continuation.rs
5443c8ca55e58a37b6d003cf5b2985214d37776094f02637adfbe30200cc36bd tools/inference-playground/src/runtime/receiving.rs
```

Commit packet: sole new path is this note; baseline `ddda9bc67`; no dependency
edits. Independent review pending; no self-certification. Proposed checkpoint:
`research: audit raw continuation capture and installed suffix dependencies`.
Shared records are synchronized by the primary after adjudication. The
producer's pending-review statement above is historical checkpoint metadata;
current review status is recorded in this header.
