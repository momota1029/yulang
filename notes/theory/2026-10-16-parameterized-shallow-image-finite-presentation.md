# Parameterized shallow images: core equations and first missing local rule

Date: 2026-10-16
Packet P2; producer `/root/runtime_source_supplier_proof`, resident leaf.
Baseline supplied by Luna: `0814021eb287edbd65ca6c1b25096ff91691f901`.
Status: unreviewed conditional constructive derivation for the proposed grammar.
Full finite-image feasibility: BLOCKED at the unspecified OriginalFrame action;
opaque foreign continuation application is a separate uncovered instance.
No impossibility result, semantic adoption or original parent promotion.

## 1. Frozen statement, scopes and exclusions

For EVERY finite well-typed L/H in the exact [r2 grammar](../design/2026-10-16-primitive-interaction-graph-proposal-r2.md),
the requested full theorem would construct finitely many permitted positive
Image defining equations, with interpretation equal to that same proposed
computation followed by the SAME shallow H. Cover Return, Request/raw resume,
Bind/Ref, union, correlated conjunction, original scoped existential, explicit
prefixes and all declared foreign/frame cases. Dynamic suffixes are operands,
never label-specialization keys. Keep original dependent environments/binders,
one xi=(nu,K,D), admitted joint carrier/response/world/history fields, same
actual providers and output-dependent futures. H and exact U remain unchanged.
Rigid/universal source binders remain external and pointwise, and original
existentials stay at their actual introduction. No independent marginal witnesses.

This packet constructs direct core clauses, then stops at an unprovided local
body. It does NOT replace the full target with a foreign-free source domain.
The described emitter returns BLOCKED when a permitted original action lacks
its defining rule; a partial presentation is not called that input's image.
No missing Image, foreign-image, FrameImage, arbitrary relation-application
primitive or desired U-membership oracle is assumed.

The [A2-R2 withdrawal](2026-10-16-primitive-interaction-graph-a2-r2-withdrawal.md)
remains effective. REUSE r2's dynamic Kont/Raw, original live-Cnow resume, local
common-preimage M2 and explicit-prefix M3 rules. ADAPT them into actual relational
bodies below. REJECT finite-Run-implies-finite-Image, infinite stack memo keys,
independent image/intersection and cyclic-reference-as-prefix introduction.
R5-D1 is scheduling context, not a substitute mathematical premise.

The original [image-discharge target](2026-10-16-image-demand-original-alternative-discharge.md)
§§1,3 is a scope guard only. Full original T_alpha coverage/admission preservation,
effective exact-U/A-B discharge, source/native correspondence, implementation,
architecture approval and production remain OPEN. This conditional candidate
work neither reconstructs the old Z declaration nor narrows its alternatives.

## 2. Relation syntax, typed operands and finite labels

Use source contracts §§2.1–2.2,3.7,5.3: finite whole-tuple conjunction/union,
original scoped binding, renaming, independently specified constructor relations,
registered references and positive recursion. Each new predicate needs a BODY.
The constructor-image label does not license shallow Image as a primitive.

Dynamic types are exactly r2's Env_l, Current, Kont and Raw, with its
Pending/Return/Request observations. There is no new universe of predicates.
Membership witness w, whole preimage y and handler witness d are the existing
r2 evidence parameters at their original scopes, not new existential source
types. Frames carry the same dependent lexical references, not store or active
handler snapshots. All original guards and private contracts remain intact.

Emit I_l(e,C,k,a,J;o) and O_l(e,C,a,J;o) for each static graph/handler label l.
I is the image computation up to H with full inside suffix k; a is the outside
suffix after the boundary. O executes outside the selected activation. J is
the original joint telescope/history, not a new product of independently
chosen fields. Also emit typed RI/RO return dispatchers, Append/Resume and
paired original-preimage versions PI_l and explicit B_H/B_O clauses for Join. These are finite
PREDICATE LABELS, not a new dynamic control sort. Initial empty suffixes use End.

A BindFrame_b(eb,k) has the original `[v,Cnow,eta]` telescope and body label b.
Its saved eb retains every original free dependency. Append requires the actual
output-dependent endpoint of its first suffix to match the second's input
under the original typed map, not merely equal printed types. OriginalFrame_f
has its original type, but that type alone supplies no operational body (§7).

## 3. Direct positive defining clauses for covered constructors

All clauses below carry the SAME nondisplayed original typed operands/guards.
An iff abbreviates a positive defining equation; multiple clauses form a finite
union. Observation equations match/construct existing Return/Request/Pending
constructors. z denotes the entire actual return packet, including its own
value, C, evidence and actual provider/future fields.

### Return and ordered Bind suffix

```text
I_Return(v)(e,C,k,a,J;o) <-> RI(z(v,e,C),k,a,J;o)
O_Return(v)(e,C,a,J;o)   <-> RO(z(v,e,C),a,J;o)

RI(z,End,a,J;o)
  <-> O_value-arm-H(eH extended by THAT z,C(z),a,J;o)
RI(z,BindFrame_b(eb,k),a,J;o)
  <-> I_body-b(eb extended by THAT (v(z),C(z),eta(z)),C(z),k,a,J;o)

RO(z,End,J;o) <-> o=Return(v(z),C(z),actual Future(v(z)))
RO(z,BindFrame_b(eb,a),J;o)
  <-> O_body-b(eb extended by THAT (v(z),C(z),eta(z)),C(z),a,J;o)
```

RI does not run H's value arm before its inside suffix completes. The arm's
own Return supplies its output provider/future; it need not be z's provider.
These equations define Image outputs directly, not via an unknown ImageOracle.
No identity-pop clause for OriginalFrame_f is inserted.

### Bind, Ref, whole alternatives and original existential

```text
I_Bind(P,b)(e,C,k,a,J;o) <-> I_P(eP,C,BindFrame_b(eb,k),a,J;o)
O_Bind(P,b)(e,C,a,J;o)   <-> O_P(eP,C,BindFrame_b(eb,a),J;o)

I_Ref(t,theta)(e,C,k,a,J;o) <-> I_t(theta(e),C,k,a,J;o)
O_Ref(t,theta)(e,C,a,J;o)   <-> O_t(theta(e),C,a,J;o)

I_(P union Q) <-> I_P union I_Q
O_(P union Q) <-> O_P union O_Q

I_(exists x:T.P) <-> exists x:T(original dependencies). I_P
O_(exists x:T.P) <-> exists x:T(original dependencies). O_P
```

The shorthand retains every original non-child operand on both sides.
Ref uses one coherent capture-avoiding substitution on the whole incident tuple.
It does not unfold a recursive graph or move any original binder.

### Request and raw resume

For a structurally declared Request with original Delta_q and continuation t:

```text
I_Request(q,t)(e,C,k,a,J;o)
  <-> Select_0-H(eH,q(e,C),Raw(t,et,k,Delta_q),C,a,J;o)
O_Request(q,t)(e,C,a,J;o)
  <-> o=Request(q(e,C),C,Raw(t,et,a,Delta_q))

Append(End,a,a)
Append(Frame_f(ef,k),a,Frame_f(ef,b)) <-> Append(k,a,b)

Resume(Raw(t,et,k,Delta_q),r,Cnow,eta,a,J;o)
  <-> Append(k,a,b)
      and O_t(et extended by THAT (r,Cnow,eta),Cnow,b,J;o).
```

Append emits one clause per existing frame tag, preserving its order and
dependent environment. Resume uses the SAME joint admitted `(r,Cnow,eta)`;
it calls O, never I, and reinstalls neither H nor a saved C. A callable response
retains its actual Future(r); no future behavior executes from its type alone.

Select_0-H must be compiled from the finite ORIGINAL matching/guard graph.
It is a TARGET LABEL, not an independent permission or image primitive. Where
that actual graph is supplied, execute its code in O. Its actual returning
selector frames have these finite local cases at the unchanged original tuple:

```text
original NoMatch_i / GuardFalse_i outcome -> Select_(i+1)-H
original Selected_j + its visibility/match/OpCompat witness -> O_arm-j
```

The first branch keeps the same q/raw and actual current C; the second extends
the original arm environment with that SAME packet/raw/witness. Effectful
selectors/guards retain their pending selector frame and use O's Request or
Pending clauses. They are outside H. A false outcome is its original rule,
not negation of an unknown generated predicate. Exhaustion uses the original
forward/re-entry wrapper's ACTUAL supplied code/transition. No identity-forward
rule is invented. If a selector/forward frame lacks that body, Select_0-H is
not complete: this is the missing OriginalFrame action of §7, not a solved case.

### Explicit Pending prefixes

```text
I_Prefix(p)(e,C,k,a,J;o)
  <-> original Prefix_p premises and
      o=Pending(original p fields; suspended I/e/k/a/H references)
O_Prefix(p)(e,C,a,J;o)
  <-> original Prefix_p premises and
      o=Pending(original p fields; suspended O/e/a references).
```

These are r2's existing Pending fields, with finite generated phase labels as
suspended roots; not new observation types or permission. The old prefix clause,
license, G and future references remain. No blanket prefix introduction for l
is added. Bind/Ref transport a successor's prefix through their actual pending
suffix by the equations above. Neither Return nor Request follows from Pending.
L=Ref L with no terminal/prefix base has no finite derivation; the intended
prefix-bearing L=Prefix(p) union Ref L retains p without inventing a terminal.
Existing foreign prefix clauses are reused exactly, not manufactured.

## 4. Explicit image relation on an original member; common-preimage Join

The preimage must be a member BEFORE either the pending suffix or H acts.
A common tuple observed only after running the suffix is insufficient: a
suffix can itself collapse distinct original results. Define B_H and B_O as
new finite relation LABELS on the existing observation/continuation operands,
with the following ACTUAL positive bodies (not image primitives):

```text
B_H(Return(z),k,a,J;o,d) <-> RI(z,k,a,J;o,d)
B_O(Return(z),a,J;o,d)   <-> RO(z,a,J;o,d)

B_H(Request(q,C,Raw(t,et,ks,Delta_q)),k,a,J;o,d)
  <-> Append(ks,k,kt)
      and Select_0-H(eH,q,Raw(t,et,kt,Delta_q),C,a,J;o,d)

B_O(Request(q,C,Raw(t,et,ks,Delta_q)),a,J;o,d)
  <-> Append(ks,a,kt)
      and o=Request(q,C,Raw(t,et,kt,Delta_q)).
```

RI/RO/Select/Append/Resume have the §3 bodies, now retaining their actual
finite derivation d. B merely exposes those bodies at the existing observation
constructors. For each genuinely licensed Pending p, B_H/B_O have §3's
Pending body:
retain its entire original prefix proof/fields and reference the suspended
B_H(p,k,a,H) or B_O(p,a) phase with the original suffix/future references.
These are finite generated phase labels in r2's existing Pending root/reference
fields, not arbitrary relation-valued application. This constructs the pending
observation without executing its future. No terminal, receipt or H-value-arm
event is added, even when a future action remains opaque. Its later development
still needs the original action at its actual owner. No rule handles an unknown
raw continuation by pretending it matches Raw(t,et,ks).

Let M_l(e,C,J;y,w) be the ORIGINAL node's finite positive membership relation,
without the external pending suffix. These are the finite input graph's
existing member roots and clauses; copying/referencing them does not decide
arbitrary membership. They retain exactly the original Return/Request/Bind/
Ref/prefix rules and complete future fields. A completed image presentation
would emit the following relational composition, with B's bodies above:

```text
PI_l(e,C,k,a,J;y,w,o,d)
  <-> M_l(e,C,J;y,w) and B_H(y,k,a,J;o,d)
I_l(e,C,k,a,J;o) <-> exists y,w,d. PI_l(e,C,k,a,J;y,w,o,d)

O_l(e,C,a,J;o) <-> exists y,w,d.
                    M_l(e,C,J;y,w) and B_O(y,a,J;o,d).
```

Unlike the withdrawn signature, B has concrete Return/Request/Pending bodies
and recursive suffix/resume targets. For the constructor-covered part these
composition clauses and §3's direct equations agree: the original Member
Bind law appends the inside suffix exactly once, Request exposes its original
Raw, and registered Ref/union/binders keep their actual source relation.
This gives actual finite relation syntax beyond Run interpreter code. It
remains INCOMPLETE when B/RI/RO/Select reach the undefined frame/opaque rule;
no completed all-input image is claimed on the strength of these labels.

For conjunction, use the locally closed M2 rule at the ORIGINAL common y:

```text
Join_P,Q(e,C,J;y,wP,wQ)
  <-> M_P(eP,C,J;y,wP) and M_Q(eQ,C,J;y,wQ)

I_(P and Q)(e,C,k,a,J;o)
  <-> exists y,wP,wQ,d.
      Join_P,Q(e,C,J;y,wP,wQ) and B_H(y,k,a,J;o,d)

O_(P and Q)(e,C,a,J;o)
  <-> exists y,wP,wQ,d.
      Join_P,Q(e,C,J;y,wP,wQ) and B_O(y,a,J;o,d).
```

One B applies the suffix and H ONCE after conjunction membership. Both member
proofs keep their own dynamic evaluator continuations; no equality of private
proof stacks is asserted. The whole y retains the SAME actual raw/provider/
future and original J. A resumed extension must retain both member obligations
at that SAME original dependent response/history extension; agreement of erased
initial Request heads alone is insufficient. Unknown original future clauses
remain active, not inferred true from the output or a copied witness handle.

Local interpretation: every generated Join witness contains that one y and
both original member proofs; B's actual constructor derivation supplies the
single same-y suffix/handler action. Conversely every such original common
member and supported original action yield those same premises. This is the
existential common-preimage image law, not distributivity over intersection.
B's two-way constructor interpretation is proved only for its actual declared
rules; §7's missing cases cannot be assumed by this argument. M2's local
correlation result remains intact; full image representability is still blocked.

Two symbolic falsifiers check the placement of the common witness:

- Disjoint y0/y1 can both be aborted by H to integer 0. Their independent
  image intersection contains 0; Join has no y and therefore no output.
- P=Return(0), Q=Return(1), with an outside or inside suffix returning 2
  irrespective of input, have disjoint original preimages. Checking a common
  result only AFTER that suffix would falsely admit Return(2), even without H.

These are algebraic checks of invalid shortcuts, not actual-source compiler
counterexamples. No successful marginal witnesses are substituted for Join.

## 5. Typing, positivity, finite generation and local interpretation

Under the original telescope, Return carries its actual whole packet; Bind
substitutes one z at its actual binder; Request scopes Delta_q once; Resume
substitutes the same admitted joint response/live Cnow/evidence. Appended frames
retain their free dependencies and original typed maps. Source existential
binders are not hoisted; source rigid/universal binders remain pointwise. The
actual Return/arm supplies output-provider futures. Witness annotations do not
reclassify installed/private evidence or generalize an event field.

Recursive occurrences of I/O/PI/Append are positive under finite union,
conjunction, existing constructor relations and original existential binding.
Join has positive original Member_P/Member_Q and ONE B_H/B_O on their
original pre-suffix tuple. It introduces no infinite universal over a recursive unknown. Fixed original guards keep their
original semantics at unchanged operands; they are parameters, not negated
uses of Image. These facts establish monotonic defining operators for the
specified clauses and their finite-derivation least interpretation.

Traverse finite labels without unfolding Ref. Preallocate phase/paired/return
labels, then fill bodies. Bind adds one frame tag and bounded clauses; Ref a
registered reference; union/existential/Join bounded clauses. Source environments,
y,Cnow and stack CONTENTS never enter a label identity. With S the finite encoded
input size INCLUDING all actually supplied handler/frame bodies and shared typed
map references, these core equations add O(S) labels/clauses/encoded references.
Dynamic stack depth and relation solving can be unbounded. No completed all-input
presentation bound follows while a permitted action's body is absent.

Local interpretation, conditional on the traversed local bodies being supplied:
induct simultaneously on finite original and generated derivations. Bind/Ref
insert/erase exactly the original administrative step; Return discharges the top
suffix before H; Request retains whole Raw; Resume appends in order and calls O;
Prefix carries the original suspended proof. Invert those same constructors for
the reverse direction. For B, invert its existing observation constructors
and the suffix rules;
for Join use the same original pre-suffix y,wP,wQ and ONE d.
This proves local interpretation of the specified constructor equations, not
that every permitted frame/foreign leaf meets the missing hypothesis.

## 6. Manual abort/resume/recursive-prefix checks

These are symbolic reductions, not tests or executable probes:

- Bind(Request(q,t),b) reaches Request with BindFrame_b in its saved Raw.
  An aborting selected arm Return(a) runs O_arm/RO and never Resume: neither
  t nor b executes. The arm's actual output provider/future determines o.
- A real resume appends saved b and the current arm suffix, then runs t,b,arm
  suffix in that order in O at supplied Cnow. A request in b is outside H.
- A store change in the arm before resumption supplies the later Cnow. No
  snapshot or selected activation is stored in Raw for restoration.
- L=Return(v) union Bind(Ref L,b), after n recursive choices, has n dynamic
  frames but ONE I_L/ONE O_L label. A Request encountered in a running b saves
  that b's actual remaining
  continuation and all STILL-pending outer frames; abort/resume preserve
  that exact suffix. It does not remint a frame whose body has begun.
  Full-stack-specialized predicate labels would fail here.
- L=Bind(Ref L,b) without a terminal/prefix base introduces no finite terminal
  or Pending from its cycle. An independently specified prefix clause must be
  retained explicitly; it is not replaced by a fabricated Return.
- Pending inside Bind retains unexecuted b/H/suffix. It cannot run the value
  arm. Request can yield an aborting arm's Return, derived from that actual arm.

## 7. First missing equation and the unchanged opaque case

The return dispatcher must cover r2's declared case

```text
RI(z,OriginalFrame_f(ef,k),a,J;o).
```

r2 names original consumer/owner/phase frames but provides no complete inventory
and no finite typed Return transition/body, Request/prefix transport or dependent
configuration/evidence map for an arbitrary f. After End/BindFrame cases, this
is the FIRST missing defining rule in the displayed constructor order.
**Full candidate finite-image feasibility is BLOCKED.** Identity-pop is not
justified: an owner-return frame may change activity; a designated consumer may
execute its input and request before Return. Keeping ef or appending its tag
specifies neither action. No ImageFrame_f placeholder is emitted as a solution.
An absent defining clause is NOT interpreted as an empty relation, and the
open clauses in this note are not installed as a completed program for that
input. Preserve the original frame/foreign reference and report BLOCKED.

Needed from that ORIGINAL frame owner: finite positive typed Return/Request/
Pending clauses at the same packet/scope, actual consumer/phase/code and current
configuration/evidence maps. If a frame already has such a finite graph body,
cloning it with the appropriate I/O references is legitimate. The declaration
of a tag alone does not prove its body. A selector/guard/forward frame with no
such action blocks §3's Request case at the same seam.

FixedForeign remains its EXACT original predicate f(original operands;y,w),
full prefix relation, actual provider and future interfaces. If its declaration
exposes structural Return/Request/prefix transitions AND its original legally
applicable continuation relation, those same fixed predicates can participate
in positive composition, without a foreign-image oracle. But r2 also permits
an opaque leaf with no such transition/application rule; none is supplied
universally by retaining the complete relation reference.

Minimal failed subgoal: Bind(FixedForeign(f,e),b), with an original Request
(q,C,k_f), whose selected arm resumes k_f while b is pending. The construction
needs to apply THAT k_f at the joint (r,Cnow,eta), obtain its actual continuation
outcome/world/future, and run the SAME b then arm suffix outside H. No body or
legal application rule ForeignNext_f at those dependent operands is supplied.

`exists y. f(e,y) and Splice(y,b,H,o)` only renames this missing application
unless Splice's opaque-k_f clause is independently derived. Source-contract
§5.3's unchanged-predicate Eq leaf supplies no new arbitrary relation-application
sort. Do not encode k_f as a fabricated Raw(code,env,k), assume a source body,
select another provider, choose marginal response/world witnesses or assert
membership at U. The original foreign leaf stays unchanged/unresolved. No
foreign-image primitive or omitted alternative is counted as finite output.

The concrete [operation source](2026-10-16-operation-primitive-image-contract-construction.md)
§§3–5 supplies k0(r,Cnow)=Return(r,Cnow) and its original ordered S. Its own proof
stops at an opaque input suffix. The two scoped source-owner audits preserve
that boundary; they do not supply all original Z/W or opaque actions.

No actual source/foreign counterexample or impossibility is proved: the missing
rule may be supplied by a concrete owner. No original relation, provider/future,
H/U or admitted source domain is changed. M2/M3 remain locally closed within
their stated grammar; neither rule supplies these missing operational bodies.

## 8. Result, economy audit, checks and handoff

Claim class: conditional core construction with finite positive clauses, and
minimized full-grammar missing-rule result. This is distinct from Run-only
finiteness; it still does not establish full finite-image feasibility.

A2-R1/A2-R2 left the Image-body premise open. This method writes relational
clauses and stops at an unspecified constructor. Economy audit: a frame's actual
action belongs at its original consumer/phase owner. Retaining its stack addresses
D only where the action is already known; its semantic body cannot be recovered
from a tag. Original image/discharge A/B gates retain their status. Do not launch
another equivalent full-closure attempt without that missing local body.

One proposed next action: Luna/dispatcher obtain ONE actual original frame's
finite typed Return/Request/Pending transition presentation, including its
configuration/evidence action. Inbox P2-FRAME-ACTION-003 records that exact
dependency; no successor, code lease, new semantics or implementation is selected.
Independent review remains Luna's responsibility.

Static checks: scoped rule/source line reads, rg, direct SHA-256 comparison and
Markdown/link/fence/whitespace integrity. No compiler edits, builds/tests/probes,
network, delegation, measurements, board/shared/question writes or Git mutations.
Two read-only Git commands (git rev-parse HEAD, git status --short) were mistakenly
included at startup despite this packet's no-Git instruction; this was reported
to Luna and no further Git was used. One prewrite check detected changed live
board bytes and wrote NEITHER output. No scratch paths were created.

Requested gpt-6.1-sol/high; observed runtime model/effort UNKNOWN. Same resident
worker; no hot reload/override inferred. <=2 lightweight read calls per batch;
25-minute allocation; CPU/RAM uninstrumented. First recorded clock after initial
reads 04:10:08 UTC; freeze check approximately 04:24 UTC (about 14 minutes
recorded interval; startup read interval not instrumented).
Luna owns verification/integration and independent review. Zero executable checks.

## 9. Immutable input manifest and commit packet

All eight mathematical/context pins below matched before writing and are
rechecked at freeze. Scoped reads: source contracts §§2.1–2.2,3.7,5.3; operation
construction §§3–7; original target §§1,3 as scope guard; source-owner audit
owner table/conclusion; source-definition audit constructor tables/first missing
field. No unrelated historical search or compiler-source investigation was needed.
The original target was initially read beyond its required sections; no later
argument relies on those additional sections. Governing policy/role reads used
the current resident contract and do not imply runtime setting changes.

| Dependency | SHA-256 |
| --- | --- |
| `notes/theory/2026-10-16-primitive-interaction-graph-a2-r2-withdrawal.md` | `f963405835082252abbbc54381bf08fdb6a760cf508ae34416d7960fe0a2e729` |
| `notes/design/2026-10-16-primitive-interaction-graph-proposal.md` | `d7485706cc998aa4bf4bcdaaa925cef2e2348c92984a77bb99e4a5922b6c68af` |
| `notes/design/2026-10-16-primitive-interaction-graph-proposal-r2.md` | `a1929f54e77335c413cc20230100bc9cad4d98bec4b51f6464db39417a07d63e` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/theory/2026-10-16-operation-primitive-image-contract-construction.md` | `4fe70b18cad9ded249869b21b84bbf26e2a5f95320f79632a29a5071ddb1c4e9` |
| `notes/theory/2026-10-16-image-demand-original-alternative-discharge.md` | `17fda1a477d451652fb9e8088cd7fb92ff763195cbdcc8ce7467763c0aaaa24f` |
| `notes/progress/2026-10-16-operation-primitive-source-owner-audit.md` | `356071a582f7ff4db3df57e5ecdccd5435da3a6f718f831b41d0934e3666fc15` |
| `notes/progress/2026-10-16-primitive-contract-source-definition-audit.md` | `f06a92a5f20b00a8e1e0a87cc231f5d60675d529e439e28e8c50941b55b0e884` |

Supplied frozen board snapshot `642a90cb2851fc0d9a77b17ab2cdc140ce565207712fc9847878f37bfd85148a`
was verified at initial intake; it is the immutable P2 packet locator, not a
mathematical premise. Its later live scheduling revision at prewrite check was
`10043d11043e36f2f7bc3a7fac17f37cb60697e042d976661aa323a0159d5d45`. This scheduling-only change was reported to Luna; no scope/baseline/
lease change was inferred and no new board content was consumed as authority.

Commit packet:

- Exact outputs: `notes/theory/2026-10-16-parameterized-shallow-image-finite-presentation.md`
  and `tasks/agent-loop/inbox/20261016-loop-a-proof-finite-image-003.md`.
- Baseline: `0814021eb287edbd65ca6c1b25096ff91691f901`; changed mathematical
  dependency hashes: none. Board scheduling delta recorded above. This leaf
  edits no dependency, previous note, shared record or other worker output.
- Review: unreviewed conditional core derivation; full finite-image feasibility
  BLOCKED. No original parent, source adequacy, admission, exact-U/A-B,
  implementation/adoption/production or impossibility claim promoted.
- Checks: exact hashes, rule/typing/positivity/finite-label audit, symbolic
  abort/resume/recursive/prefix/common-witness checks and note/inbox integrity.
  Zero executable verification and zero independent review.
- Proposed checkpoint: `research: derive parameterized image core and frame-action stop`.
- Shared deltas left to Luna/curator: retain conditional core equations; record
  exact OriginalFrame/foreign application gaps; preserve local M2/M3 and every
  original T_alpha/admission/exact-U/source/native/production parent OPEN.
- Inbox P2-FRAME-ACTION-003 revision 1, frozen before notification; dispatcher
  intake pending. No successor selected by this submission.

Writing stops for both exact leased outputs at the immutable handoff.
